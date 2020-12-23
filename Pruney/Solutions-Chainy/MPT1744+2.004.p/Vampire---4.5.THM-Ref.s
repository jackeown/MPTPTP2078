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
% DateTime   : Thu Dec  3 13:18:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 742 expanded)
%              Number of leaves         :   23 ( 394 expanded)
%              Depth                    :   34
%              Number of atoms          : 1113 (13766 expanded)
%              Number of equality atoms :   58 (  58 expanded)
%              Maximal formula depth    :   29 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(subsumption_resolution,[],[f357,f345])).

fof(f345,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f344,f61])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f41,f40,f39,f38,f37,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f344,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f343,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f343,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f340,f60])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f340,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f251,f71])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f126,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_connsp_2(X1,X0))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f92,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
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
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f357,plain,(
    v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f348,f263])).

fof(f263,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f262,f74])).

fof(f74,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f42])).

fof(f262,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(resolution,[],[f256,f185])).

fof(f185,plain,(
    ! [X0] :
      ( r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f184,f59])).

fof(f184,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f183,f60])).

fof(f183,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f182,f61])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f181,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f180,f63])).

fof(f63,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f180,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f179,f64])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f178,f65])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f178,plain,(
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
    inference(subsumption_resolution,[],[f177,f66])).

fof(f66,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f177,plain,(
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
    inference(subsumption_resolution,[],[f175,f72])).

fof(f72,plain,(
    v5_pre_topc(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f175,plain,(
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
    inference(resolution,[],[f81,f67])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f256,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f255,f71])).

fof(f255,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f253,f73])).

fof(f73,plain,(
    r1_tmap_1(sK1,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f253,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,sK5)
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(superposition,[],[f231,f146])).

fof(f146,plain,
    ( sK5 = k1_funct_1(sK3,sK6)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f145,f110])).

fof(f110,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f108,f90])).

fof(f90,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f108,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    inference(resolution,[],[f78,f67])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f145,plain,
    ( ~ v1_relat_1(sK3)
    | sK5 = k1_funct_1(sK3,sK6)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f142,f65])).

fof(f142,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK5 = k1_funct_1(sK3,sK6)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f120,f125])).

fof(f125,plain,
    ( r2_hidden(sK6,k10_relat_1(sK3,k1_tarski(sK5)))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f123,f67])).

fof(f123,plain,
    ( r2_hidden(sK6,k10_relat_1(sK3,k1_tarski(sK5)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f115,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f115,plain,
    ( r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k1_tarski(sK5)))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f114,f71])).

fof(f114,plain,
    ( r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k1_tarski(sK5)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(superposition,[],[f75,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f75,plain,(
    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) ),
    inference(cnf_transformation,[],[f42])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X1,k1_tarski(X2)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(X1,X0) = X2 ) ),
    inference(resolution,[],[f102,f106])).

fof(f106,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
                | ~ r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK8(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
                  & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

% (23430)Termination reason: Refutation not found, incomplete strategy
fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f231,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f230,f65])).

fof(f230,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f229,f66])).

fof(f229,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f228,f67])).

fof(f228,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f226,f74])).

fof(f226,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(superposition,[],[f213,f99])).

% (23430)Memory used [KB]: 6652
fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f213,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f212,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f212,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f211,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f210,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f209,f62])).

fof(f209,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f208,f63])).

fof(f208,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f207,f64])).

fof(f207,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f59])).

fof(f206,plain,
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
    inference(subsumption_resolution,[],[f205,f60])).

fof(f205,plain,
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
    inference(subsumption_resolution,[],[f204,f61])).

fof(f204,plain,
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
    inference(subsumption_resolution,[],[f203,f65])).

fof(f203,plain,
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
    inference(subsumption_resolution,[],[f202,f66])).

fof(f202,plain,
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
    inference(subsumption_resolution,[],[f201,f67])).

fof(f201,plain,
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
    inference(subsumption_resolution,[],[f200,f68])).

% (23430)Time elapsed: 0.119 s
fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f200,plain,
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
    inference(subsumption_resolution,[],[f199,f69])).

fof(f69,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f199,plain,
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
    inference(subsumption_resolution,[],[f198,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f198,plain,
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
    inference(subsumption_resolution,[],[f195,f74])).

% (23430)------------------------------
% (23430)------------------------------
fof(f195,plain,
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
    inference(resolution,[],[f100,f76])).

fof(f76,plain,(
    ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f22])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f348,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f347,f64])).

fof(f347,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f346,f62])).

fof(f346,plain,
    ( v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f341,f63])).

fof(f341,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f251,f74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:10:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (23403)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (23411)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (23408)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (23419)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (23405)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (23430)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (23419)Refutation not found, incomplete strategy% (23419)------------------------------
% 0.22/0.53  % (23419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23416)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (23406)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (23412)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (23419)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23419)Memory used [KB]: 10746
% 0.22/0.53  % (23419)Time elapsed: 0.111 s
% 0.22/0.53  % (23419)------------------------------
% 0.22/0.53  % (23419)------------------------------
% 0.22/0.54  % (23422)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (23414)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (23417)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (23404)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (23415)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (23404)Refutation not found, incomplete strategy% (23404)------------------------------
% 0.22/0.54  % (23404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23404)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23404)Memory used [KB]: 1918
% 0.22/0.54  % (23404)Time elapsed: 0.127 s
% 0.22/0.54  % (23404)------------------------------
% 0.22/0.54  % (23404)------------------------------
% 0.22/0.54  % (23407)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (23409)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (23425)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (23426)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (23430)Refutation not found, incomplete strategy% (23430)------------------------------
% 0.22/0.55  % (23430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23432)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (23423)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (23428)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (23407)Refutation not found, incomplete strategy% (23407)------------------------------
% 0.22/0.55  % (23407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23407)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23407)Memory used [KB]: 1918
% 0.22/0.55  % (23407)Time elapsed: 0.132 s
% 0.22/0.55  % (23407)------------------------------
% 0.22/0.55  % (23407)------------------------------
% 0.22/0.55  % (23432)Refutation not found, incomplete strategy% (23432)------------------------------
% 0.22/0.55  % (23432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23432)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23432)Memory used [KB]: 1791
% 0.22/0.55  % (23432)Time elapsed: 0.139 s
% 0.22/0.55  % (23432)------------------------------
% 0.22/0.55  % (23432)------------------------------
% 0.22/0.55  % (23418)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (23421)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (23429)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (23424)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (23412)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f358,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f357,f345])).
% 0.22/0.56  fof(f345,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f344,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    l1_pre_topc(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ((((((~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) & r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(sK6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,sK5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f41,f40,f39,f38,f37,f36,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,sK0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,sK0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,X2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,X2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) => (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,sK5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(sK5,u1_struct_0(sK1)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) & r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : ((~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))) & m1_subset_1(X6,u1_struct_0(X2))) & (r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1))) & m1_subset_1(X5,u1_struct_0(X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 0.22/0.56    inference(negated_conjecture,[],[f14])).
% 0.22/0.56  fof(f14,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tmap_1)).
% 0.22/0.56  fof(f344,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f343,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ~v2_struct_0(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f343,plain,(
% 0.22/0.56    v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f340,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    v2_pre_topc(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f340,plain,(
% 0.22/0.56    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.56    inference(resolution,[],[f251,f71])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f251,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f247])).
% 0.22/0.56  fof(f247,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(resolution,[],[f126,f79])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_connsp_2(X1,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.56    inference(resolution,[],[f92,f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.22/0.56  fof(f357,plain,(
% 0.22/0.56    v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(resolution,[],[f348,f263])).
% 0.22/0.56  fof(f263,plain,(
% 0.22/0.56    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f262,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f262,plain,(
% 0.22/0.56    v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.56    inference(resolution,[],[f256,f185])).
% 0.22/0.56  fof(f185,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tmap_1(sK2,sK1,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f184,f59])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f183,f60])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f182,f61])).
% 0.22/0.56  fof(f182,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f181,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ~v2_struct_0(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f181,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f180,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    v2_pre_topc(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f180,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f179,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    l1_pre_topc(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f178,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f177,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f175,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    v5_pre_topc(sK3,sK2,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v5_pre_topc(sK3,sK2,sK1) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.22/0.56    inference(resolution,[],[f81,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | r1_tmap_1(X1,X0,X2,X4) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(rectify,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.22/0.56  fof(f256,plain,(
% 0.22/0.56    ~r1_tmap_1(sK2,sK1,sK3,sK6) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f255,f71])).
% 0.22/0.56  fof(f255,plain,(
% 0.22/0.56    ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f253,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    r1_tmap_1(sK1,sK0,sK4,sK5)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f253,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,sK5) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(superposition,[],[f231,f146])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    sK5 = k1_funct_1(sK3,sK6) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f145,f110])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    v1_relat_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f108,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))),
% 0.22/0.56    inference(resolution,[],[f78,f67])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ~v1_relat_1(sK3) | sK5 = k1_funct_1(sK3,sK6) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f142,f65])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK5 = k1_funct_1(sK3,sK6) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(resolution,[],[f120,f125])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    r2_hidden(sK6,k10_relat_1(sK3,k1_tarski(sK5))) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f123,f67])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    r2_hidden(sK6,k10_relat_1(sK3,k1_tarski(sK5))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.22/0.56    inference(superposition,[],[f115,f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k1_tarski(sK5))) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f114,f71])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k1_tarski(sK5))) | ~m1_subset_1(sK5,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.56    inference(superposition,[],[f75,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5)))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X1,k1_tarski(X2))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_funct_1(X1,X0) = X2) )),
% 0.22/0.56    inference(resolution,[],[f102,f106])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.56    inference(equality_resolution,[],[f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f53,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(rectify,[],[f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1) | ~r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1) | ~r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(rectify,[],[f48])).
% 0.22/0.56  % (23430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f47])).
% 0.22/0.56  
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f230,f65])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f229,f66])).
% 0.22/0.56  fof(f229,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f228,f67])).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f226,f74])).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k1_funct_1(sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k1_funct_1(sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.56    inference(superposition,[],[f213,f99])).
% 0.22/0.56  % (23430)Memory used [KB]: 6652
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.56  fof(f213,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))),
% 0.22/0.56    inference(subsumption_resolution,[],[f212,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ~v2_struct_0(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f211,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    v2_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f211,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f210,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f209,f62])).
% 0.22/0.56  fof(f209,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f208,f63])).
% 0.22/0.56  fof(f208,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f207,f64])).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f206,f59])).
% 0.22/0.56  fof(f206,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f205,f60])).
% 0.22/0.56  fof(f205,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f204,f61])).
% 0.22/0.56  fof(f204,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f203,f65])).
% 0.22/0.56  fof(f203,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f202,f66])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f201,f67])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f200,f68])).
% 0.22/0.56  % (23430)Time elapsed: 0.119 s
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    v1_funct_1(sK4)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f200,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f199,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f199,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f198,f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f195,f74])).
% 0.22/0.56  % (23430)------------------------------
% 0.22/0.56  % (23430)------------------------------
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f100,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f80])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).
% 0.22/0.56  fof(f348,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f347,f64])).
% 0.22/0.56  fof(f347,plain,(
% 0.22/0.56    ~v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f346,f62])).
% 0.22/0.56  fof(f346,plain,(
% 0.22/0.56    v2_struct_0(sK2) | ~v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f341,f63])).
% 0.22/0.56  fof(f341,plain,(
% 0.22/0.56    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~v1_xboole_0(u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 0.22/0.56    inference(resolution,[],[f251,f74])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (23412)------------------------------
% 0.22/0.56  % (23412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23412)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (23412)Memory used [KB]: 2046
% 0.22/0.56  % (23412)Time elapsed: 0.141 s
% 0.22/0.56  % (23412)------------------------------
% 0.22/0.56  % (23412)------------------------------
% 0.22/0.56  % (23413)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (23420)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (23413)Refutation not found, incomplete strategy% (23413)------------------------------
% 0.22/0.56  % (23413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23413)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23413)Memory used [KB]: 11129
% 0.22/0.56  % (23413)Time elapsed: 0.152 s
% 0.22/0.56  % (23413)------------------------------
% 0.22/0.56  % (23413)------------------------------
% 0.22/0.57  % (23402)Success in time 0.198 s
%------------------------------------------------------------------------------
