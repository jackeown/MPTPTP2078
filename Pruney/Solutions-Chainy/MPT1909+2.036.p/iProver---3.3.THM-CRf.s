%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:01 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  189 (1336 expanded)
%              Number of clauses        :   98 ( 226 expanded)
%              Number of leaves         :   28 ( 550 expanded)
%              Depth                    :   30
%              Number of atoms          :  824 (14809 expanded)
%              Number of equality atoms :  267 (2810 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_borsuk_1(X2,X0,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( X3 = X4
                           => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6))
        & sK6 = X3
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
            & sK5 = X4
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X1)) )
          & v3_borsuk_1(X2,X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & v3_borsuk_1(sK4,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK4,X0,X1)
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK3)) )
            & v3_borsuk_1(X2,X0,sK3)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v5_pre_topc(X2,X0,sK3)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK3,X0)
        & v4_tex_2(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                        & X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & v3_borsuk_1(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK2,X1)
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK2)
          & v4_tex_2(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v3_borsuk_1(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v5_pre_topc(sK4,sK2,sK3)
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK2)
    & v4_tex_2(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f46,f45,f44,f43,f42])).

fof(f84,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f82,f84])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ! [X5] :
                      ( m1_subset_1(X5,X0)
                     => ! [X6] :
                          ( m1_subset_1(X6,X0)
                         => ! [X7] :
                              ( m1_subset_1(X7,X0)
                             => ! [X8] :
                                  ( m1_subset_1(X8,X0)
                                 => ( k1_xboole_0 != X0
                                   => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( ! [X7] :
                              ( ! [X8] :
                                  ( m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  | k1_xboole_0 = X0
                                  | ~ m1_subset_1(X8,X0) )
                              | ~ m1_subset_1(X7,X0) )
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ! [X6] :
                          ( ! [X7] :
                              ( ! [X8] :
                                  ( m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
                                  | k1_xboole_0 = X0
                                  | ~ m1_subset_1(X8,X0) )
                              | ~ m1_subset_1(X7,X0) )
                          | ~ m1_subset_1(X6,X0) )
                      | ~ m1_subset_1(X5,X0) )
                  | ~ m1_subset_1(X4,X0) )
              | ~ m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X8,X0)
      | ~ m1_subset_1(X7,X0)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f81,plain,(
    v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK1(X0,X1),X0)
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f86])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f87])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f88])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f89])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f90])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f91])).

fof(f85,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(definition_unfolding,[],[f85,f84])).

fof(f83,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_794,plain,
    ( X0 != X1
    | X2 != X3
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
    theory(equality)).

cnf(c_1245,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,X1)
    | k6_domain_1(u1_struct_0(sK2),sK6) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1450,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,k6_domain_1(X1,X2))
    | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(X1,X2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1245])).

cnf(c_3225,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X1),sK6))
    | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(u1_struct_0(X1),sK6)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_12853,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6))
    | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(u1_struct_0(sK3),sK6)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_3225])).

cnf(c_12854,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(u1_struct_0(sK3),sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_12853])).

cnf(c_786,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1923,plain,
    ( X0 != X1
    | X0 = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != X1 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_3819,plain,
    ( X0 != k2_pre_topc(X1,k6_domain_1(u1_struct_0(X2),sK6))
    | X0 = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(X1,k6_domain_1(u1_struct_0(X2),sK6)) ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_10160,plain,
    ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(X1,k6_domain_1(u1_struct_0(sK3),sK6))
    | k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(X1,k6_domain_1(u1_struct_0(sK3),sK6)) ),
    inference(instantiation,[status(thm)],[c_3819])).

cnf(c_10162,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
    | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) ),
    inference(instantiation,[status(thm)],[c_10160])).

cnf(c_4645,plain,
    ( X0 != X1
    | X2 != k6_domain_1(u1_struct_0(X3),sK6)
    | k2_pre_topc(X0,X2) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X3),sK6)) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_7486,plain,
    ( X0 != X1
    | k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(sK3),sK6))
    | k6_domain_1(u1_struct_0(sK3),sK6) != k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(instantiation,[status(thm)],[c_4645])).

cnf(c_7487,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
    | k6_domain_1(u1_struct_0(sK3),sK6) != k6_domain_1(u1_struct_0(sK3),sK6)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7486])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1010,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X6,X1)
    | ~ m1_subset_1(X7,X1)
    | ~ m1_subset_1(X8,X1)
    | m1_subset_1(k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X0),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1013,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X4,X0) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X6,X0) != iProver_top
    | m1_subset_1(X7,X0) != iProver_top
    | m1_subset_1(X8,X0) != iProver_top
    | m1_subset_1(k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK3 != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_567,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_26])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_567])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_borsuk_1(X0,X1,X2)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_18,negated_conjecture,
    ( v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_357,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_358,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v4_tex_2(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v3_tdlat_3(sK2)
    | ~ v1_funct_1(sK4)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_568,c_363])).

cnf(c_1005,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_1495,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_pre_topc(sK2,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
    | u1_struct_0(sK3) = k1_xboole_0
    | m1_subset_1(X7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_1005])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_13,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_382,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_383,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_387,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_29,c_26])).

cnf(c_12,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_158,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_8])).

cnf(c_159,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_158])).

cnf(c_536,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_159,c_23])).

cnf(c_537,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_539,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_29,c_26,c_24])).

cnf(c_593,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_387,c_539])).

cnf(c_594,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_551,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_552,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_596,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_26,c_552])).

cnf(c_631,plain,
    ( u1_struct_0(sK3) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_596])).

cnf(c_2529,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_pre_topc(sK2,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
    | m1_subset_1(X7,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1495,c_631])).

cnf(c_2530,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_pre_topc(sK2,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X7,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2529])).

cnf(c_2544,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,X0,X1,X2,X3,X4,X5,X6)) = k2_pre_topc(sK2,k6_enumset1(sK6,X0,X1,X2,X3,X4,X5,X6))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_2530])).

cnf(c_2669,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,X0,X1,X2,X3,X4,X5)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,X0,X1,X2,X3,X4,X5))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_2544])).

cnf(c_2681,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,X0,X1,X2,X3,X4)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,X0,X1,X2,X3,X4))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_2669])).

cnf(c_2836,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,X0,X1,X2,X3)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,X0,X1,X2,X3))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_2681])).

cnf(c_2846,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,X0,X1,X2)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,X0,X1,X2))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_2836])).

cnf(c_2964,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0,X1)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0,X1))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_2846])).

cnf(c_2972,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_2964])).

cnf(c_3052,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_1010,c_2972])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1012,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1388,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1010,c_1012])).

cnf(c_1169,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1782,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1388,c_26,c_17,c_552,c_594,c_1169])).

cnf(c_3053,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) ),
    inference(light_normalisation,[status(thm)],[c_3052,c_1782])).

cnf(c_15,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_7076,plain,
    ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(demodulation,[status(thm)],[c_3053,c_15])).

cnf(c_1995,plain,
    ( X0 != X1
    | u1_struct_0(sK3) != X1
    | u1_struct_0(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_3006,plain,
    ( X0 != u1_struct_0(sK3)
    | u1_struct_0(sK3) = X0
    | u1_struct_0(sK3) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_3550,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_785,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3153,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1011,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1387,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK2),sK6)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1011,c_1012])).

cnf(c_1785,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK6) = k6_domain_1(u1_struct_0(sK3),sK6)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1782,c_1387])).

cnf(c_1786,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1785])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | X2 != X0
    | sK0(X2) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_554,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_26])).

cnf(c_1677,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK3) ),
    inference(resolution,[status(thm)],[c_335,c_554])).

cnf(c_1360,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_806,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12854,c_10162,c_7487,c_7076,c_3550,c_3153,c_1786,c_1677,c_1360,c_806,c_631])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.34/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.01  
% 3.34/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.01  
% 3.34/1.01  ------  iProver source info
% 3.34/1.01  
% 3.34/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.01  git: non_committed_changes: false
% 3.34/1.01  git: last_make_outside_of_git: false
% 3.34/1.01  
% 3.34/1.01  ------ 
% 3.34/1.01  ------ Parsing...
% 3.34/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.01  
% 3.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 13 0s  sf_e  pe_s  pe_e 
% 3.34/1.01  
% 3.34/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.01  
% 3.34/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.01  ------ Proving...
% 3.34/1.01  ------ Problem Properties 
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  clauses                                 14
% 3.34/1.01  conjectures                             4
% 3.34/1.01  EPR                                     1
% 3.34/1.01  Horn                                    12
% 3.34/1.01  unary                                   7
% 3.34/1.01  binary                                  4
% 3.34/1.01  lits                                    31
% 3.34/1.01  lits eq                                 9
% 3.34/1.01  fd_pure                                 0
% 3.34/1.01  fd_pseudo                               0
% 3.34/1.01  fd_cond                                 4
% 3.34/1.01  fd_pseudo_cond                          0
% 3.34/1.01  AC symbols                              0
% 3.34/1.01  
% 3.34/1.01  ------ Input Options Time Limit: Unbounded
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  ------ 
% 3.34/1.01  Current options:
% 3.34/1.01  ------ 
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  ------ Proving...
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  % SZS status Theorem for theBenchmark.p
% 3.34/1.01  
% 3.34/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.01  
% 3.34/1.01  fof(f82,plain,(
% 3.34/1.01    m1_subset_1(sK5,u1_struct_0(sK3))),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f18,conjecture,(
% 3.34/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f19,negated_conjecture,(
% 3.34/1.01    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 3.34/1.01    inference(negated_conjecture,[],[f18])).
% 3.34/1.01  
% 3.34/1.01  fof(f34,plain,(
% 3.34/1.01    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.34/1.01    inference(ennf_transformation,[],[f19])).
% 3.34/1.01  
% 3.34/1.01  fof(f35,plain,(
% 3.34/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.34/1.01    inference(flattening,[],[f34])).
% 3.34/1.01  
% 3.34/1.01  fof(f46,plain,(
% 3.34/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) & sK6 = X3 & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f45,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f44,plain,(
% 3.34/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK4,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f43,plain,(
% 3.34/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(X2,X0,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(sK3,X0) & v4_tex_2(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f42,plain,(
% 3.34/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & v4_tex_2(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f47,plain,(
% 3.34/1.01    ((((k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & v3_borsuk_1(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & v4_tex_2(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f46,f45,f44,f43,f42])).
% 3.34/1.01  
% 3.34/1.01  fof(f84,plain,(
% 3.34/1.01    sK5 = sK6),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f94,plain,(
% 3.34/1.01    m1_subset_1(sK6,u1_struct_0(sK3))),
% 3.34/1.01    inference(definition_unfolding,[],[f82,f84])).
% 3.34/1.01  
% 3.34/1.01  fof(f9,axiom,(
% 3.34/1.01    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => ! [X8] : (m1_subset_1(X8,X0) => (k1_xboole_0 != X0 => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)))))))))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f20,plain,(
% 3.34/1.01    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (! [X8] : ((m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X8,X0)) | ~m1_subset_1(X7,X0)) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 3.34/1.01    inference(ennf_transformation,[],[f9])).
% 3.34/1.01  
% 3.34/1.01  fof(f21,plain,(
% 3.34/1.01    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (! [X8] : (m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X8,X0)) | ~m1_subset_1(X7,X0)) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 3.34/1.01    inference(flattening,[],[f20])).
% 3.34/1.01  
% 3.34/1.01  fof(f56,plain,(
% 3.34/1.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X8,X0) | ~m1_subset_1(X7,X0) | ~m1_subset_1(X6,X0) | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f21])).
% 3.34/1.01  
% 3.34/1.01  fof(f12,axiom,(
% 3.34/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f24,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.34/1.01    inference(ennf_transformation,[],[f12])).
% 3.34/1.01  
% 3.34/1.01  fof(f61,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f24])).
% 3.34/1.01  
% 3.34/1.01  fof(f76,plain,(
% 3.34/1.01    m1_pre_topc(sK3,sK2)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f73,plain,(
% 3.34/1.01    l1_pre_topc(sK2)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f17,axiom,(
% 3.34/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f32,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.34/1.01    inference(ennf_transformation,[],[f17])).
% 3.34/1.01  
% 3.34/1.01  fof(f33,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/1.01    inference(flattening,[],[f32])).
% 3.34/1.01  
% 3.34/1.01  fof(f69,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f33])).
% 3.34/1.01  
% 3.34/1.01  fof(f96,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/1.01    inference(equality_resolution,[],[f69])).
% 3.34/1.01  
% 3.34/1.01  fof(f81,plain,(
% 3.34/1.01    v3_borsuk_1(sK4,sK2,sK3)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f70,plain,(
% 3.34/1.01    ~v2_struct_0(sK2)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f71,plain,(
% 3.34/1.01    v2_pre_topc(sK2)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f72,plain,(
% 3.34/1.01    v3_tdlat_3(sK2)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f74,plain,(
% 3.34/1.01    ~v2_struct_0(sK3)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f75,plain,(
% 3.34/1.01    v4_tex_2(sK3,sK2)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f77,plain,(
% 3.34/1.01    v1_funct_1(sK4)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f78,plain,(
% 3.34/1.01    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f79,plain,(
% 3.34/1.01    v5_pre_topc(sK4,sK2,sK3)),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f80,plain,(
% 3.34/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f1,axiom,(
% 3.34/1.01    v1_xboole_0(k1_xboole_0)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f48,plain,(
% 3.34/1.01    v1_xboole_0(k1_xboole_0)),
% 3.34/1.01    inference(cnf_transformation,[],[f1])).
% 3.34/1.01  
% 3.34/1.01  fof(f16,axiom,(
% 3.34/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f30,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.34/1.01    inference(ennf_transformation,[],[f16])).
% 3.34/1.01  
% 3.34/1.01  fof(f31,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/1.01    inference(flattening,[],[f30])).
% 3.34/1.01  
% 3.34/1.01  fof(f68,plain,(
% 3.34/1.01    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f31])).
% 3.34/1.01  
% 3.34/1.01  fof(f15,axiom,(
% 3.34/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f28,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.34/1.01    inference(ennf_transformation,[],[f15])).
% 3.34/1.01  
% 3.34/1.01  fof(f29,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/1.01    inference(flattening,[],[f28])).
% 3.34/1.01  
% 3.34/1.01  fof(f38,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/1.01    inference(nnf_transformation,[],[f29])).
% 3.34/1.01  
% 3.34/1.01  fof(f39,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/1.01    inference(rectify,[],[f38])).
% 3.34/1.01  
% 3.34/1.01  fof(f40,plain,(
% 3.34/1.01    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f41,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.34/1.01  
% 3.34/1.01  fof(f64,plain,(
% 3.34/1.01    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f41])).
% 3.34/1.01  
% 3.34/1.01  fof(f95,plain,(
% 3.34/1.01    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.34/1.01    inference(equality_resolution,[],[f64])).
% 3.34/1.01  
% 3.34/1.01  fof(f14,axiom,(
% 3.34/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f27,plain,(
% 3.34/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.34/1.01    inference(ennf_transformation,[],[f14])).
% 3.34/1.01  
% 3.34/1.01  fof(f63,plain,(
% 3.34/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f27])).
% 3.34/1.01  
% 3.34/1.01  fof(f13,axiom,(
% 3.34/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f25,plain,(
% 3.34/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.34/1.01    inference(ennf_transformation,[],[f13])).
% 3.34/1.01  
% 3.34/1.01  fof(f26,plain,(
% 3.34/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.34/1.01    inference(flattening,[],[f25])).
% 3.34/1.01  
% 3.34/1.01  fof(f62,plain,(
% 3.34/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f26])).
% 3.34/1.01  
% 3.34/1.01  fof(f2,axiom,(
% 3.34/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f49,plain,(
% 3.34/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f2])).
% 3.34/1.01  
% 3.34/1.01  fof(f3,axiom,(
% 3.34/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f50,plain,(
% 3.34/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f3])).
% 3.34/1.01  
% 3.34/1.01  fof(f4,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f51,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f4])).
% 3.34/1.01  
% 3.34/1.01  fof(f5,axiom,(
% 3.34/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f52,plain,(
% 3.34/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f5])).
% 3.34/1.01  
% 3.34/1.01  fof(f6,axiom,(
% 3.34/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f53,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f6])).
% 3.34/1.01  
% 3.34/1.01  fof(f7,axiom,(
% 3.34/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f54,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f7])).
% 3.34/1.01  
% 3.34/1.01  fof(f8,axiom,(
% 3.34/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f55,plain,(
% 3.34/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f8])).
% 3.34/1.01  
% 3.34/1.01  fof(f86,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.34/1.01    inference(definition_unfolding,[],[f54,f55])).
% 3.34/1.01  
% 3.34/1.01  fof(f87,plain,(
% 3.34/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.34/1.01    inference(definition_unfolding,[],[f53,f86])).
% 3.34/1.01  
% 3.34/1.01  fof(f88,plain,(
% 3.34/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.34/1.01    inference(definition_unfolding,[],[f52,f87])).
% 3.34/1.01  
% 3.34/1.01  fof(f89,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.34/1.01    inference(definition_unfolding,[],[f51,f88])).
% 3.34/1.01  
% 3.34/1.01  fof(f90,plain,(
% 3.34/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.34/1.01    inference(definition_unfolding,[],[f50,f89])).
% 3.34/1.01  
% 3.34/1.01  fof(f91,plain,(
% 3.34/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.34/1.01    inference(definition_unfolding,[],[f49,f90])).
% 3.34/1.01  
% 3.34/1.01  fof(f92,plain,(
% 3.34/1.01    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.34/1.01    inference(definition_unfolding,[],[f62,f91])).
% 3.34/1.01  
% 3.34/1.01  fof(f85,plain,(
% 3.34/1.01    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f93,plain,(
% 3.34/1.01    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 3.34/1.01    inference(definition_unfolding,[],[f85,f84])).
% 3.34/1.01  
% 3.34/1.01  fof(f83,plain,(
% 3.34/1.01    m1_subset_1(sK6,u1_struct_0(sK2))),
% 3.34/1.01    inference(cnf_transformation,[],[f47])).
% 3.34/1.01  
% 3.34/1.01  fof(f10,axiom,(
% 3.34/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f22,plain,(
% 3.34/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.34/1.01    inference(ennf_transformation,[],[f10])).
% 3.34/1.01  
% 3.34/1.01  fof(f57,plain,(
% 3.34/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.34/1.01    inference(cnf_transformation,[],[f22])).
% 3.34/1.01  
% 3.34/1.01  fof(f11,axiom,(
% 3.34/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.34/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.01  
% 3.34/1.01  fof(f23,plain,(
% 3.34/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.34/1.01    inference(ennf_transformation,[],[f11])).
% 3.34/1.01  
% 3.34/1.01  fof(f36,plain,(
% 3.34/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 3.34/1.01    introduced(choice_axiom,[])).
% 3.34/1.01  
% 3.34/1.01  fof(f37,plain,(
% 3.34/1.01    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 3.34/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).
% 3.34/1.01  
% 3.34/1.01  fof(f58,plain,(
% 3.34/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.34/1.01    inference(cnf_transformation,[],[f37])).
% 3.34/1.01  
% 3.34/1.01  cnf(c_794,plain,
% 3.34/1.01      ( X0 != X1 | X2 != X3 | k2_pre_topc(X0,X2) = k2_pre_topc(X1,X3) ),
% 3.34/1.01      theory(equality) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1245,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,X1)
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK2),sK6) != X1
% 3.34/1.01      | sK2 != X0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_794]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1450,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,k6_domain_1(X1,X2))
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(X1,X2)
% 3.34/1.01      | sK2 != X0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_1245]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3225,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X1),sK6))
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(u1_struct_0(X1),sK6)
% 3.34/1.01      | sK2 != X0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_1450]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_12853,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6))
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(u1_struct_0(sK3),sK6)
% 3.34/1.01      | sK2 != X0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_3225]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_12854,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK2),sK6) != k6_domain_1(u1_struct_0(sK3),sK6)
% 3.34/1.01      | sK2 != sK2 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_12853]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_786,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1923,plain,
% 3.34/1.01      ( X0 != X1
% 3.34/1.01      | X0 = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
% 3.34/1.01      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != X1 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_786]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3819,plain,
% 3.34/1.01      ( X0 != k2_pre_topc(X1,k6_domain_1(u1_struct_0(X2),sK6))
% 3.34/1.01      | X0 = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
% 3.34/1.01      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(X1,k6_domain_1(u1_struct_0(X2),sK6)) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_1923]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_10160,plain,
% 3.34/1.01      ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(X1,k6_domain_1(u1_struct_0(sK3),sK6))
% 3.34/1.01      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
% 3.34/1.01      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(X1,k6_domain_1(u1_struct_0(sK3),sK6)) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_3819]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_10162,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
% 3.34/1.01      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
% 3.34/1.01      | k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_10160]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_4645,plain,
% 3.34/1.01      ( X0 != X1
% 3.34/1.01      | X2 != k6_domain_1(u1_struct_0(X3),sK6)
% 3.34/1.01      | k2_pre_topc(X0,X2) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X3),sK6)) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_794]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_7486,plain,
% 3.34/1.01      ( X0 != X1
% 3.34/1.01      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(sK3),sK6))
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK3),sK6) != k6_domain_1(u1_struct_0(sK3),sK6) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_4645]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_7487,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6))
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK3),sK6) != k6_domain_1(u1_struct_0(sK3),sK6)
% 3.34/1.01      | sK2 != sK2 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_7486]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_17,negated_conjecture,
% 3.34/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.34/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1010,plain,
% 3.34/1.01      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(X2,X1)
% 3.34/1.01      | ~ m1_subset_1(X3,X1)
% 3.34/1.01      | ~ m1_subset_1(X4,X1)
% 3.34/1.01      | ~ m1_subset_1(X5,X1)
% 3.34/1.01      | ~ m1_subset_1(X6,X1)
% 3.34/1.01      | ~ m1_subset_1(X7,X1)
% 3.34/1.01      | ~ m1_subset_1(X8,X1)
% 3.34/1.01      | m1_subset_1(k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X0),k1_zfmisc_1(X1))
% 3.34/1.01      | k1_xboole_0 = X1 ),
% 3.34/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1013,plain,
% 3.34/1.01      ( k1_xboole_0 = X0
% 3.34/1.01      | m1_subset_1(X1,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X5,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X6,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X7,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(X8,X0) != iProver_top
% 3.34/1.01      | m1_subset_1(k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_6,plain,
% 3.34/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 3.34/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | ~ l1_pre_topc(X1) ),
% 3.34/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_23,negated_conjecture,
% 3.34/1.01      ( m1_pre_topc(sK3,sK2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_562,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.34/1.01      | ~ l1_pre_topc(X2)
% 3.34/1.01      | sK3 != X1
% 3.34/1.01      | sK2 != X2 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_563,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ l1_pre_topc(sK2) ),
% 3.34/1.01      inference(unflattening,[status(thm)],[c_562]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_26,negated_conjecture,
% 3.34/1.01      ( l1_pre_topc(sK2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_567,plain,
% 3.34/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_563,c_26]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_568,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_567]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_14,plain,
% 3.34/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.34/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 3.34/1.01      | ~ v3_borsuk_1(X0,X1,X2)
% 3.34/1.01      | ~ v4_tex_2(X2,X1)
% 3.34/1.01      | ~ m1_pre_topc(X2,X1)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.34/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 3.34/1.01      | ~ v3_tdlat_3(X1)
% 3.34/1.01      | ~ v1_funct_1(X0)
% 3.34/1.01      | ~ v2_pre_topc(X1)
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | v2_struct_0(X2)
% 3.34/1.01      | ~ l1_pre_topc(X1)
% 3.34/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 3.34/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_18,negated_conjecture,
% 3.34/1.01      ( v3_borsuk_1(sK4,sK2,sK3) ),
% 3.34/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_357,plain,
% 3.34/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.34/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 3.34/1.01      | ~ v4_tex_2(X2,X1)
% 3.34/1.01      | ~ m1_pre_topc(X2,X1)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.34/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 3.34/1.01      | ~ v3_tdlat_3(X1)
% 3.34/1.01      | ~ v1_funct_1(X0)
% 3.34/1.01      | ~ v2_pre_topc(X1)
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | v2_struct_0(X2)
% 3.34/1.01      | ~ l1_pre_topc(X1)
% 3.34/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 3.34/1.01      | sK4 != X0
% 3.34/1.01      | sK3 != X2
% 3.34/1.01      | sK2 != X1 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_358,plain,
% 3.34/1.01      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 3.34/1.01      | ~ v5_pre_topc(sK4,sK2,sK3)
% 3.34/1.01      | ~ v4_tex_2(sK3,sK2)
% 3.34/1.01      | ~ m1_pre_topc(sK3,sK2)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.34/1.01      | ~ v3_tdlat_3(sK2)
% 3.34/1.01      | ~ v1_funct_1(sK4)
% 3.34/1.01      | ~ v2_pre_topc(sK2)
% 3.34/1.01      | v2_struct_0(sK3)
% 3.34/1.01      | v2_struct_0(sK2)
% 3.34/1.01      | ~ l1_pre_topc(sK2)
% 3.34/1.01      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 3.34/1.01      inference(unflattening,[status(thm)],[c_357]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_29,negated_conjecture,
% 3.34/1.01      ( ~ v2_struct_0(sK2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_28,negated_conjecture,
% 3.34/1.01      ( v2_pre_topc(sK2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_27,negated_conjecture,
% 3.34/1.01      ( v3_tdlat_3(sK2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_25,negated_conjecture,
% 3.34/1.01      ( ~ v2_struct_0(sK3) ),
% 3.34/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_24,negated_conjecture,
% 3.34/1.01      ( v4_tex_2(sK3,sK2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_22,negated_conjecture,
% 3.34/1.01      ( v1_funct_1(sK4) ),
% 3.34/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_21,negated_conjecture,
% 3.34/1.01      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.34/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_20,negated_conjecture,
% 3.34/1.01      ( v5_pre_topc(sK4,sK2,sK3) ),
% 3.34/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_19,negated_conjecture,
% 3.34/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.34/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_362,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.34/1.01      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_358,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,
% 3.34/1.01                 c_19]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_363,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_362]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_588,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 3.34/1.01      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 3.34/1.01      inference(backward_subsumption_resolution,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_568,c_363]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1005,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0)
% 3.34/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1495,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_pre_topc(sK2,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
% 3.34/1.01      | u1_struct_0(sK3) = k1_xboole_0
% 3.34/1.01      | m1_subset_1(X7,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1013,c_1005]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_0,plain,
% 3.34/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_13,plain,
% 3.34/1.01      ( ~ v3_tex_2(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | ~ v2_pre_topc(X1)
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | ~ l1_pre_topc(X1)
% 3.34/1.01      | ~ v1_xboole_0(X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_382,plain,
% 3.34/1.01      ( ~ v3_tex_2(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | ~ l1_pre_topc(X1)
% 3.34/1.01      | ~ v1_xboole_0(X0)
% 3.34/1.01      | sK2 != X1 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_383,plain,
% 3.34/1.01      ( ~ v3_tex_2(X0,sK2)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | v2_struct_0(sK2)
% 3.34/1.01      | ~ l1_pre_topc(sK2)
% 3.34/1.01      | ~ v1_xboole_0(X0) ),
% 3.34/1.01      inference(unflattening,[status(thm)],[c_382]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_387,plain,
% 3.34/1.01      ( ~ v3_tex_2(X0,sK2)
% 3.34/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ v1_xboole_0(X0) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_383,c_29,c_26]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_12,plain,
% 3.34/1.01      ( v3_tex_2(u1_struct_0(X0),X1)
% 3.34/1.01      | ~ v4_tex_2(X0,X1)
% 3.34/1.01      | ~ m1_pre_topc(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | ~ l1_pre_topc(X1) ),
% 3.34/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_8,plain,
% 3.34/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.34/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | ~ l1_pre_topc(X1) ),
% 3.34/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_158,plain,
% 3.34/1.01      ( ~ m1_pre_topc(X0,X1)
% 3.34/1.01      | ~ v4_tex_2(X0,X1)
% 3.34/1.01      | v3_tex_2(u1_struct_0(X0),X1)
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | ~ l1_pre_topc(X1) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_12,c_8]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_159,plain,
% 3.34/1.01      ( v3_tex_2(u1_struct_0(X0),X1)
% 3.34/1.01      | ~ v4_tex_2(X0,X1)
% 3.34/1.01      | ~ m1_pre_topc(X0,X1)
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | ~ l1_pre_topc(X1) ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_158]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_536,plain,
% 3.34/1.01      ( v3_tex_2(u1_struct_0(X0),X1)
% 3.34/1.01      | ~ v4_tex_2(X0,X1)
% 3.34/1.01      | v2_struct_0(X1)
% 3.34/1.01      | ~ l1_pre_topc(X1)
% 3.34/1.01      | sK3 != X0
% 3.34/1.01      | sK2 != X1 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_159,c_23]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_537,plain,
% 3.34/1.01      ( v3_tex_2(u1_struct_0(sK3),sK2)
% 3.34/1.01      | ~ v4_tex_2(sK3,sK2)
% 3.34/1.01      | v2_struct_0(sK2)
% 3.34/1.01      | ~ l1_pre_topc(sK2) ),
% 3.34/1.01      inference(unflattening,[status(thm)],[c_536]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_539,plain,
% 3.34/1.01      ( v3_tex_2(u1_struct_0(sK3),sK2) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_537,c_29,c_26,c_24]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_593,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ v1_xboole_0(X0)
% 3.34/1.01      | u1_struct_0(sK3) != X0
% 3.34/1.01      | sK2 != sK2 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_387,c_539]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_594,plain,
% 3.34/1.01      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.34/1.01      inference(unflattening,[status(thm)],[c_593]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_551,plain,
% 3.34/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.34/1.01      | ~ l1_pre_topc(X1)
% 3.34/1.01      | sK3 != X0
% 3.34/1.01      | sK2 != X1 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_552,plain,
% 3.34/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.34/1.01      | ~ l1_pre_topc(sK2) ),
% 3.34/1.01      inference(unflattening,[status(thm)],[c_551]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_596,plain,
% 3.34/1.01      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_594,c_26,c_552]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_631,plain,
% 3.34/1.01      ( u1_struct_0(sK3) != k1_xboole_0 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_596]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2529,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_pre_topc(sK2,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
% 3.34/1.01      | m1_subset_1(X7,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_1495,c_631]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2530,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = k2_pre_topc(sK2,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X7,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(renaming,[status(thm)],[c_2529]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2544,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,X0,X1,X2,X3,X4,X5,X6)) = k2_pre_topc(sK2,k6_enumset1(sK6,X0,X1,X2,X3,X4,X5,X6))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X6,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2530]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2669,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,X0,X1,X2,X3,X4,X5)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,X0,X1,X2,X3,X4,X5))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X5,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2544]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2681,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,X0,X1,X2,X3,X4)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,X0,X1,X2,X3,X4))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X4,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2669]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2836,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,X0,X1,X2,X3)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,X0,X1,X2,X3))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2681]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2846,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,X0,X1,X2)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,X0,X1,X2))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2836]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2964,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0,X1)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,X0,X1))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.34/1.01      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2846]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2972,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,X0))
% 3.34/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2964]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3052,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = k2_pre_topc(sK2,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_2972]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_7,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,X1)
% 3.34/1.01      | v1_xboole_0(X1)
% 3.34/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 3.34/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1012,plain,
% 3.34/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 3.34/1.01      | m1_subset_1(X0,X1) != iProver_top
% 3.34/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1388,plain,
% 3.34/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6)
% 3.34/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1010,c_1012]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1169,plain,
% 3.34/1.01      ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 3.34/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 3.34/1.01      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1782,plain,
% 3.34/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_1388,c_26,c_17,c_552,c_594,c_1169]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3053,plain,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) ),
% 3.34/1.01      inference(light_normalisation,[status(thm)],[c_3052,c_1782]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_15,negated_conjecture,
% 3.34/1.01      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
% 3.34/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_7076,plain,
% 3.34/1.01      ( k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
% 3.34/1.01      inference(demodulation,[status(thm)],[c_3053,c_15]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1995,plain,
% 3.34/1.01      ( X0 != X1 | u1_struct_0(sK3) != X1 | u1_struct_0(sK3) = X0 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_786]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3006,plain,
% 3.34/1.01      ( X0 != u1_struct_0(sK3)
% 3.34/1.01      | u1_struct_0(sK3) = X0
% 3.34/1.01      | u1_struct_0(sK3) != u1_struct_0(sK3) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_1995]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3550,plain,
% 3.34/1.01      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 3.34/1.01      | u1_struct_0(sK3) = k1_xboole_0
% 3.34/1.01      | k1_xboole_0 != u1_struct_0(sK3) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_3006]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_785,plain,( X0 = X0 ),theory(equality) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_3153,plain,
% 3.34/1.01      ( k6_domain_1(u1_struct_0(sK3),sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_785]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_16,negated_conjecture,
% 3.34/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 3.34/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1011,plain,
% 3.34/1.01      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 3.34/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1387,plain,
% 3.34/1.01      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK2),sK6)
% 3.34/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.34/1.01      inference(superposition,[status(thm)],[c_1011,c_1012]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1785,plain,
% 3.34/1.01      ( k6_domain_1(u1_struct_0(sK2),sK6) = k6_domain_1(u1_struct_0(sK3),sK6)
% 3.34/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 3.34/1.01      inference(demodulation,[status(thm)],[c_1782,c_1387]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1786,plain,
% 3.34/1.01      ( v1_xboole_0(u1_struct_0(sK2))
% 3.34/1.01      | k6_domain_1(u1_struct_0(sK2),sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
% 3.34/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1785]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_2,plain,
% 3.34/1.01      ( ~ r2_hidden(X0,X1)
% 3.34/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.34/1.01      | ~ v1_xboole_0(X2) ),
% 3.34/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_5,plain,
% 3.34/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.34/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_334,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.01      | ~ v1_xboole_0(X1)
% 3.34/1.01      | X2 != X0
% 3.34/1.01      | sK0(X2) != X3
% 3.34/1.01      | k1_xboole_0 = X2 ),
% 3.34/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_335,plain,
% 3.34/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/1.01      | ~ v1_xboole_0(X1)
% 3.34/1.01      | k1_xboole_0 = X0 ),
% 3.34/1.01      inference(unflattening,[status(thm)],[c_334]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_554,plain,
% 3.34/1.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.34/1.01      inference(global_propositional_subsumption,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_552,c_26]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1677,plain,
% 3.34/1.01      ( ~ v1_xboole_0(u1_struct_0(sK2))
% 3.34/1.01      | k1_xboole_0 = u1_struct_0(sK3) ),
% 3.34/1.01      inference(resolution,[status(thm)],[c_335,c_554]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_1360,plain,
% 3.34/1.01      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_785]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(c_806,plain,
% 3.34/1.01      ( sK2 = sK2 ),
% 3.34/1.01      inference(instantiation,[status(thm)],[c_785]) ).
% 3.34/1.01  
% 3.34/1.01  cnf(contradiction,plain,
% 3.34/1.01      ( $false ),
% 3.34/1.01      inference(minisat,
% 3.34/1.01                [status(thm)],
% 3.34/1.01                [c_12854,c_10162,c_7487,c_7076,c_3550,c_3153,c_1786,
% 3.34/1.01                 c_1677,c_1360,c_806,c_631]) ).
% 3.34/1.01  
% 3.34/1.01  
% 3.34/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.01  
% 3.34/1.01  ------                               Statistics
% 3.34/1.01  
% 3.34/1.01  ------ Selected
% 3.34/1.01  
% 3.34/1.01  total_time:                             0.461
% 3.34/1.01  
%------------------------------------------------------------------------------
