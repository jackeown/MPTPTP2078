%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:54 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  204 (1354 expanded)
%              Number of clauses        :  114 ( 298 expanded)
%              Number of leaves         :   23 ( 505 expanded)
%              Depth                    :   21
%              Number of atoms          :  914 (14445 expanded)
%              Number of equality atoms :  138 (2321 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))
        & sK5 = X3
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
            & sK4 = X4
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & v3_borsuk_1(sK3,X0,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK3,X0,X1)
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK2)) )
            & v3_borsuk_1(X2,X0,sK2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v5_pre_topc(X2,X0,sK2)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK2,X0)
        & v4_tex_2(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
                      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK1,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK1,X1)
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK1)
          & v4_tex_2(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    & sK4 = sK5
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v3_borsuk_1(sK3,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v5_pre_topc(sK3,sK1,sK2)
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & v4_tex_2(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f49,f56,f55,f54,f53,f52])).

fof(f92,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(definition_unfolding,[],[f90,f92])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f59])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ v3_tex_2(X2,X0) )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(sK0(X0),X0)
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f50])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v4_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tdlat_3(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tdlat_3(X1)
          | ~ v1_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_tdlat_3(X1)
      | ~ v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK0(X0),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(definition_unfolding,[],[f93,f92])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f89,plain,(
    v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f86,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f59])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1123,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1125,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1668,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_1125])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1127,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(resolution,[status(thm)],[c_14,c_17])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_531,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_532,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_534,plain,
    ( v2_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_32,c_30])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_581,c_534])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_12,plain,
    ( ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v1_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X0)
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_380,plain,
    ( ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_382,plain,
    ( ~ l1_pre_topc(X1)
    | v3_tdlat_3(X0)
    | ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_380,c_12,c_11])).

cnf(c_383,plain,
    ( ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_28,negated_conjecture,
    ( v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_478,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_383,c_28])).

cnf(c_479,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_520,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_521,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_670,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_666,c_33,c_30,c_29,c_27,c_479,c_521])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_670])).

cnf(c_1114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_1888,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1114])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1126,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2704,plain,
    ( v1_xboole_0(sK0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_1126])).

cnf(c_1240,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1243,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1799,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_1800,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_15,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_16,plain,
    ( v3_tex_2(sK0(X0),X0)
    | ~ v2_tex_2(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_412,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | X1 != X3
    | sK0(X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_16])).

cnf(c_413,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(sK0(X1)) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(sK0(X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_17])).

cnf(c_418,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(sK0(X1)) ),
    inference(renaming,[status(thm)],[c_417])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X1)) ),
    inference(resolution,[status(thm)],[c_14,c_418])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X1))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_555,c_534])).

cnf(c_687,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(sK2)) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_33,c_30,c_29,c_27,c_479,c_521])).

cnf(c_1113,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_1515,plain,
    ( v1_xboole_0(sK0(sK2)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1113])).

cnf(c_1601,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1126])).

cnf(c_1962,plain,
    ( v1_xboole_0(sK0(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1515,c_1601])).

cnf(c_3170,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2704,c_1243,c_1800,c_1962])).

cnf(c_3175,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_1668,c_3170])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1124,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1667,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1124,c_1125])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_491,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_492,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_494,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_30])).

cnf(c_1119,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_1603,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1126])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(X1))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_555,c_32])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(sK1)) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_31,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_649,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_33,c_31,c_30])).

cnf(c_1115,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_1440,plain,
    ( v1_xboole_0(sK0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1115])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_581,c_32])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_628,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_33,c_31,c_30])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_628])).

cnf(c_1116,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1446,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1116])).

cnf(c_1353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1783,plain,
    ( ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(sK0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_1784,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(sK0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_1843,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1603,c_1440,c_1446,c_1784])).

cnf(c_1848,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5) ),
    inference(superposition,[status(thm)],[c_1667,c_1843])).

cnf(c_19,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1850,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_1848,c_19])).

cnf(c_3214,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_tarski(sK5,sK5)) != k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_3175,c_1850])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_507,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_30])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_507])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v3_borsuk_1(X0,X1,X2)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_22,negated_conjecture,
    ( v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_454,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_tex_2(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_24,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_508,c_459])).

cnf(c_1550,plain,
    ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_tarski(sK5,sK5)) = k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1554,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_tarski(sK5,sK5)) = k2_pre_topc(sK1,k2_tarski(sK5,sK5))
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1550])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_4,c_2])).

cnf(c_1257,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1258,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3214,c_3170,c_1554,c_1258,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.51/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.00  
% 2.51/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.51/1.00  
% 2.51/1.00  ------  iProver source info
% 2.51/1.00  
% 2.51/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.51/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.51/1.00  git: non_committed_changes: false
% 2.51/1.00  git: last_make_outside_of_git: false
% 2.51/1.00  
% 2.51/1.00  ------ 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options
% 2.51/1.00  
% 2.51/1.00  --out_options                           all
% 2.51/1.00  --tptp_safe_out                         true
% 2.51/1.00  --problem_path                          ""
% 2.51/1.00  --include_path                          ""
% 2.51/1.00  --clausifier                            res/vclausify_rel
% 2.51/1.00  --clausifier_options                    --mode clausify
% 2.51/1.00  --stdin                                 false
% 2.51/1.00  --stats_out                             all
% 2.51/1.00  
% 2.51/1.00  ------ General Options
% 2.51/1.00  
% 2.51/1.00  --fof                                   false
% 2.51/1.00  --time_out_real                         305.
% 2.51/1.00  --time_out_virtual                      -1.
% 2.51/1.00  --symbol_type_check                     false
% 2.51/1.00  --clausify_out                          false
% 2.51/1.00  --sig_cnt_out                           false
% 2.51/1.00  --trig_cnt_out                          false
% 2.51/1.00  --trig_cnt_out_tolerance                1.
% 2.51/1.00  --trig_cnt_out_sk_spl                   false
% 2.51/1.00  --abstr_cl_out                          false
% 2.51/1.00  
% 2.51/1.00  ------ Global Options
% 2.51/1.00  
% 2.51/1.00  --schedule                              default
% 2.51/1.00  --add_important_lit                     false
% 2.51/1.00  --prop_solver_per_cl                    1000
% 2.51/1.00  --min_unsat_core                        false
% 2.51/1.00  --soft_assumptions                      false
% 2.51/1.00  --soft_lemma_size                       3
% 2.51/1.00  --prop_impl_unit_size                   0
% 2.51/1.00  --prop_impl_unit                        []
% 2.51/1.00  --share_sel_clauses                     true
% 2.51/1.00  --reset_solvers                         false
% 2.51/1.00  --bc_imp_inh                            [conj_cone]
% 2.51/1.00  --conj_cone_tolerance                   3.
% 2.51/1.00  --extra_neg_conj                        none
% 2.51/1.00  --large_theory_mode                     true
% 2.51/1.00  --prolific_symb_bound                   200
% 2.51/1.00  --lt_threshold                          2000
% 2.51/1.00  --clause_weak_htbl                      true
% 2.51/1.00  --gc_record_bc_elim                     false
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing Options
% 2.51/1.00  
% 2.51/1.00  --preprocessing_flag                    true
% 2.51/1.00  --time_out_prep_mult                    0.1
% 2.51/1.00  --splitting_mode                        input
% 2.51/1.00  --splitting_grd                         true
% 2.51/1.00  --splitting_cvd                         false
% 2.51/1.00  --splitting_cvd_svl                     false
% 2.51/1.00  --splitting_nvd                         32
% 2.51/1.00  --sub_typing                            true
% 2.51/1.00  --prep_gs_sim                           true
% 2.51/1.00  --prep_unflatten                        true
% 2.51/1.00  --prep_res_sim                          true
% 2.51/1.00  --prep_upred                            true
% 2.51/1.00  --prep_sem_filter                       exhaustive
% 2.51/1.00  --prep_sem_filter_out                   false
% 2.51/1.00  --pred_elim                             true
% 2.51/1.00  --res_sim_input                         true
% 2.51/1.00  --eq_ax_congr_red                       true
% 2.51/1.00  --pure_diseq_elim                       true
% 2.51/1.00  --brand_transform                       false
% 2.51/1.00  --non_eq_to_eq                          false
% 2.51/1.00  --prep_def_merge                        true
% 2.51/1.00  --prep_def_merge_prop_impl              false
% 2.51/1.00  --prep_def_merge_mbd                    true
% 2.51/1.00  --prep_def_merge_tr_red                 false
% 2.51/1.00  --prep_def_merge_tr_cl                  false
% 2.51/1.00  --smt_preprocessing                     true
% 2.51/1.00  --smt_ac_axioms                         fast
% 2.51/1.00  --preprocessed_out                      false
% 2.51/1.00  --preprocessed_stats                    false
% 2.51/1.00  
% 2.51/1.00  ------ Abstraction refinement Options
% 2.51/1.00  
% 2.51/1.00  --abstr_ref                             []
% 2.51/1.00  --abstr_ref_prep                        false
% 2.51/1.00  --abstr_ref_until_sat                   false
% 2.51/1.00  --abstr_ref_sig_restrict                funpre
% 2.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/1.00  --abstr_ref_under                       []
% 2.51/1.00  
% 2.51/1.00  ------ SAT Options
% 2.51/1.00  
% 2.51/1.00  --sat_mode                              false
% 2.51/1.00  --sat_fm_restart_options                ""
% 2.51/1.00  --sat_gr_def                            false
% 2.51/1.00  --sat_epr_types                         true
% 2.51/1.00  --sat_non_cyclic_types                  false
% 2.51/1.00  --sat_finite_models                     false
% 2.51/1.00  --sat_fm_lemmas                         false
% 2.51/1.00  --sat_fm_prep                           false
% 2.51/1.00  --sat_fm_uc_incr                        true
% 2.51/1.00  --sat_out_model                         small
% 2.51/1.00  --sat_out_clauses                       false
% 2.51/1.00  
% 2.51/1.00  ------ QBF Options
% 2.51/1.00  
% 2.51/1.00  --qbf_mode                              false
% 2.51/1.00  --qbf_elim_univ                         false
% 2.51/1.00  --qbf_dom_inst                          none
% 2.51/1.00  --qbf_dom_pre_inst                      false
% 2.51/1.00  --qbf_sk_in                             false
% 2.51/1.00  --qbf_pred_elim                         true
% 2.51/1.00  --qbf_split                             512
% 2.51/1.00  
% 2.51/1.00  ------ BMC1 Options
% 2.51/1.00  
% 2.51/1.00  --bmc1_incremental                      false
% 2.51/1.00  --bmc1_axioms                           reachable_all
% 2.51/1.00  --bmc1_min_bound                        0
% 2.51/1.00  --bmc1_max_bound                        -1
% 2.51/1.00  --bmc1_max_bound_default                -1
% 2.51/1.00  --bmc1_symbol_reachability              true
% 2.51/1.00  --bmc1_property_lemmas                  false
% 2.51/1.00  --bmc1_k_induction                      false
% 2.51/1.00  --bmc1_non_equiv_states                 false
% 2.51/1.00  --bmc1_deadlock                         false
% 2.51/1.00  --bmc1_ucm                              false
% 2.51/1.00  --bmc1_add_unsat_core                   none
% 2.51/1.00  --bmc1_unsat_core_children              false
% 2.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/1.00  --bmc1_out_stat                         full
% 2.51/1.00  --bmc1_ground_init                      false
% 2.51/1.00  --bmc1_pre_inst_next_state              false
% 2.51/1.00  --bmc1_pre_inst_state                   false
% 2.51/1.00  --bmc1_pre_inst_reach_state             false
% 2.51/1.00  --bmc1_out_unsat_core                   false
% 2.51/1.00  --bmc1_aig_witness_out                  false
% 2.51/1.00  --bmc1_verbose                          false
% 2.51/1.00  --bmc1_dump_clauses_tptp                false
% 2.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.51/1.00  --bmc1_dump_file                        -
% 2.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.51/1.00  --bmc1_ucm_extend_mode                  1
% 2.51/1.00  --bmc1_ucm_init_mode                    2
% 2.51/1.00  --bmc1_ucm_cone_mode                    none
% 2.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.51/1.00  --bmc1_ucm_relax_model                  4
% 2.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/1.00  --bmc1_ucm_layered_model                none
% 2.51/1.00  --bmc1_ucm_max_lemma_size               10
% 2.51/1.00  
% 2.51/1.00  ------ AIG Options
% 2.51/1.00  
% 2.51/1.00  --aig_mode                              false
% 2.51/1.00  
% 2.51/1.00  ------ Instantiation Options
% 2.51/1.00  
% 2.51/1.00  --instantiation_flag                    true
% 2.51/1.00  --inst_sos_flag                         false
% 2.51/1.00  --inst_sos_phase                        true
% 2.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel_side                     num_symb
% 2.51/1.00  --inst_solver_per_active                1400
% 2.51/1.00  --inst_solver_calls_frac                1.
% 2.51/1.00  --inst_passive_queue_type               priority_queues
% 2.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/1.00  --inst_passive_queues_freq              [25;2]
% 2.51/1.00  --inst_dismatching                      true
% 2.51/1.00  --inst_eager_unprocessed_to_passive     true
% 2.51/1.00  --inst_prop_sim_given                   true
% 2.51/1.00  --inst_prop_sim_new                     false
% 2.51/1.00  --inst_subs_new                         false
% 2.51/1.00  --inst_eq_res_simp                      false
% 2.51/1.00  --inst_subs_given                       false
% 2.51/1.00  --inst_orphan_elimination               true
% 2.51/1.00  --inst_learning_loop_flag               true
% 2.51/1.00  --inst_learning_start                   3000
% 2.51/1.00  --inst_learning_factor                  2
% 2.51/1.00  --inst_start_prop_sim_after_learn       3
% 2.51/1.00  --inst_sel_renew                        solver
% 2.51/1.00  --inst_lit_activity_flag                true
% 2.51/1.00  --inst_restr_to_given                   false
% 2.51/1.00  --inst_activity_threshold               500
% 2.51/1.00  --inst_out_proof                        true
% 2.51/1.00  
% 2.51/1.00  ------ Resolution Options
% 2.51/1.00  
% 2.51/1.00  --resolution_flag                       true
% 2.51/1.00  --res_lit_sel                           adaptive
% 2.51/1.00  --res_lit_sel_side                      none
% 2.51/1.00  --res_ordering                          kbo
% 2.51/1.00  --res_to_prop_solver                    active
% 2.51/1.00  --res_prop_simpl_new                    false
% 2.51/1.00  --res_prop_simpl_given                  true
% 2.51/1.00  --res_passive_queue_type                priority_queues
% 2.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/1.00  --res_passive_queues_freq               [15;5]
% 2.51/1.00  --res_forward_subs                      full
% 2.51/1.00  --res_backward_subs                     full
% 2.51/1.00  --res_forward_subs_resolution           true
% 2.51/1.00  --res_backward_subs_resolution          true
% 2.51/1.00  --res_orphan_elimination                true
% 2.51/1.00  --res_time_limit                        2.
% 2.51/1.00  --res_out_proof                         true
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Options
% 2.51/1.00  
% 2.51/1.00  --superposition_flag                    true
% 2.51/1.00  --sup_passive_queue_type                priority_queues
% 2.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.51/1.00  --demod_completeness_check              fast
% 2.51/1.00  --demod_use_ground                      true
% 2.51/1.00  --sup_to_prop_solver                    passive
% 2.51/1.00  --sup_prop_simpl_new                    true
% 2.51/1.00  --sup_prop_simpl_given                  true
% 2.51/1.00  --sup_fun_splitting                     false
% 2.51/1.00  --sup_smt_interval                      50000
% 2.51/1.00  
% 2.51/1.00  ------ Superposition Simplification Setup
% 2.51/1.00  
% 2.51/1.00  --sup_indices_passive                   []
% 2.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_full_bw                           [BwDemod]
% 2.51/1.00  --sup_immed_triv                        [TrivRules]
% 2.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_immed_bw_main                     []
% 2.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.00  
% 2.51/1.00  ------ Combination Options
% 2.51/1.00  
% 2.51/1.00  --comb_res_mult                         3
% 2.51/1.00  --comb_sup_mult                         2
% 2.51/1.00  --comb_inst_mult                        10
% 2.51/1.00  
% 2.51/1.00  ------ Debug Options
% 2.51/1.00  
% 2.51/1.00  --dbg_backtrace                         false
% 2.51/1.00  --dbg_dump_prop_clauses                 false
% 2.51/1.00  --dbg_dump_prop_clauses_file            -
% 2.51/1.00  --dbg_out_stat                          false
% 2.51/1.00  ------ Parsing...
% 2.51/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.51/1.00  ------ Proving...
% 2.51/1.00  ------ Problem Properties 
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  clauses                                 17
% 2.51/1.00  conjectures                             4
% 2.51/1.00  EPR                                     1
% 2.51/1.00  Horn                                    14
% 2.51/1.00  unary                                   6
% 2.51/1.00  binary                                  3
% 2.51/1.00  lits                                    37
% 2.51/1.00  lits eq                                 4
% 2.51/1.00  fd_pure                                 0
% 2.51/1.00  fd_pseudo                               0
% 2.51/1.00  fd_cond                                 1
% 2.51/1.00  fd_pseudo_cond                          0
% 2.51/1.00  AC symbols                              0
% 2.51/1.00  
% 2.51/1.00  ------ Schedule dynamic 5 is on 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.51/1.00  
% 2.51/1.00  
% 2.51/1.00  ------ 
% 2.51/1.00  Current options:
% 2.51/1.00  ------ 
% 2.51/1.00  
% 2.51/1.00  ------ Input Options
% 2.51/1.00  
% 2.51/1.00  --out_options                           all
% 2.51/1.00  --tptp_safe_out                         true
% 2.51/1.00  --problem_path                          ""
% 2.51/1.00  --include_path                          ""
% 2.51/1.00  --clausifier                            res/vclausify_rel
% 2.51/1.00  --clausifier_options                    --mode clausify
% 2.51/1.00  --stdin                                 false
% 2.51/1.00  --stats_out                             all
% 2.51/1.00  
% 2.51/1.00  ------ General Options
% 2.51/1.00  
% 2.51/1.00  --fof                                   false
% 2.51/1.00  --time_out_real                         305.
% 2.51/1.00  --time_out_virtual                      -1.
% 2.51/1.00  --symbol_type_check                     false
% 2.51/1.00  --clausify_out                          false
% 2.51/1.00  --sig_cnt_out                           false
% 2.51/1.00  --trig_cnt_out                          false
% 2.51/1.00  --trig_cnt_out_tolerance                1.
% 2.51/1.00  --trig_cnt_out_sk_spl                   false
% 2.51/1.00  --abstr_cl_out                          false
% 2.51/1.00  
% 2.51/1.00  ------ Global Options
% 2.51/1.00  
% 2.51/1.00  --schedule                              default
% 2.51/1.00  --add_important_lit                     false
% 2.51/1.00  --prop_solver_per_cl                    1000
% 2.51/1.00  --min_unsat_core                        false
% 2.51/1.00  --soft_assumptions                      false
% 2.51/1.00  --soft_lemma_size                       3
% 2.51/1.00  --prop_impl_unit_size                   0
% 2.51/1.00  --prop_impl_unit                        []
% 2.51/1.00  --share_sel_clauses                     true
% 2.51/1.00  --reset_solvers                         false
% 2.51/1.00  --bc_imp_inh                            [conj_cone]
% 2.51/1.00  --conj_cone_tolerance                   3.
% 2.51/1.00  --extra_neg_conj                        none
% 2.51/1.00  --large_theory_mode                     true
% 2.51/1.00  --prolific_symb_bound                   200
% 2.51/1.00  --lt_threshold                          2000
% 2.51/1.00  --clause_weak_htbl                      true
% 2.51/1.00  --gc_record_bc_elim                     false
% 2.51/1.00  
% 2.51/1.00  ------ Preprocessing Options
% 2.51/1.00  
% 2.51/1.00  --preprocessing_flag                    true
% 2.51/1.00  --time_out_prep_mult                    0.1
% 2.51/1.00  --splitting_mode                        input
% 2.51/1.00  --splitting_grd                         true
% 2.51/1.00  --splitting_cvd                         false
% 2.51/1.00  --splitting_cvd_svl                     false
% 2.51/1.00  --splitting_nvd                         32
% 2.51/1.00  --sub_typing                            true
% 2.51/1.00  --prep_gs_sim                           true
% 2.51/1.00  --prep_unflatten                        true
% 2.51/1.00  --prep_res_sim                          true
% 2.51/1.00  --prep_upred                            true
% 2.51/1.00  --prep_sem_filter                       exhaustive
% 2.51/1.00  --prep_sem_filter_out                   false
% 2.51/1.00  --pred_elim                             true
% 2.51/1.00  --res_sim_input                         true
% 2.51/1.00  --eq_ax_congr_red                       true
% 2.51/1.00  --pure_diseq_elim                       true
% 2.51/1.00  --brand_transform                       false
% 2.51/1.00  --non_eq_to_eq                          false
% 2.51/1.00  --prep_def_merge                        true
% 2.51/1.00  --prep_def_merge_prop_impl              false
% 2.51/1.00  --prep_def_merge_mbd                    true
% 2.51/1.00  --prep_def_merge_tr_red                 false
% 2.51/1.00  --prep_def_merge_tr_cl                  false
% 2.51/1.00  --smt_preprocessing                     true
% 2.51/1.00  --smt_ac_axioms                         fast
% 2.51/1.00  --preprocessed_out                      false
% 2.51/1.00  --preprocessed_stats                    false
% 2.51/1.00  
% 2.51/1.00  ------ Abstraction refinement Options
% 2.51/1.00  
% 2.51/1.00  --abstr_ref                             []
% 2.51/1.00  --abstr_ref_prep                        false
% 2.51/1.00  --abstr_ref_until_sat                   false
% 2.51/1.00  --abstr_ref_sig_restrict                funpre
% 2.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.51/1.00  --abstr_ref_under                       []
% 2.51/1.00  
% 2.51/1.00  ------ SAT Options
% 2.51/1.00  
% 2.51/1.00  --sat_mode                              false
% 2.51/1.00  --sat_fm_restart_options                ""
% 2.51/1.00  --sat_gr_def                            false
% 2.51/1.00  --sat_epr_types                         true
% 2.51/1.00  --sat_non_cyclic_types                  false
% 2.51/1.00  --sat_finite_models                     false
% 2.51/1.00  --sat_fm_lemmas                         false
% 2.51/1.00  --sat_fm_prep                           false
% 2.51/1.00  --sat_fm_uc_incr                        true
% 2.51/1.00  --sat_out_model                         small
% 2.51/1.00  --sat_out_clauses                       false
% 2.51/1.00  
% 2.51/1.00  ------ QBF Options
% 2.51/1.00  
% 2.51/1.00  --qbf_mode                              false
% 2.51/1.00  --qbf_elim_univ                         false
% 2.51/1.00  --qbf_dom_inst                          none
% 2.51/1.00  --qbf_dom_pre_inst                      false
% 2.51/1.00  --qbf_sk_in                             false
% 2.51/1.00  --qbf_pred_elim                         true
% 2.51/1.00  --qbf_split                             512
% 2.51/1.00  
% 2.51/1.00  ------ BMC1 Options
% 2.51/1.00  
% 2.51/1.00  --bmc1_incremental                      false
% 2.51/1.00  --bmc1_axioms                           reachable_all
% 2.51/1.00  --bmc1_min_bound                        0
% 2.51/1.00  --bmc1_max_bound                        -1
% 2.51/1.00  --bmc1_max_bound_default                -1
% 2.51/1.00  --bmc1_symbol_reachability              true
% 2.51/1.00  --bmc1_property_lemmas                  false
% 2.51/1.00  --bmc1_k_induction                      false
% 2.51/1.00  --bmc1_non_equiv_states                 false
% 2.51/1.00  --bmc1_deadlock                         false
% 2.51/1.00  --bmc1_ucm                              false
% 2.51/1.00  --bmc1_add_unsat_core                   none
% 2.51/1.00  --bmc1_unsat_core_children              false
% 2.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.51/1.00  --bmc1_out_stat                         full
% 2.51/1.00  --bmc1_ground_init                      false
% 2.51/1.00  --bmc1_pre_inst_next_state              false
% 2.51/1.00  --bmc1_pre_inst_state                   false
% 2.51/1.00  --bmc1_pre_inst_reach_state             false
% 2.51/1.00  --bmc1_out_unsat_core                   false
% 2.51/1.00  --bmc1_aig_witness_out                  false
% 2.51/1.00  --bmc1_verbose                          false
% 2.51/1.00  --bmc1_dump_clauses_tptp                false
% 2.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.51/1.00  --bmc1_dump_file                        -
% 2.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.51/1.00  --bmc1_ucm_extend_mode                  1
% 2.51/1.00  --bmc1_ucm_init_mode                    2
% 2.51/1.00  --bmc1_ucm_cone_mode                    none
% 2.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.51/1.00  --bmc1_ucm_relax_model                  4
% 2.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.51/1.00  --bmc1_ucm_layered_model                none
% 2.51/1.00  --bmc1_ucm_max_lemma_size               10
% 2.51/1.00  
% 2.51/1.00  ------ AIG Options
% 2.51/1.00  
% 2.51/1.00  --aig_mode                              false
% 2.51/1.00  
% 2.51/1.00  ------ Instantiation Options
% 2.51/1.00  
% 2.51/1.00  --instantiation_flag                    true
% 2.51/1.00  --inst_sos_flag                         false
% 2.51/1.00  --inst_sos_phase                        true
% 2.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.51/1.00  --inst_lit_sel_side                     none
% 2.51/1.00  --inst_solver_per_active                1400
% 2.51/1.00  --inst_solver_calls_frac                1.
% 2.51/1.00  --inst_passive_queue_type               priority_queues
% 2.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.51/1.01  --inst_passive_queues_freq              [25;2]
% 2.51/1.01  --inst_dismatching                      true
% 2.51/1.01  --inst_eager_unprocessed_to_passive     true
% 2.51/1.01  --inst_prop_sim_given                   true
% 2.51/1.01  --inst_prop_sim_new                     false
% 2.51/1.01  --inst_subs_new                         false
% 2.51/1.01  --inst_eq_res_simp                      false
% 2.51/1.01  --inst_subs_given                       false
% 2.51/1.01  --inst_orphan_elimination               true
% 2.51/1.01  --inst_learning_loop_flag               true
% 2.51/1.01  --inst_learning_start                   3000
% 2.51/1.01  --inst_learning_factor                  2
% 2.51/1.01  --inst_start_prop_sim_after_learn       3
% 2.51/1.01  --inst_sel_renew                        solver
% 2.51/1.01  --inst_lit_activity_flag                true
% 2.51/1.01  --inst_restr_to_given                   false
% 2.51/1.01  --inst_activity_threshold               500
% 2.51/1.01  --inst_out_proof                        true
% 2.51/1.01  
% 2.51/1.01  ------ Resolution Options
% 2.51/1.01  
% 2.51/1.01  --resolution_flag                       false
% 2.51/1.01  --res_lit_sel                           adaptive
% 2.51/1.01  --res_lit_sel_side                      none
% 2.51/1.01  --res_ordering                          kbo
% 2.51/1.01  --res_to_prop_solver                    active
% 2.51/1.01  --res_prop_simpl_new                    false
% 2.51/1.01  --res_prop_simpl_given                  true
% 2.51/1.01  --res_passive_queue_type                priority_queues
% 2.51/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.51/1.01  --res_passive_queues_freq               [15;5]
% 2.51/1.01  --res_forward_subs                      full
% 2.51/1.01  --res_backward_subs                     full
% 2.51/1.01  --res_forward_subs_resolution           true
% 2.51/1.01  --res_backward_subs_resolution          true
% 2.51/1.01  --res_orphan_elimination                true
% 2.51/1.01  --res_time_limit                        2.
% 2.51/1.01  --res_out_proof                         true
% 2.51/1.01  
% 2.51/1.01  ------ Superposition Options
% 2.51/1.01  
% 2.51/1.01  --superposition_flag                    true
% 2.51/1.01  --sup_passive_queue_type                priority_queues
% 2.51/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.51/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.51/1.01  --demod_completeness_check              fast
% 2.51/1.01  --demod_use_ground                      true
% 2.51/1.01  --sup_to_prop_solver                    passive
% 2.51/1.01  --sup_prop_simpl_new                    true
% 2.51/1.01  --sup_prop_simpl_given                  true
% 2.51/1.01  --sup_fun_splitting                     false
% 2.51/1.01  --sup_smt_interval                      50000
% 2.51/1.01  
% 2.51/1.01  ------ Superposition Simplification Setup
% 2.51/1.01  
% 2.51/1.01  --sup_indices_passive                   []
% 2.51/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.51/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.51/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.01  --sup_full_bw                           [BwDemod]
% 2.51/1.01  --sup_immed_triv                        [TrivRules]
% 2.51/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.51/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.01  --sup_immed_bw_main                     []
% 2.51/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.51/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.51/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.51/1.01  
% 2.51/1.01  ------ Combination Options
% 2.51/1.01  
% 2.51/1.01  --comb_res_mult                         3
% 2.51/1.01  --comb_sup_mult                         2
% 2.51/1.01  --comb_inst_mult                        10
% 2.51/1.01  
% 2.51/1.01  ------ Debug Options
% 2.51/1.01  
% 2.51/1.01  --dbg_backtrace                         false
% 2.51/1.01  --dbg_dump_prop_clauses                 false
% 2.51/1.01  --dbg_dump_prop_clauses_file            -
% 2.51/1.01  --dbg_out_stat                          false
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  ------ Proving...
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  % SZS status Theorem for theBenchmark.p
% 2.51/1.01  
% 2.51/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.51/1.01  
% 2.51/1.01  fof(f90,plain,(
% 2.51/1.01    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f19,conjecture,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f20,negated_conjecture,(
% 2.51/1.01    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.51/1.01    inference(negated_conjecture,[],[f19])).
% 2.51/1.01  
% 2.51/1.01  fof(f48,plain,(
% 2.51/1.01    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f20])).
% 2.51/1.01  
% 2.51/1.01  fof(f49,plain,(
% 2.51/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.51/1.01    inference(flattening,[],[f48])).
% 2.51/1.01  
% 2.51/1.01  fof(f56,plain,(
% 2.51/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) & sK5 = X3 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.51/1.01    introduced(choice_axiom,[])).
% 2.51/1.01  
% 2.51/1.01  fof(f55,plain,(
% 2.51/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK4 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 2.51/1.01    introduced(choice_axiom,[])).
% 2.51/1.01  
% 2.51/1.01  fof(f54,plain,(
% 2.51/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK3,X0,X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK3,X0,X1) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.51/1.01    introduced(choice_axiom,[])).
% 2.51/1.01  
% 2.51/1.01  fof(f53,plain,(
% 2.51/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(X2,X0,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v5_pre_topc(X2,X0,sK2) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & v4_tex_2(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.51/1.01    introduced(choice_axiom,[])).
% 2.51/1.01  
% 2.51/1.01  fof(f52,plain,(
% 2.51/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X2,sK1,X1) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & v4_tex_2(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.51/1.01    introduced(choice_axiom,[])).
% 2.51/1.01  
% 2.51/1.01  fof(f57,plain,(
% 2.51/1.01    ((((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2))) & v3_borsuk_1(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & v4_tex_2(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.51/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f49,f56,f55,f54,f53,f52])).
% 2.51/1.01  
% 2.51/1.01  fof(f92,plain,(
% 2.51/1.01    sK4 = sK5),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f97,plain,(
% 2.51/1.01    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.51/1.01    inference(definition_unfolding,[],[f90,f92])).
% 2.51/1.01  
% 2.51/1.01  fof(f11,axiom,(
% 2.51/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f33,plain,(
% 2.51/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f11])).
% 2.51/1.01  
% 2.51/1.01  fof(f34,plain,(
% 2.51/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.51/1.01    inference(flattening,[],[f33])).
% 2.51/1.01  
% 2.51/1.01  fof(f68,plain,(
% 2.51/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f34])).
% 2.51/1.01  
% 2.51/1.01  fof(f2,axiom,(
% 2.51/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f59,plain,(
% 2.51/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f2])).
% 2.51/1.01  
% 2.51/1.01  fof(f95,plain,(
% 2.51/1.01    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.51/1.01    inference(definition_unfolding,[],[f68,f59])).
% 2.51/1.01  
% 2.51/1.01  fof(f3,axiom,(
% 2.51/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f60,plain,(
% 2.51/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.51/1.01    inference(cnf_transformation,[],[f3])).
% 2.51/1.01  
% 2.51/1.01  fof(f15,axiom,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f40,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f15])).
% 2.51/1.01  
% 2.51/1.01  fof(f41,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.51/1.01    inference(flattening,[],[f40])).
% 2.51/1.01  
% 2.51/1.01  fof(f73,plain,(
% 2.51/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f41])).
% 2.51/1.01  
% 2.51/1.01  fof(f17,axiom,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f21,plain,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~v3_tex_2(X2,X0)) & v2_tex_2(X1,X0))))),
% 2.51/1.01    inference(pure_predicate_removal,[],[f17])).
% 2.51/1.01  
% 2.51/1.01  fof(f44,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : ((? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f21])).
% 2.51/1.01  
% 2.51/1.01  fof(f45,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.51/1.01    inference(flattening,[],[f44])).
% 2.51/1.01  
% 2.51/1.01  fof(f50,plain,(
% 2.51/1.01    ! [X0] : (? [X2] : (v3_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.51/1.01    introduced(choice_axiom,[])).
% 2.51/1.01  
% 2.51/1.01  fof(f51,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : ((v3_tex_2(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.51/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f50])).
% 2.51/1.01  
% 2.51/1.01  fof(f75,plain,(
% 2.51/1.01    ( ! [X0,X1] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f51])).
% 2.51/1.01  
% 2.51/1.01  fof(f8,axiom,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f29,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f8])).
% 2.51/1.01  
% 2.51/1.01  fof(f30,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.51/1.01    inference(flattening,[],[f29])).
% 2.51/1.01  
% 2.51/1.01  fof(f65,plain,(
% 2.51/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f30])).
% 2.51/1.01  
% 2.51/1.01  fof(f84,plain,(
% 2.51/1.01    m1_pre_topc(sK2,sK1)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f79,plain,(
% 2.51/1.01    v2_pre_topc(sK1)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f81,plain,(
% 2.51/1.01    l1_pre_topc(sK1)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f78,plain,(
% 2.51/1.01    ~v2_struct_0(sK1)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f82,plain,(
% 2.51/1.01    ~v2_struct_0(sK2)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f14,axiom,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f38,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v4_tex_2(X1,X0) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f14])).
% 2.51/1.01  
% 2.51/1.01  fof(f39,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.51/1.01    inference(flattening,[],[f38])).
% 2.51/1.01  
% 2.51/1.01  fof(f72,plain,(
% 2.51/1.01    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f39])).
% 2.51/1.01  
% 2.51/1.01  fof(f13,axiom,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) => v3_tdlat_3(X1))))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f36,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : ((v3_tdlat_3(X1) | ~v1_tdlat_3(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f13])).
% 2.51/1.01  
% 2.51/1.01  fof(f37,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (v3_tdlat_3(X1) | ~v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.51/1.01    inference(flattening,[],[f36])).
% 2.51/1.01  
% 2.51/1.01  fof(f70,plain,(
% 2.51/1.01    ( ! [X0,X1] : (v3_tdlat_3(X1) | ~v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f37])).
% 2.51/1.01  
% 2.51/1.01  fof(f83,plain,(
% 2.51/1.01    v4_tex_2(sK2,sK1)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f9,axiom,(
% 2.51/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f31,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.51/1.01    inference(ennf_transformation,[],[f9])).
% 2.51/1.01  
% 2.51/1.01  fof(f66,plain,(
% 2.51/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f31])).
% 2.51/1.01  
% 2.51/1.01  fof(f5,axiom,(
% 2.51/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f24,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.51/1.01    inference(ennf_transformation,[],[f5])).
% 2.51/1.01  
% 2.51/1.01  fof(f62,plain,(
% 2.51/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f24])).
% 2.51/1.01  
% 2.51/1.01  fof(f16,axiom,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f42,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f16])).
% 2.51/1.01  
% 2.51/1.01  fof(f43,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.51/1.01    inference(flattening,[],[f42])).
% 2.51/1.01  
% 2.51/1.01  fof(f74,plain,(
% 2.51/1.01    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f43])).
% 2.51/1.01  
% 2.51/1.01  fof(f76,plain,(
% 2.51/1.01    ( ! [X0,X1] : (v3_tex_2(sK0(X0),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f51])).
% 2.51/1.01  
% 2.51/1.01  fof(f91,plain,(
% 2.51/1.01    m1_subset_1(sK5,u1_struct_0(sK1))),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f12,axiom,(
% 2.51/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f35,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.51/1.01    inference(ennf_transformation,[],[f12])).
% 2.51/1.01  
% 2.51/1.01  fof(f69,plain,(
% 2.51/1.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f35])).
% 2.51/1.01  
% 2.51/1.01  fof(f80,plain,(
% 2.51/1.01    v3_tdlat_3(sK1)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f93,plain,(
% 2.51/1.01    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f96,plain,(
% 2.51/1.01    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 2.51/1.01    inference(definition_unfolding,[],[f93,f92])).
% 2.51/1.01  
% 2.51/1.01  fof(f10,axiom,(
% 2.51/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f32,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.51/1.01    inference(ennf_transformation,[],[f10])).
% 2.51/1.01  
% 2.51/1.01  fof(f67,plain,(
% 2.51/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f32])).
% 2.51/1.01  
% 2.51/1.01  fof(f18,axiom,(
% 2.51/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f46,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.51/1.01    inference(ennf_transformation,[],[f18])).
% 2.51/1.01  
% 2.51/1.01  fof(f47,plain,(
% 2.51/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.51/1.01    inference(flattening,[],[f46])).
% 2.51/1.01  
% 2.51/1.01  fof(f77,plain,(
% 2.51/1.01    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f47])).
% 2.51/1.01  
% 2.51/1.01  fof(f98,plain,(
% 2.51/1.01    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.51/1.01    inference(equality_resolution,[],[f77])).
% 2.51/1.01  
% 2.51/1.01  fof(f89,plain,(
% 2.51/1.01    v3_borsuk_1(sK3,sK1,sK2)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f85,plain,(
% 2.51/1.01    v1_funct_1(sK3)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f86,plain,(
% 2.51/1.01    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f87,plain,(
% 2.51/1.01    v5_pre_topc(sK3,sK1,sK2)),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f88,plain,(
% 2.51/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.51/1.01    inference(cnf_transformation,[],[f57])).
% 2.51/1.01  
% 2.51/1.01  fof(f6,axiom,(
% 2.51/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f25,plain,(
% 2.51/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.51/1.01    inference(ennf_transformation,[],[f6])).
% 2.51/1.01  
% 2.51/1.01  fof(f26,plain,(
% 2.51/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.51/1.01    inference(flattening,[],[f25])).
% 2.51/1.01  
% 2.51/1.01  fof(f63,plain,(
% 2.51/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f26])).
% 2.51/1.01  
% 2.51/1.01  fof(f4,axiom,(
% 2.51/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.51/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.51/1.01  
% 2.51/1.01  fof(f23,plain,(
% 2.51/1.01    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.51/1.01    inference(ennf_transformation,[],[f4])).
% 2.51/1.01  
% 2.51/1.01  fof(f61,plain,(
% 2.51/1.01    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.51/1.01    inference(cnf_transformation,[],[f23])).
% 2.51/1.01  
% 2.51/1.01  fof(f94,plain,(
% 2.51/1.01    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.51/1.01    inference(definition_unfolding,[],[f61,f59])).
% 2.51/1.01  
% 2.51/1.01  cnf(c_21,negated_conjecture,
% 2.51/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.51/1.01      inference(cnf_transformation,[],[f97]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1123,plain,
% 2.51/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_9,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,X1)
% 2.51/1.01      | v1_xboole_0(X1)
% 2.51/1.01      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.51/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1125,plain,
% 2.51/1.01      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 2.51/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.51/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1668,plain,
% 2.51/1.01      ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5)
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1123,c_1125]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1,plain,
% 2.51/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.51/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1127,plain,
% 2.51/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_14,plain,
% 2.51/1.01      ( v2_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_17,plain,
% 2.51/1.01      ( ~ v2_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_581,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(resolution,[status(thm)],[c_14,c_17]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_6,plain,
% 2.51/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | v2_pre_topc(X0) ),
% 2.51/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_27,negated_conjecture,
% 2.51/1.01      ( m1_pre_topc(sK2,sK1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_531,plain,
% 2.51/1.01      ( ~ l1_pre_topc(X0)
% 2.51/1.01      | ~ v2_pre_topc(X0)
% 2.51/1.01      | v2_pre_topc(X1)
% 2.51/1.01      | sK2 != X1
% 2.51/1.01      | sK1 != X0 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_27]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_532,plain,
% 2.51/1.01      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK1) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_531]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_32,negated_conjecture,
% 2.51/1.01      ( v2_pre_topc(sK1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_30,negated_conjecture,
% 2.51/1.01      ( l1_pre_topc(sK1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_534,plain,
% 2.51/1.01      ( v2_pre_topc(sK2) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_532,c_32,c_30]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_665,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | sK2 != X1 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_581,c_534]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_666,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | v2_struct_0(sK2)
% 2.51/1.01      | ~ v3_tdlat_3(sK2)
% 2.51/1.01      | ~ l1_pre_topc(sK2)
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_665]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_33,negated_conjecture,
% 2.51/1.01      ( ~ v2_struct_0(sK1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_29,negated_conjecture,
% 2.51/1.01      ( ~ v2_struct_0(sK2) ),
% 2.51/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_12,plain,
% 2.51/1.01      ( ~ v4_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | v2_struct_0(X0)
% 2.51/1.01      | v1_tdlat_3(X0)
% 2.51/1.01      | ~ l1_pre_topc(X1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_11,plain,
% 2.51/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v1_tdlat_3(X0)
% 2.51/1.01      | v3_tdlat_3(X0)
% 2.51/1.01      | ~ l1_pre_topc(X1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_380,plain,
% 2.51/1.01      ( ~ v4_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | ~ m1_pre_topc(X0,X2)
% 2.51/1.01      | v2_struct_0(X0)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | v2_struct_0(X2)
% 2.51/1.01      | v3_tdlat_3(X0)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ l1_pre_topc(X2) ),
% 2.51/1.01      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_382,plain,
% 2.51/1.01      ( ~ l1_pre_topc(X1)
% 2.51/1.01      | v3_tdlat_3(X0)
% 2.51/1.01      | ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | ~ v4_tex_2(X0,X1)
% 2.51/1.01      | v2_struct_0(X0)
% 2.51/1.01      | v2_struct_0(X1) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_380,c_12,c_11]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_383,plain,
% 2.51/1.01      ( ~ v4_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | v2_struct_0(X0)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | v3_tdlat_3(X0)
% 2.51/1.01      | ~ l1_pre_topc(X1) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_382]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_28,negated_conjecture,
% 2.51/1.01      ( v4_tex_2(sK2,sK1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_478,plain,
% 2.51/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | v2_struct_0(X0)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | v3_tdlat_3(X0)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | sK2 != X0
% 2.51/1.01      | sK1 != X1 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_383,c_28]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_479,plain,
% 2.51/1.01      ( ~ m1_pre_topc(sK2,sK1)
% 2.51/1.01      | v2_struct_0(sK2)
% 2.51/1.01      | v2_struct_0(sK1)
% 2.51/1.01      | v3_tdlat_3(sK2)
% 2.51/1.01      | ~ l1_pre_topc(sK1) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_478]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_7,plain,
% 2.51/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.51/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_520,plain,
% 2.51/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X1 | sK1 != X0 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_521,plain,
% 2.51/1.01      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_520]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_670,plain,
% 2.51/1.01      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_666,c_33,c_30,c_29,c_27,c_479,c_521]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_671,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_670]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1114,plain,
% 2.51/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.51/1.01      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.51/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1888,plain,
% 2.51/1.01      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.51/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1127,c_1114]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_3,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.51/1.01      | ~ v1_xboole_0(X1)
% 2.51/1.01      | v1_xboole_0(X0) ),
% 2.51/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1126,plain,
% 2.51/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.51/1.01      | v1_xboole_0(X1) != iProver_top
% 2.51/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2704,plain,
% 2.51/1.01      ( v1_xboole_0(sK0(sK2)) = iProver_top
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 2.51/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1888,c_1126]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1240,plain,
% 2.51/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1243,plain,
% 2.51/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1377,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1799,plain,
% 2.51/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ v1_xboole_0(u1_struct_0(sK2))
% 2.51/1.01      | v1_xboole_0(k1_xboole_0) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_1377]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1800,plain,
% 2.51/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 2.51/1.01      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_15,plain,
% 2.51/1.01      ( ~ v3_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_16,plain,
% 2.51/1.01      ( v3_tex_2(sK0(X0),X0)
% 2.51/1.01      | ~ v2_tex_2(X1,X0)
% 2.51/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.51/1.01      | v2_struct_0(X0)
% 2.51/1.01      | ~ v3_tdlat_3(X0)
% 2.51/1.01      | ~ l1_pre_topc(X0)
% 2.51/1.01      | ~ v2_pre_topc(X0) ),
% 2.51/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_412,plain,
% 2.51/1.01      ( ~ v2_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X3)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X3)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X3)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X2)
% 2.51/1.01      | X1 != X3
% 2.51/1.01      | sK0(X1) != X2 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_16]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_413,plain,
% 2.51/1.01      ( ~ v2_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | ~ m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(sK0(X1)) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_412]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_417,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | ~ v2_tex_2(X0,X1)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(sK0(X1)) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_413,c_17]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_418,plain,
% 2.51/1.01      ( ~ v2_tex_2(X0,X1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(sK0(X1)) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_417]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_555,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(sK0(X1)) ),
% 2.51/1.01      inference(resolution,[status(thm)],[c_14,c_418]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_686,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(sK0(X1))
% 2.51/1.01      | sK2 != X1 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_555,c_534]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_687,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | v2_struct_0(sK2)
% 2.51/1.01      | ~ v3_tdlat_3(sK2)
% 2.51/1.01      | ~ l1_pre_topc(sK2)
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(sK0(sK2)) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_686]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_691,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(sK0(sK2)) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_687,c_33,c_30,c_29,c_27,c_479,c_521]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1113,plain,
% 2.51/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.51/1.01      | v1_xboole_0(X0) != iProver_top
% 2.51/1.01      | v1_xboole_0(sK0(sK2)) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1515,plain,
% 2.51/1.01      ( v1_xboole_0(sK0(sK2)) != iProver_top
% 2.51/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1127,c_1113]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1601,plain,
% 2.51/1.01      ( v1_xboole_0(X0) != iProver_top
% 2.51/1.01      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1127,c_1126]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1962,plain,
% 2.51/1.01      ( v1_xboole_0(sK0(sK2)) != iProver_top ),
% 2.51/1.01      inference(forward_subsumption_resolution,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_1515,c_1601]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_3170,plain,
% 2.51/1.01      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_2704,c_1243,c_1800,c_1962]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_3175,plain,
% 2.51/1.01      ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5) ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1668,c_3170]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_20,negated_conjecture,
% 2.51/1.01      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 2.51/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1124,plain,
% 2.51/1.01      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1667,plain,
% 2.51/1.01      ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5)
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1124,c_1125]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_10,plain,
% 2.51/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | ~ l1_pre_topc(X1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_491,plain,
% 2.51/1.01      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | sK2 != X0
% 2.51/1.01      | sK1 != X1 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_492,plain,
% 2.51/1.01      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ l1_pre_topc(sK1) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_491]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_494,plain,
% 2.51/1.01      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_492,c_30]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1119,plain,
% 2.51/1.01      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1603,plain,
% 2.51/1.01      ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1119,c_1126]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_644,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(sK0(X1))
% 2.51/1.01      | sK1 != X1 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_555,c_32]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_645,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | v2_struct_0(sK1)
% 2.51/1.01      | ~ v3_tdlat_3(sK1)
% 2.51/1.01      | ~ l1_pre_topc(sK1)
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(sK0(sK1)) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_644]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_31,negated_conjecture,
% 2.51/1.01      ( v3_tdlat_3(sK1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_649,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(sK0(sK1)) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_645,c_33,c_31,c_30]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1115,plain,
% 2.51/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.51/1.01      | v1_xboole_0(X0) != iProver_top
% 2.51/1.01      | v1_xboole_0(sK0(sK1)) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1440,plain,
% 2.51/1.01      ( v1_xboole_0(sK0(sK1)) != iProver_top
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1119,c_1115]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_623,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | m1_subset_1(sK0(X1),k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v1_xboole_0(X0)
% 2.51/1.01      | sK1 != X1 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_581,c_32]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_624,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | v2_struct_0(sK1)
% 2.51/1.01      | ~ v3_tdlat_3(sK1)
% 2.51/1.01      | ~ l1_pre_topc(sK1)
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_623]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_628,plain,
% 2.51/1.01      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_624,c_33,c_31,c_30]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_629,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ v1_xboole_0(X0) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_628]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1116,plain,
% 2.51/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.51/1.01      | m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.51/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1446,plain,
% 2.51/1.01      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1119,c_1116]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1353,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | v1_xboole_0(X0)
% 2.51/1.01      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1783,plain,
% 2.51/1.01      ( ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | v1_xboole_0(sK0(sK1))
% 2.51/1.01      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_1353]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1784,plain,
% 2.51/1.01      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.51/1.01      | v1_xboole_0(sK0(sK1)) = iProver_top
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1843,plain,
% 2.51/1.01      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_1603,c_1440,c_1446,c_1784]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1848,plain,
% 2.51/1.01      ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5) ),
% 2.51/1.01      inference(superposition,[status(thm)],[c_1667,c_1843]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_19,negated_conjecture,
% 2.51/1.01      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.51/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1850,plain,
% 2.51/1.01      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
% 2.51/1.01      inference(demodulation,[status(thm)],[c_1848,c_19]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_3214,plain,
% 2.51/1.01      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_tarski(sK5,sK5)) != k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
% 2.51/1.01      inference(demodulation,[status(thm)],[c_3175,c_1850]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_8,plain,
% 2.51/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.51/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.51/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | ~ l1_pre_topc(X1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_502,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.51/1.01      | ~ l1_pre_topc(X2)
% 2.51/1.01      | sK2 != X1
% 2.51/1.01      | sK1 != X2 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_503,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ l1_pre_topc(sK1) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_502]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_507,plain,
% 2.51/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_503,c_30]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_508,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_507]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_18,plain,
% 2.51/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.51/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 2.51/1.01      | ~ v3_borsuk_1(X0,X1,X2)
% 2.51/1.01      | ~ v4_tex_2(X2,X1)
% 2.51/1.01      | ~ m1_pre_topc(X2,X1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.51/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.51/1.01      | ~ v1_funct_1(X0)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | v2_struct_0(X2)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 2.51/1.01      inference(cnf_transformation,[],[f98]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_22,negated_conjecture,
% 2.51/1.01      ( v3_borsuk_1(sK3,sK1,sK2) ),
% 2.51/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_453,plain,
% 2.51/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.51/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 2.51/1.01      | ~ v4_tex_2(X2,X1)
% 2.51/1.01      | ~ m1_pre_topc(X2,X1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.51/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.51/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.51/1.01      | ~ v1_funct_1(X0)
% 2.51/1.01      | v2_struct_0(X1)
% 2.51/1.01      | v2_struct_0(X2)
% 2.51/1.01      | ~ v3_tdlat_3(X1)
% 2.51/1.01      | ~ l1_pre_topc(X1)
% 2.51/1.01      | ~ v2_pre_topc(X1)
% 2.51/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 2.51/1.01      | sK3 != X0
% 2.51/1.01      | sK2 != X2
% 2.51/1.01      | sK1 != X1 ),
% 2.51/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_454,plain,
% 2.51/1.01      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.51/1.01      | ~ v5_pre_topc(sK3,sK1,sK2)
% 2.51/1.01      | ~ v4_tex_2(sK2,sK1)
% 2.51/1.01      | ~ m1_pre_topc(sK2,sK1)
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.51/1.01      | ~ v1_funct_1(sK3)
% 2.51/1.01      | v2_struct_0(sK2)
% 2.51/1.01      | v2_struct_0(sK1)
% 2.51/1.01      | ~ v3_tdlat_3(sK1)
% 2.51/1.01      | ~ l1_pre_topc(sK1)
% 2.51/1.01      | ~ v2_pre_topc(sK1)
% 2.51/1.01      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.51/1.01      inference(unflattening,[status(thm)],[c_453]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_26,negated_conjecture,
% 2.51/1.01      ( v1_funct_1(sK3) ),
% 2.51/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_25,negated_conjecture,
% 2.51/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.51/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_24,negated_conjecture,
% 2.51/1.01      ( v5_pre_topc(sK3,sK1,sK2) ),
% 2.51/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_23,negated_conjecture,
% 2.51/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.51/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_458,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.51/1.01      inference(global_propositional_subsumption,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_454,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24,
% 2.51/1.01                 c_23]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_459,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.51/1.01      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.51/1.01      inference(renaming,[status(thm)],[c_458]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_546,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.51/1.01      inference(backward_subsumption_resolution,
% 2.51/1.01                [status(thm)],
% 2.51/1.01                [c_508,c_459]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1550,plain,
% 2.51/1.01      ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_tarski(sK5,sK5)) = k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_546]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1554,plain,
% 2.51/1.01      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k2_tarski(sK5,sK5)) = k2_pre_topc(sK1,k2_tarski(sK5,sK5))
% 2.51/1.01      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_1550]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_4,plain,
% 2.51/1.01      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.51/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_2,plain,
% 2.51/1.01      ( ~ r2_hidden(X0,X1)
% 2.51/1.01      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ),
% 2.51/1.01      inference(cnf_transformation,[],[f94]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_357,plain,
% 2.51/1.01      ( ~ m1_subset_1(X0,X1)
% 2.51/1.01      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 2.51/1.01      | v1_xboole_0(X1) ),
% 2.51/1.01      inference(resolution,[status(thm)],[c_4,c_2]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1257,plain,
% 2.51/1.01      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.51/1.01      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.51/1.01      inference(instantiation,[status(thm)],[c_357]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_1258,plain,
% 2.51/1.01      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.51/1.01      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 2.51/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(c_46,plain,
% 2.51/1.01      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.51/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.51/1.01  
% 2.51/1.01  cnf(contradiction,plain,
% 2.51/1.01      ( $false ),
% 2.51/1.01      inference(minisat,[status(thm)],[c_3214,c_3170,c_1554,c_1258,c_46]) ).
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.51/1.01  
% 2.51/1.01  ------                               Statistics
% 2.51/1.01  
% 2.51/1.01  ------ General
% 2.51/1.01  
% 2.51/1.01  abstr_ref_over_cycles:                  0
% 2.51/1.01  abstr_ref_under_cycles:                 0
% 2.51/1.01  gc_basic_clause_elim:                   0
% 2.51/1.01  forced_gc_time:                         0
% 2.51/1.01  parsing_time:                           0.033
% 2.51/1.01  unif_index_cands_time:                  0.
% 2.51/1.01  unif_index_add_time:                    0.
% 2.51/1.01  orderings_time:                         0.
% 2.51/1.01  out_proof_time:                         0.013
% 2.51/1.01  total_time:                             0.148
% 2.51/1.01  num_of_symbols:                         60
% 2.51/1.01  num_of_terms:                           2135
% 2.51/1.01  
% 2.51/1.01  ------ Preprocessing
% 2.51/1.01  
% 2.51/1.01  num_of_splits:                          0
% 2.51/1.01  num_of_split_atoms:                     0
% 2.51/1.01  num_of_reused_defs:                     0
% 2.51/1.01  num_eq_ax_congr_red:                    14
% 2.51/1.01  num_of_sem_filtered_clauses:            1
% 2.51/1.01  num_of_subtypes:                        0
% 2.51/1.01  monotx_restored_types:                  0
% 2.51/1.01  sat_num_of_epr_types:                   0
% 2.51/1.01  sat_num_of_non_cyclic_types:            0
% 2.51/1.01  sat_guarded_non_collapsed_types:        0
% 2.51/1.01  num_pure_diseq_elim:                    0
% 2.51/1.01  simp_replaced_by:                       0
% 2.51/1.01  res_preprocessed:                       107
% 2.51/1.01  prep_upred:                             0
% 2.51/1.01  prep_unflattend:                        19
% 2.51/1.01  smt_new_axioms:                         0
% 2.51/1.01  pred_elim_cands:                        2
% 2.51/1.01  pred_elim:                              14
% 2.51/1.01  pred_elim_cl:                           16
% 2.51/1.01  pred_elim_cycles:                       16
% 2.51/1.01  merged_defs:                            0
% 2.51/1.01  merged_defs_ncl:                        0
% 2.51/1.01  bin_hyper_res:                          0
% 2.51/1.01  prep_cycles:                            4
% 2.51/1.01  pred_elim_time:                         0.006
% 2.51/1.01  splitting_time:                         0.
% 2.51/1.01  sem_filter_time:                        0.
% 2.51/1.01  monotx_time:                            0.
% 2.51/1.01  subtype_inf_time:                       0.
% 2.51/1.01  
% 2.51/1.01  ------ Problem properties
% 2.51/1.01  
% 2.51/1.01  clauses:                                17
% 2.51/1.01  conjectures:                            4
% 2.51/1.01  epr:                                    1
% 2.51/1.01  horn:                                   14
% 2.51/1.01  ground:                                 5
% 2.51/1.01  unary:                                  6
% 2.51/1.01  binary:                                 3
% 2.51/1.01  lits:                                   37
% 2.51/1.01  lits_eq:                                4
% 2.51/1.01  fd_pure:                                0
% 2.51/1.01  fd_pseudo:                              0
% 2.51/1.01  fd_cond:                                1
% 2.51/1.01  fd_pseudo_cond:                         0
% 2.51/1.01  ac_symbols:                             0
% 2.51/1.01  
% 2.51/1.01  ------ Propositional Solver
% 2.51/1.01  
% 2.51/1.01  prop_solver_calls:                      27
% 2.51/1.01  prop_fast_solver_calls:                 788
% 2.51/1.01  smt_solver_calls:                       0
% 2.51/1.01  smt_fast_solver_calls:                  0
% 2.51/1.01  prop_num_of_clauses:                    1063
% 2.51/1.01  prop_preprocess_simplified:             3760
% 2.51/1.01  prop_fo_subsumed:                       41
% 2.51/1.01  prop_solver_time:                       0.
% 2.51/1.01  smt_solver_time:                        0.
% 2.51/1.01  smt_fast_solver_time:                   0.
% 2.51/1.01  prop_fast_solver_time:                  0.
% 2.51/1.01  prop_unsat_core_time:                   0.
% 2.51/1.01  
% 2.51/1.01  ------ QBF
% 2.51/1.01  
% 2.51/1.01  qbf_q_res:                              0
% 2.51/1.01  qbf_num_tautologies:                    0
% 2.51/1.01  qbf_prep_cycles:                        0
% 2.51/1.01  
% 2.51/1.01  ------ BMC1
% 2.51/1.01  
% 2.51/1.01  bmc1_current_bound:                     -1
% 2.51/1.01  bmc1_last_solved_bound:                 -1
% 2.51/1.01  bmc1_unsat_core_size:                   -1
% 2.51/1.01  bmc1_unsat_core_parents_size:           -1
% 2.51/1.01  bmc1_merge_next_fun:                    0
% 2.51/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.51/1.01  
% 2.51/1.01  ------ Instantiation
% 2.51/1.01  
% 2.51/1.01  inst_num_of_clauses:                    306
% 2.51/1.01  inst_num_in_passive:                    73
% 2.51/1.01  inst_num_in_active:                     188
% 2.51/1.01  inst_num_in_unprocessed:                45
% 2.51/1.01  inst_num_of_loops:                      260
% 2.51/1.01  inst_num_of_learning_restarts:          0
% 2.51/1.01  inst_num_moves_active_passive:          69
% 2.51/1.01  inst_lit_activity:                      0
% 2.51/1.01  inst_lit_activity_moves:                0
% 2.51/1.01  inst_num_tautologies:                   0
% 2.51/1.01  inst_num_prop_implied:                  0
% 2.51/1.01  inst_num_existing_simplified:           0
% 2.51/1.01  inst_num_eq_res_simplified:             0
% 2.51/1.01  inst_num_child_elim:                    0
% 2.51/1.01  inst_num_of_dismatching_blockings:      84
% 2.51/1.01  inst_num_of_non_proper_insts:           271
% 2.51/1.01  inst_num_of_duplicates:                 0
% 2.51/1.01  inst_inst_num_from_inst_to_res:         0
% 2.51/1.01  inst_dismatching_checking_time:         0.
% 2.51/1.01  
% 2.51/1.01  ------ Resolution
% 2.51/1.01  
% 2.51/1.01  res_num_of_clauses:                     0
% 2.51/1.01  res_num_in_passive:                     0
% 2.51/1.01  res_num_in_active:                      0
% 2.51/1.01  res_num_of_loops:                       111
% 2.51/1.01  res_forward_subset_subsumed:            24
% 2.51/1.01  res_backward_subset_subsumed:           0
% 2.51/1.01  res_forward_subsumed:                   0
% 2.51/1.01  res_backward_subsumed:                  0
% 2.51/1.01  res_forward_subsumption_resolution:     0
% 2.51/1.01  res_backward_subsumption_resolution:    1
% 2.51/1.01  res_clause_to_clause_subsumption:       120
% 2.51/1.01  res_orphan_elimination:                 0
% 2.51/1.01  res_tautology_del:                      20
% 2.51/1.01  res_num_eq_res_simplified:              0
% 2.51/1.01  res_num_sel_changes:                    0
% 2.51/1.01  res_moves_from_active_to_pass:          0
% 2.51/1.01  
% 2.51/1.01  ------ Superposition
% 2.51/1.01  
% 2.51/1.01  sup_time_total:                         0.
% 2.51/1.01  sup_time_generating:                    0.
% 2.51/1.01  sup_time_sim_full:                      0.
% 2.51/1.01  sup_time_sim_immed:                     0.
% 2.51/1.01  
% 2.51/1.01  sup_num_of_clauses:                     68
% 2.51/1.01  sup_num_in_active:                      44
% 2.51/1.01  sup_num_in_passive:                     24
% 2.51/1.01  sup_num_of_loops:                       51
% 2.51/1.01  sup_fw_superposition:                   28
% 2.51/1.01  sup_bw_superposition:                   51
% 2.51/1.01  sup_immediate_simplified:               13
% 2.51/1.01  sup_given_eliminated:                   0
% 2.51/1.01  comparisons_done:                       0
% 2.51/1.01  comparisons_avoided:                    12
% 2.51/1.01  
% 2.51/1.01  ------ Simplifications
% 2.51/1.01  
% 2.51/1.01  
% 2.51/1.01  sim_fw_subset_subsumed:                 12
% 2.51/1.01  sim_bw_subset_subsumed:                 6
% 2.51/1.01  sim_fw_subsumed:                        1
% 2.51/1.01  sim_bw_subsumed:                        0
% 2.51/1.01  sim_fw_subsumption_res:                 1
% 2.51/1.01  sim_bw_subsumption_res:                 0
% 2.51/1.01  sim_tautology_del:                      1
% 2.51/1.01  sim_eq_tautology_del:                   2
% 2.51/1.01  sim_eq_res_simp:                        0
% 2.51/1.01  sim_fw_demodulated:                     0
% 2.51/1.01  sim_bw_demodulated:                     2
% 2.51/1.01  sim_light_normalised:                   0
% 2.51/1.01  sim_joinable_taut:                      0
% 2.51/1.01  sim_joinable_simp:                      0
% 2.51/1.01  sim_ac_normalised:                      0
% 2.51/1.01  sim_smt_subsumption:                    0
% 2.51/1.01  
%------------------------------------------------------------------------------
