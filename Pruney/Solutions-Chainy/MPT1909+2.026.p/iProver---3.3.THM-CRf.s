%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:59 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  183 (1174 expanded)
%              Number of clauses        :   88 ( 218 expanded)
%              Number of leaves         :   25 ( 459 expanded)
%              Depth                    :   23
%              Number of atoms          :  708 (12226 expanded)
%              Number of equality atoms :  141 (2219 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6))
        & sK6 = X3
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f48,f47,f46,f45,f44])).

fof(f84,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f88])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f89])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f90])).

fof(f92,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f91])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f92])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f51,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f76,plain,(
    v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f92])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f82,plain,(
    v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f49])).

fof(f96,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f83,f85])).

fof(f86,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f49])).

fof(f95,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(definition_unfolding,[],[f86,f85])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_848,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1131,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | v1_xboole_0(X1_55)
    | k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1130,plain,
    ( k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55)
    | m1_subset_1(X0_55,X1_55) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_1881,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK2),sK6)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_1130])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_540,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_541,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_542,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_12,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_333,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_334,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_338,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_28,c_25])).

cnf(c_11,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_154,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_7])).

cnf(c_155,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_525,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_155,c_22])).

cnf(c_526,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_23,negated_conjecture,
    ( v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_528,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_28,c_25,c_23])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_528])).

cnf(c_583,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_585,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_25,c_541])).

cnf(c_629,plain,
    ( r2_hidden(sK0(X0),X0)
    | u1_struct_0(sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_585])).

cnf(c_630,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_631,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X2_55,X0_55)
    | r2_hidden(X2_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_55))
    | r2_hidden(sK0(u1_struct_0(sK3)),X0_55)
    | ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_1463,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
    | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_1464,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_854,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | ~ v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1488,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_1497,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1488])).

cnf(c_1970,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK2),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_32,c_542,c_631,c_1464,c_1497])).

cnf(c_3,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_852,plain,
    ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1128,plain,
    ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55)) = iProver_top
    | r2_hidden(X0_55,X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_1973,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK6),k1_zfmisc_1(X0_55)) = iProver_top
    | r2_hidden(sK6,X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1970,c_1128])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK3 != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_556,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_25])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_556])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f98])).

cnf(c_17,negated_conjecture,
    ( v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_308,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_309,plain,
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
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_26,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_19,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_557,c_314])).

cnf(c_843,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55) ),
    inference(subtyping,[status(esa)],[c_577])).

cnf(c_1136,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_2091,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
    | r2_hidden(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1973,c_1136])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_847,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1132,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_1882,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1130])).

cnf(c_1256,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(u1_struct_0(sK3),X0_55) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_1441,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(instantiation,[status(thm)],[c_1256])).

cnf(c_2043,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_25,c_16,c_541,c_583,c_1441])).

cnf(c_2045,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
    inference(light_normalisation,[status(thm)],[c_2043,c_1970])).

cnf(c_14,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_849,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2047,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(demodulation,[status(thm)],[c_2045,c_849])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_851,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | r2_hidden(X0_55,X1_55)
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1225,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
    | r2_hidden(X0_55,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_hidden(sK6,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_1324,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1323])).

cnf(c_584,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_41,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2091,c_2047,c_1324,c_584,c_542,c_41,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:33:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.96/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/1.00  
% 1.96/1.00  ------  iProver source info
% 1.96/1.00  
% 1.96/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.96/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/1.00  git: non_committed_changes: false
% 1.96/1.00  git: last_make_outside_of_git: false
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     num_symb
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       true
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  ------ Parsing...
% 1.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/1.00  ------ Proving...
% 1.96/1.00  ------ Problem Properties 
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  clauses                                 14
% 1.96/1.00  conjectures                             4
% 1.96/1.00  EPR                                     2
% 1.96/1.00  Horn                                    11
% 1.96/1.00  unary                                   6
% 1.96/1.00  binary                                  5
% 1.96/1.00  lits                                    25
% 1.96/1.00  lits eq                                 3
% 1.96/1.00  fd_pure                                 0
% 1.96/1.00  fd_pseudo                               0
% 1.96/1.00  fd_cond                                 0
% 1.96/1.00  fd_pseudo_cond                          0
% 1.96/1.00  AC symbols                              0
% 1.96/1.00  
% 1.96/1.00  ------ Schedule dynamic 5 is on 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  Current options:
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     none
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       false
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ Proving...
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS status Theorem for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  fof(f18,conjecture,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f19,negated_conjecture,(
% 1.96/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.96/1.00    inference(negated_conjecture,[],[f18])).
% 1.96/1.00  
% 1.96/1.00  fof(f34,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f19])).
% 1.96/1.00  
% 1.96/1.00  fof(f35,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f34])).
% 1.96/1.00  
% 1.96/1.00  fof(f48,plain,(
% 1.96/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) & sK6 = X3 & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f47,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f46,plain,(
% 1.96/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK4,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f45,plain,(
% 1.96/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(X2,X0,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(sK3,X0) & v4_tex_2(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f44,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & v4_tex_2(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f49,plain,(
% 1.96/1.00    ((((k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & v3_borsuk_1(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & v4_tex_2(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f48,f47,f46,f45,f44])).
% 1.96/1.00  
% 1.96/1.00  fof(f84,plain,(
% 1.96/1.00    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f13,axiom,(
% 1.96/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f25,plain,(
% 1.96/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f13])).
% 1.96/1.00  
% 1.96/1.00  fof(f26,plain,(
% 1.96/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.96/1.00    inference(flattening,[],[f25])).
% 1.96/1.00  
% 1.96/1.00  fof(f63,plain,(
% 1.96/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f26])).
% 1.96/1.00  
% 1.96/1.00  fof(f2,axiom,(
% 1.96/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f52,plain,(
% 1.96/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f2])).
% 1.96/1.00  
% 1.96/1.00  fof(f3,axiom,(
% 1.96/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f53,plain,(
% 1.96/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f3])).
% 1.96/1.00  
% 1.96/1.00  fof(f4,axiom,(
% 1.96/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f54,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f4])).
% 1.96/1.00  
% 1.96/1.00  fof(f5,axiom,(
% 1.96/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f55,plain,(
% 1.96/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f5])).
% 1.96/1.00  
% 1.96/1.00  fof(f6,axiom,(
% 1.96/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f56,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f6])).
% 1.96/1.00  
% 1.96/1.00  fof(f7,axiom,(
% 1.96/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f57,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f7])).
% 1.96/1.00  
% 1.96/1.00  fof(f8,axiom,(
% 1.96/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f58,plain,(
% 1.96/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f8])).
% 1.96/1.00  
% 1.96/1.00  fof(f87,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f57,f58])).
% 1.96/1.00  
% 1.96/1.00  fof(f88,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f56,f87])).
% 1.96/1.00  
% 1.96/1.00  fof(f89,plain,(
% 1.96/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f55,f88])).
% 1.96/1.00  
% 1.96/1.00  fof(f90,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f54,f89])).
% 1.96/1.00  
% 1.96/1.00  fof(f91,plain,(
% 1.96/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f53,f90])).
% 1.96/1.00  
% 1.96/1.00  fof(f92,plain,(
% 1.96/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f52,f91])).
% 1.96/1.00  
% 1.96/1.00  fof(f94,plain,(
% 1.96/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f63,f92])).
% 1.96/1.00  
% 1.96/1.00  fof(f74,plain,(
% 1.96/1.00    l1_pre_topc(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f14,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f27,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f14])).
% 1.96/1.00  
% 1.96/1.00  fof(f64,plain,(
% 1.96/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f27])).
% 1.96/1.00  
% 1.96/1.00  fof(f77,plain,(
% 1.96/1.00    m1_pre_topc(sK3,sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f1,axiom,(
% 1.96/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f36,plain,(
% 1.96/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.96/1.00    inference(nnf_transformation,[],[f1])).
% 1.96/1.00  
% 1.96/1.00  fof(f37,plain,(
% 1.96/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.96/1.00    inference(rectify,[],[f36])).
% 1.96/1.00  
% 1.96/1.00  fof(f38,plain,(
% 1.96/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f39,plain,(
% 1.96/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 1.96/1.00  
% 1.96/1.00  fof(f51,plain,(
% 1.96/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f39])).
% 1.96/1.00  
% 1.96/1.00  fof(f16,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f30,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f16])).
% 1.96/1.00  
% 1.96/1.00  fof(f31,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f30])).
% 1.96/1.00  
% 1.96/1.00  fof(f69,plain,(
% 1.96/1.00    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f72,plain,(
% 1.96/1.00    v2_pre_topc(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f71,plain,(
% 1.96/1.00    ~v2_struct_0(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f15,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f28,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f15])).
% 1.96/1.00  
% 1.96/1.00  fof(f29,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f40,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f29])).
% 1.96/1.00  
% 1.96/1.00  fof(f41,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(rectify,[],[f40])).
% 1.96/1.00  
% 1.96/1.00  fof(f42,plain,(
% 1.96/1.00    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f43,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 1.96/1.00  
% 1.96/1.00  fof(f65,plain,(
% 1.96/1.00    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f43])).
% 1.96/1.00  
% 1.96/1.00  fof(f97,plain,(
% 1.96/1.00    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f65])).
% 1.96/1.00  
% 1.96/1.00  fof(f76,plain,(
% 1.96/1.00    v4_tex_2(sK3,sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f9,axiom,(
% 1.96/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f20,plain,(
% 1.96/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f9])).
% 1.96/1.00  
% 1.96/1.00  fof(f59,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.96/1.00    inference(cnf_transformation,[],[f20])).
% 1.96/1.00  
% 1.96/1.00  fof(f50,plain,(
% 1.96/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f39])).
% 1.96/1.00  
% 1.96/1.00  fof(f10,axiom,(
% 1.96/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f21,plain,(
% 1.96/1.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.96/1.00    inference(ennf_transformation,[],[f10])).
% 1.96/1.00  
% 1.96/1.00  fof(f60,plain,(
% 1.96/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f21])).
% 1.96/1.00  
% 1.96/1.00  fof(f93,plain,(
% 1.96/1.00    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.96/1.00    inference(definition_unfolding,[],[f60,f92])).
% 1.96/1.00  
% 1.96/1.00  fof(f12,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f24,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f12])).
% 1.96/1.00  
% 1.96/1.00  fof(f62,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f24])).
% 1.96/1.00  
% 1.96/1.00  fof(f17,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f32,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f17])).
% 1.96/1.00  
% 1.96/1.00  fof(f33,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f32])).
% 1.96/1.00  
% 1.96/1.00  fof(f70,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f33])).
% 1.96/1.00  
% 1.96/1.00  fof(f98,plain,(
% 1.96/1.00    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f70])).
% 1.96/1.00  
% 1.96/1.00  fof(f82,plain,(
% 1.96/1.00    v3_borsuk_1(sK4,sK2,sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f73,plain,(
% 1.96/1.00    v3_tdlat_3(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f75,plain,(
% 1.96/1.00    ~v2_struct_0(sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f78,plain,(
% 1.96/1.00    v1_funct_1(sK4)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f79,plain,(
% 1.96/1.00    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f80,plain,(
% 1.96/1.00    v5_pre_topc(sK4,sK2,sK3)),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f81,plain,(
% 1.96/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f83,plain,(
% 1.96/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f85,plain,(
% 1.96/1.00    sK5 = sK6),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f96,plain,(
% 1.96/1.00    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.96/1.00    inference(definition_unfolding,[],[f83,f85])).
% 1.96/1.00  
% 1.96/1.00  fof(f86,plain,(
% 1.96/1.00    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 1.96/1.00    inference(cnf_transformation,[],[f49])).
% 1.96/1.00  
% 1.96/1.00  fof(f95,plain,(
% 1.96/1.00    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 1.96/1.00    inference(definition_unfolding,[],[f86,f85])).
% 1.96/1.00  
% 1.96/1.00  fof(f11,axiom,(
% 1.96/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f22,plain,(
% 1.96/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.96/1.00    inference(ennf_transformation,[],[f11])).
% 1.96/1.00  
% 1.96/1.00  fof(f23,plain,(
% 1.96/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.96/1.00    inference(flattening,[],[f22])).
% 1.96/1.00  
% 1.96/1.00  fof(f61,plain,(
% 1.96/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f23])).
% 1.96/1.00  
% 1.96/1.00  cnf(c_15,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_848,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1131,plain,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_6,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,X1)
% 1.96/1.00      | v1_xboole_0(X1)
% 1.96/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f94]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_850,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_55,X1_55)
% 1.96/1.00      | v1_xboole_0(X1_55)
% 1.96/1.00      | k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1130,plain,
% 1.96/1.00      ( k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55)
% 1.96/1.00      | m1_subset_1(X0_55,X1_55) != iProver_top
% 1.96/1.00      | v1_xboole_0(X1_55) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1881,plain,
% 1.96/1.00      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK2),sK6)
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_1131,c_1130]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_25,negated_conjecture,
% 1.96/1.00      ( l1_pre_topc(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_32,plain,
% 1.96/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_7,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_22,negated_conjecture,
% 1.96/1.00      ( m1_pre_topc(sK3,sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_540,plain,
% 1.96/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | sK3 != X0
% 1.96/1.00      | sK2 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_541,plain,
% 1.96/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ l1_pre_topc(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_540]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_542,plain,
% 1.96/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_0,plain,
% 1.96/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_12,plain,
% 1.96/1.00      ( ~ v3_tex_2(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ v1_xboole_0(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_27,negated_conjecture,
% 1.96/1.00      ( v2_pre_topc(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_333,plain,
% 1.96/1.00      ( ~ v3_tex_2(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ v1_xboole_0(X0)
% 1.96/1.00      | sK2 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_334,plain,
% 1.96/1.00      ( ~ v3_tex_2(X0,sK2)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | v2_struct_0(sK2)
% 1.96/1.00      | ~ l1_pre_topc(sK2)
% 1.96/1.00      | ~ v1_xboole_0(X0) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_333]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_28,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_338,plain,
% 1.96/1.00      ( ~ v3_tex_2(X0,sK2)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ v1_xboole_0(X0) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_334,c_28,c_25]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_11,plain,
% 1.96/1.00      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.96/1.00      | ~ v4_tex_2(X0,X1)
% 1.96/1.00      | ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f97]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_154,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ v4_tex_2(X0,X1)
% 1.96/1.00      | v3_tex_2(u1_struct_0(X0),X1)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_11,c_7]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_155,plain,
% 1.96/1.00      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.96/1.00      | ~ v4_tex_2(X0,X1)
% 1.96/1.00      | ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_154]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_525,plain,
% 1.96/1.00      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.96/1.00      | ~ v4_tex_2(X0,X1)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | sK3 != X0
% 1.96/1.00      | sK2 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_155,c_22]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_526,plain,
% 1.96/1.00      ( v3_tex_2(u1_struct_0(sK3),sK2)
% 1.96/1.00      | ~ v4_tex_2(sK3,sK2)
% 1.96/1.00      | v2_struct_0(sK2)
% 1.96/1.00      | ~ l1_pre_topc(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_525]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_23,negated_conjecture,
% 1.96/1.00      ( v4_tex_2(sK3,sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_528,plain,
% 1.96/1.00      ( v3_tex_2(u1_struct_0(sK3),sK2) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_526,c_28,c_25,c_23]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_582,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ v1_xboole_0(X0)
% 1.96/1.00      | u1_struct_0(sK3) != X0
% 1.96/1.00      | sK2 != sK2 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_338,c_528]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_583,plain,
% 1.96/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_582]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_585,plain,
% 1.96/1.00      ( ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_583,c_25,c_541]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_629,plain,
% 1.96/1.00      ( r2_hidden(sK0(X0),X0) | u1_struct_0(sK3) != X0 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_585]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_630,plain,
% 1.96/1.00      ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_629]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_631,plain,
% 1.96/1.00      ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.96/1.00      | ~ r2_hidden(X2,X0)
% 1.96/1.00      | r2_hidden(X2,X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_853,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 1.96/1.00      | ~ r2_hidden(X2_55,X0_55)
% 1.96/1.00      | r2_hidden(X2_55,X1_55) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1316,plain,
% 1.96/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(X0_55))
% 1.96/1.00      | r2_hidden(sK0(u1_struct_0(sK3)),X0_55)
% 1.96/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_853]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1463,plain,
% 1.96/1.00      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
% 1.96/1.00      | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_1316]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1464,plain,
% 1.96/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.96/1.00      | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 1.96/1.00      | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1,plain,
% 1.96/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_854,plain,
% 1.96/1.00      ( ~ r2_hidden(X0_55,X1_55) | ~ v1_xboole_0(X1_55) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1488,plain,
% 1.96/1.00      ( ~ r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2))
% 1.96/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_854]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1497,plain,
% 1.96/1.00      ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK2)) != iProver_top
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_1488]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1970,plain,
% 1.96/1.00      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK2),sK6) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1881,c_32,c_542,c_631,c_1464,c_1497]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3,plain,
% 1.96/1.00      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 1.96/1.00      | ~ r2_hidden(X0,X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f93]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_852,plain,
% 1.96/1.00      ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55))
% 1.96/1.00      | ~ r2_hidden(X0_55,X1_55) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1128,plain,
% 1.96/1.00      ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55)) = iProver_top
% 1.96/1.00      | r2_hidden(X0_55,X1_55) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1973,plain,
% 1.96/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK6),k1_zfmisc_1(X0_55)) = iProver_top
% 1.96/1.00      | r2_hidden(sK6,X0_55) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_1970,c_1128]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_5,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.96/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_551,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.96/1.00      | ~ l1_pre_topc(X2)
% 1.96/1.00      | sK3 != X1
% 1.96/1.00      | sK2 != X2 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_552,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ l1_pre_topc(sK2) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_551]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_556,plain,
% 1.96/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_552,c_25]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_557,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_556]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_13,plain,
% 1.96/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.96/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.96/1.00      | ~ v3_borsuk_1(X0,X1,X2)
% 1.96/1.00      | ~ v4_tex_2(X2,X1)
% 1.96/1.00      | ~ m1_pre_topc(X2,X1)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.96/1.00      | ~ v3_tdlat_3(X1)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f98]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_17,negated_conjecture,
% 1.96/1.00      ( v3_borsuk_1(sK4,sK2,sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_308,plain,
% 1.96/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.96/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.96/1.00      | ~ v4_tex_2(X2,X1)
% 1.96/1.00      | ~ m1_pre_topc(X2,X1)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.96/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ v3_tdlat_3(X1)
% 1.96/1.00      | ~ v1_funct_1(X0)
% 1.96/1.00      | ~ v2_pre_topc(X1)
% 1.96/1.00      | v2_struct_0(X1)
% 1.96/1.00      | v2_struct_0(X2)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 1.96/1.00      | sK4 != X0
% 1.96/1.00      | sK3 != X2
% 1.96/1.00      | sK2 != X1 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_309,plain,
% 1.96/1.00      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 1.96/1.00      | ~ v5_pre_topc(sK4,sK2,sK3)
% 1.96/1.00      | ~ v4_tex_2(sK3,sK2)
% 1.96/1.00      | ~ m1_pre_topc(sK3,sK2)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 1.96/1.00      | ~ v3_tdlat_3(sK2)
% 1.96/1.00      | ~ v1_funct_1(sK4)
% 1.96/1.00      | ~ v2_pre_topc(sK2)
% 1.96/1.00      | v2_struct_0(sK3)
% 1.96/1.00      | v2_struct_0(sK2)
% 1.96/1.00      | ~ l1_pre_topc(sK2)
% 1.96/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.96/1.00      inference(unflattening,[status(thm)],[c_308]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_26,negated_conjecture,
% 1.96/1.00      ( v3_tdlat_3(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_24,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_21,negated_conjecture,
% 1.96/1.00      ( v1_funct_1(sK4) ),
% 1.96/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_20,negated_conjecture,
% 1.96/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_19,negated_conjecture,
% 1.96/1.00      ( v5_pre_topc(sK4,sK2,sK3) ),
% 1.96/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_18,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 1.96/1.00      inference(cnf_transformation,[],[f81]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_313,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_309,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,
% 1.96/1.00                 c_18]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_314,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.96/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_313]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_577,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.96/1.00      inference(backward_subsumption_resolution,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_557,c_314]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_843,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.96/1.00      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_577]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1136,plain,
% 1.96/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55)
% 1.96/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2091,plain,
% 1.96/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK2),sK6)) = k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))
% 1.96/1.00      | r2_hidden(sK6,u1_struct_0(sK3)) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_1973,c_1136]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_16,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f96]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_847,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1132,plain,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1882,plain,
% 1.96/1.00      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6)
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_1132,c_1130]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1256,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.96/1.00      | k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(u1_struct_0(sK3),X0_55) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_850]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1441,plain,
% 1.96/1.00      ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 1.96/1.00      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_1256]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2043,plain,
% 1.96/1.00      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1882,c_25,c_16,c_541,c_583,c_1441]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2045,plain,
% 1.96/1.00      ( k6_domain_1(u1_struct_0(sK2),sK6) = k6_domain_1(u1_struct_0(sK3),sK6) ),
% 1.96/1.00      inference(light_normalisation,[status(thm)],[c_2043,c_1970]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_14,negated_conjecture,
% 1.96/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f95]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_849,negated_conjecture,
% 1.96/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2047,plain,
% 1.96/1.00      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK2),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
% 1.96/1.00      inference(demodulation,[status(thm)],[c_2045,c_849]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f61]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_851,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_55,X1_55)
% 1.96/1.00      | r2_hidden(X0_55,X1_55)
% 1.96/1.00      | v1_xboole_0(X1_55) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1225,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK3))
% 1.96/1.00      | r2_hidden(X0_55,u1_struct_0(sK3))
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_851]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1323,plain,
% 1.96/1.00      ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
% 1.96/1.00      | r2_hidden(sK6,u1_struct_0(sK3))
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK3)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_1225]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1324,plain,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.96/1.00      | r2_hidden(sK6,u1_struct_0(sK3)) = iProver_top
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_1323]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_584,plain,
% 1.96/1.00      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.96/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_41,plain,
% 1.96/1.00      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(contradiction,plain,
% 1.96/1.00      ( $false ),
% 1.96/1.00      inference(minisat,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_2091,c_2047,c_1324,c_584,c_542,c_41,c_32]) ).
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  ------                               Statistics
% 1.96/1.00  
% 1.96/1.00  ------ General
% 1.96/1.00  
% 1.96/1.00  abstr_ref_over_cycles:                  0
% 1.96/1.00  abstr_ref_under_cycles:                 0
% 1.96/1.00  gc_basic_clause_elim:                   0
% 1.96/1.00  forced_gc_time:                         0
% 1.96/1.00  parsing_time:                           0.011
% 1.96/1.00  unif_index_cands_time:                  0.
% 1.96/1.00  unif_index_add_time:                    0.
% 1.96/1.00  orderings_time:                         0.
% 1.96/1.00  out_proof_time:                         0.013
% 1.96/1.00  total_time:                             0.138
% 1.96/1.00  num_of_symbols:                         64
% 1.96/1.00  num_of_terms:                           1754
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing
% 1.96/1.00  
% 1.96/1.00  num_of_splits:                          0
% 1.96/1.00  num_of_split_atoms:                     0
% 1.96/1.00  num_of_reused_defs:                     0
% 1.96/1.00  num_eq_ax_congr_red:                    36
% 1.96/1.00  num_of_sem_filtered_clauses:            1
% 1.96/1.00  num_of_subtypes:                        3
% 1.96/1.00  monotx_restored_types:                  0
% 1.96/1.00  sat_num_of_epr_types:                   0
% 1.96/1.00  sat_num_of_non_cyclic_types:            0
% 1.96/1.00  sat_guarded_non_collapsed_types:        0
% 1.96/1.00  num_pure_diseq_elim:                    0
% 1.96/1.00  simp_replaced_by:                       0
% 1.96/1.00  res_preprocessed:                       96
% 1.96/1.00  prep_upred:                             0
% 1.96/1.00  prep_unflattend:                        31
% 1.96/1.00  smt_new_axioms:                         0
% 1.96/1.00  pred_elim_cands:                        3
% 1.96/1.00  pred_elim:                              11
% 1.96/1.00  pred_elim_cl:                           15
% 1.96/1.00  pred_elim_cycles:                       15
% 1.96/1.00  merged_defs:                            0
% 1.96/1.00  merged_defs_ncl:                        0
% 1.96/1.00  bin_hyper_res:                          0
% 1.96/1.00  prep_cycles:                            4
% 1.96/1.00  pred_elim_time:                         0.007
% 1.96/1.00  splitting_time:                         0.
% 1.96/1.00  sem_filter_time:                        0.
% 1.96/1.00  monotx_time:                            0.
% 1.96/1.00  subtype_inf_time:                       0.
% 1.96/1.00  
% 1.96/1.00  ------ Problem properties
% 1.96/1.00  
% 1.96/1.00  clauses:                                14
% 1.96/1.00  conjectures:                            4
% 1.96/1.00  epr:                                    2
% 1.96/1.00  horn:                                   11
% 1.96/1.00  ground:                                 6
% 1.96/1.00  unary:                                  6
% 1.96/1.00  binary:                                 5
% 1.96/1.00  lits:                                   25
% 1.96/1.00  lits_eq:                                3
% 1.96/1.00  fd_pure:                                0
% 1.96/1.00  fd_pseudo:                              0
% 1.96/1.00  fd_cond:                                0
% 1.96/1.00  fd_pseudo_cond:                         0
% 1.96/1.00  ac_symbols:                             0
% 1.96/1.00  
% 1.96/1.00  ------ Propositional Solver
% 1.96/1.00  
% 1.96/1.00  prop_solver_calls:                      27
% 1.96/1.00  prop_fast_solver_calls:                 606
% 1.96/1.00  smt_solver_calls:                       0
% 1.96/1.00  smt_fast_solver_calls:                  0
% 1.96/1.00  prop_num_of_clauses:                    620
% 1.96/1.00  prop_preprocess_simplified:             2817
% 1.96/1.00  prop_fo_subsumed:                       27
% 1.96/1.00  prop_solver_time:                       0.
% 1.96/1.00  smt_solver_time:                        0.
% 1.96/1.00  smt_fast_solver_time:                   0.
% 1.96/1.00  prop_fast_solver_time:                  0.
% 1.96/1.00  prop_unsat_core_time:                   0.
% 1.96/1.00  
% 1.96/1.00  ------ QBF
% 1.96/1.00  
% 1.96/1.00  qbf_q_res:                              0
% 1.96/1.00  qbf_num_tautologies:                    0
% 1.96/1.00  qbf_prep_cycles:                        0
% 1.96/1.00  
% 1.96/1.00  ------ BMC1
% 1.96/1.00  
% 1.96/1.00  bmc1_current_bound:                     -1
% 1.96/1.00  bmc1_last_solved_bound:                 -1
% 1.96/1.00  bmc1_unsat_core_size:                   -1
% 1.96/1.00  bmc1_unsat_core_parents_size:           -1
% 1.96/1.00  bmc1_merge_next_fun:                    0
% 1.96/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation
% 1.96/1.00  
% 1.96/1.00  inst_num_of_clauses:                    165
% 1.96/1.00  inst_num_in_passive:                    12
% 1.96/1.00  inst_num_in_active:                     133
% 1.96/1.00  inst_num_in_unprocessed:                20
% 1.96/1.00  inst_num_of_loops:                      140
% 1.96/1.00  inst_num_of_learning_restarts:          0
% 1.96/1.00  inst_num_moves_active_passive:          4
% 1.96/1.00  inst_lit_activity:                      0
% 1.96/1.00  inst_lit_activity_moves:                0
% 1.96/1.00  inst_num_tautologies:                   0
% 1.96/1.00  inst_num_prop_implied:                  0
% 1.96/1.00  inst_num_existing_simplified:           0
% 1.96/1.00  inst_num_eq_res_simplified:             0
% 1.96/1.00  inst_num_child_elim:                    0
% 1.96/1.00  inst_num_of_dismatching_blockings:      16
% 1.96/1.00  inst_num_of_non_proper_insts:           151
% 1.96/1.00  inst_num_of_duplicates:                 0
% 1.96/1.00  inst_inst_num_from_inst_to_res:         0
% 1.96/1.00  inst_dismatching_checking_time:         0.
% 1.96/1.00  
% 1.96/1.00  ------ Resolution
% 1.96/1.00  
% 1.96/1.00  res_num_of_clauses:                     0
% 1.96/1.00  res_num_in_passive:                     0
% 1.96/1.00  res_num_in_active:                      0
% 1.96/1.00  res_num_of_loops:                       100
% 1.96/1.00  res_forward_subset_subsumed:            50
% 1.96/1.00  res_backward_subset_subsumed:           2
% 1.96/1.00  res_forward_subsumed:                   0
% 1.96/1.00  res_backward_subsumed:                  0
% 1.96/1.00  res_forward_subsumption_resolution:     0
% 1.96/1.00  res_backward_subsumption_resolution:    1
% 1.96/1.00  res_clause_to_clause_subsumption:       47
% 1.96/1.00  res_orphan_elimination:                 0
% 1.96/1.00  res_tautology_del:                      27
% 1.96/1.00  res_num_eq_res_simplified:              0
% 1.96/1.00  res_num_sel_changes:                    0
% 1.96/1.00  res_moves_from_active_to_pass:          0
% 1.96/1.00  
% 1.96/1.00  ------ Superposition
% 1.96/1.00  
% 1.96/1.00  sup_time_total:                         0.
% 1.96/1.00  sup_time_generating:                    0.
% 1.96/1.00  sup_time_sim_full:                      0.
% 1.96/1.00  sup_time_sim_immed:                     0.
% 1.96/1.00  
% 1.96/1.00  sup_num_of_clauses:                     37
% 1.96/1.00  sup_num_in_active:                      27
% 1.96/1.00  sup_num_in_passive:                     10
% 1.96/1.00  sup_num_of_loops:                       27
% 1.96/1.00  sup_fw_superposition:                   14
% 1.96/1.00  sup_bw_superposition:                   16
% 1.96/1.00  sup_immediate_simplified:               0
% 1.96/1.00  sup_given_eliminated:                   0
% 1.96/1.00  comparisons_done:                       0
% 1.96/1.00  comparisons_avoided:                    0
% 1.96/1.00  
% 1.96/1.00  ------ Simplifications
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  sim_fw_subset_subsumed:                 0
% 1.96/1.00  sim_bw_subset_subsumed:                 0
% 1.96/1.00  sim_fw_subsumed:                        0
% 1.96/1.00  sim_bw_subsumed:                        0
% 1.96/1.00  sim_fw_subsumption_res:                 0
% 1.96/1.00  sim_bw_subsumption_res:                 0
% 1.96/1.00  sim_tautology_del:                      3
% 1.96/1.00  sim_eq_tautology_del:                   0
% 1.96/1.00  sim_eq_res_simp:                        0
% 1.96/1.00  sim_fw_demodulated:                     0
% 1.96/1.00  sim_bw_demodulated:                     1
% 1.96/1.00  sim_light_normalised:                   1
% 1.96/1.00  sim_joinable_taut:                      0
% 1.96/1.00  sim_joinable_simp:                      0
% 1.96/1.00  sim_ac_normalised:                      0
% 1.96/1.00  sim_smt_subsumption:                    0
% 1.96/1.00  
%------------------------------------------------------------------------------
