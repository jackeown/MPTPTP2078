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
% DateTime   : Thu Dec  3 12:27:58 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  204 (1423 expanded)
%              Number of clauses        :  101 ( 255 expanded)
%              Number of leaves         :   27 ( 563 expanded)
%              Depth                    :   24
%              Number of atoms          :  784 (15165 expanded)
%              Number of equality atoms :  181 (2788 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK7))
        & sK7 = X3
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
            & sK6 = X4
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & v3_borsuk_1(sK5,X0,X1)
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK5,X0,X1)
        & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k6_domain_1(u1_struct_0(sK4),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK4)) )
            & v3_borsuk_1(X2,X0,sK4)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4))))
            & v5_pre_topc(X2,X0,sK4)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK4,X0)
        & v4_tex_2(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
                      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK3)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK3,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK3,X1)
              & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK3)
          & v4_tex_2(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v3_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))
    & sK6 = sK7
    & m1_subset_1(sK7,u1_struct_0(sK3))
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & v3_borsuk_1(sK5,sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    & v5_pre_topc(sK5,sK3,sK4)
    & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    & v1_funct_1(sK5)
    & m1_pre_topc(sK4,sK3)
    & v4_tex_2(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v3_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f37,f55,f54,f53,f52,f51])).

fof(f96,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(definition_unfolding,[],[f94,f96])).

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

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f98])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f99])).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f100])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f101])).

fof(f103,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f102])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f73,f103])).

fof(f85,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK2(X0,X1),X0)
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f87,plain,(
    v4_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f81])).

fof(f93,plain,(
    v3_borsuk_1(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f74,f102])).

fof(f97,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(definition_unfolding,[],[f97,f96])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1154,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1634,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1158,plain,
    ( ~ m1_subset_1(X0_58,X1_58)
    | v1_xboole_0(X1_58)
    | k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58) = k6_domain_1(X1_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1631,plain,
    ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58) = k6_domain_1(X1_58,X0_58)
    | m1_subset_1(X0_58,X1_58) != iProver_top
    | v1_xboole_0(X1_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_2372,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_1631])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_623,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_624,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_623])).

cnf(c_16,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_451,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_452,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_456,plain,
    ( ~ v3_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_32,c_29])).

cnf(c_15,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_178,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_11])).

cnf(c_179,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_608,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_26])).

cnf(c_609,plain,
    ( v3_tex_2(u1_struct_0(sK4),sK3)
    | ~ v4_tex_2(sK4,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_27,negated_conjecture,
    ( v4_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_611,plain,
    ( v3_tex_2(u1_struct_0(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_32,c_29,c_27])).

cnf(c_665,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_456,c_611])).

cnf(c_666,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_1798,plain,
    ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58) = k6_domain_1(u1_struct_0(sK4),X0_58) ),
    inference(instantiation,[status(thm)],[c_1158])).

cnf(c_2011,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_2636,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2372,c_29,c_20,c_624,c_666,c_2011])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1155,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1633,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1155])).

cnf(c_2371,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1631])).

cnf(c_2639,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK7) = k6_domain_1(u1_struct_0(sK4),sK7)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2636,c_2371])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1166,plain,
    ( r2_hidden(sK0(X0_58),X0_58)
    | v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1623,plain,
    ( r2_hidden(sK0(X0_58),X0_58) = iProver_top
    | v1_xboole_0(X0_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_626,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_29])).

cnf(c_1152,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subtyping,[status(esa)],[c_626])).

cnf(c_1636,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1152])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1160,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(X1_58))
    | r1_tarski(X0_58,X1_58) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1629,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(X1_58)) != iProver_top
    | r1_tarski(X0_58,X1_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1160])).

cnf(c_2046,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_1629])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1162,plain,
    ( ~ r1_tarski(X0_58,X1_58)
    | ~ r2_hidden(X0_61,X0_58)
    | r2_hidden(X0_61,X1_58) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1627,plain,
    ( r1_tarski(X0_58,X1_58) != iProver_top
    | r2_hidden(X0_61,X0_58) != iProver_top
    | r2_hidden(X0_61,X1_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1162])).

cnf(c_2348,plain,
    ( r2_hidden(X0_61,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_61,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_1627])).

cnf(c_2998,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_2348])).

cnf(c_36,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_625,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_667,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_3090,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2998,c_36,c_625,c_667])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1165,plain,
    ( ~ r2_hidden(X0_61,X0_58)
    | ~ v1_xboole_0(X0_58) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1624,plain,
    ( r2_hidden(X0_61,X0_58) != iProver_top
    | v1_xboole_0(X0_58) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_3095,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3090,c_1624])).

cnf(c_3278,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2639,c_3095])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1159,plain,
    ( ~ m1_subset_1(X0_58,X1_58)
    | ~ m1_subset_1(X2_58,X1_58)
    | m1_subset_1(k7_domain_1(X1_58,X2_58,X0_58),k1_zfmisc_1(X1_58))
    | v1_xboole_0(X1_58) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1630,plain,
    ( m1_subset_1(X0_58,X1_58) != iProver_top
    | m1_subset_1(X2_58,X1_58) != iProver_top
    | m1_subset_1(k7_domain_1(X1_58,X2_58,X0_58),k1_zfmisc_1(X1_58)) = iProver_top
    | v1_xboole_0(X1_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1159])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK4 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_639,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_635,c_29])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_639])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f109])).

cnf(c_21,negated_conjecture,
    ( v3_borsuk_1(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_426,plain,
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
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_427,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v5_pre_topc(sK5,sK3,sK4)
    | ~ v4_tex_2(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v3_tdlat_3(sK3)
    | ~ v1_funct_1(sK5)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_30,negated_conjecture,
    ( v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_23,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(renaming,[status(thm)],[c_431])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_640,c_432])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_58) = k2_pre_topc(sK3,X0_58) ),
    inference(subtyping,[status(esa)],[c_660])).

cnf(c_1638,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_58) = k2_pre_topc(sK3,X0_58)
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1150])).

cnf(c_2249,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58))
    | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_1638])).

cnf(c_2905,plain,
    ( m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2249,c_36,c_625,c_667])).

cnf(c_2906,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58))
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2905])).

cnf(c_2914,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),sK7,X0_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),sK7,X0_58))
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_2906])).

cnf(c_3147,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),sK7,sK7)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),sK7,sK7)) ),
    inference(superposition,[status(thm)],[c_1634,c_2914])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0) = k7_domain_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1157,plain,
    ( ~ m1_subset_1(X0_58,X1_58)
    | ~ m1_subset_1(X2_58,X1_58)
    | v1_xboole_0(X1_58)
    | k6_enumset1(X2_58,X2_58,X2_58,X2_58,X2_58,X2_58,X2_58,X0_58) = k7_domain_1(X1_58,X2_58,X0_58) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1632,plain,
    ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X1_58) = k7_domain_1(X2_58,X0_58,X1_58)
    | m1_subset_1(X1_58,X2_58) != iProver_top
    | m1_subset_1(X0_58,X2_58) != iProver_top
    | v1_xboole_0(X2_58) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1157])).

cnf(c_2491,plain,
    ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,sK7) = k7_domain_1(u1_struct_0(sK4),X0_58,sK7)
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_1632])).

cnf(c_2763,plain,
    ( m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
    | k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,sK7) = k7_domain_1(u1_struct_0(sK4),X0_58,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_36,c_625,c_667])).

cnf(c_2764,plain,
    ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,sK7) = k7_domain_1(u1_struct_0(sK4),X0_58,sK7)
    | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2763])).

cnf(c_2771,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k7_domain_1(u1_struct_0(sK4),sK7,sK7) ),
    inference(superposition,[status(thm)],[c_1634,c_2764])).

cnf(c_2772,plain,
    ( k7_domain_1(u1_struct_0(sK4),sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
    inference(light_normalisation,[status(thm)],[c_2771,c_2636])).

cnf(c_3148,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK4),sK7)) ),
    inference(light_normalisation,[status(thm)],[c_3147,c_2772])).

cnf(c_18,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1156,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3219,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(demodulation,[status(thm)],[c_3148,c_1156])).

cnf(c_3281,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(demodulation,[status(thm)],[c_3278,c_3219])).

cnf(c_3291,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3281])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:55:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.08/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/0.99  
% 2.08/0.99  ------  iProver source info
% 2.08/0.99  
% 2.08/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.08/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/0.99  git: non_committed_changes: false
% 2.08/0.99  git: last_make_outside_of_git: false
% 2.08/0.99  
% 2.08/0.99  ------ 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options
% 2.08/0.99  
% 2.08/0.99  --out_options                           all
% 2.08/0.99  --tptp_safe_out                         true
% 2.08/0.99  --problem_path                          ""
% 2.08/0.99  --include_path                          ""
% 2.08/0.99  --clausifier                            res/vclausify_rel
% 2.08/0.99  --clausifier_options                    --mode clausify
% 2.08/0.99  --stdin                                 false
% 2.08/0.99  --stats_out                             all
% 2.08/0.99  
% 2.08/0.99  ------ General Options
% 2.08/0.99  
% 2.08/0.99  --fof                                   false
% 2.08/0.99  --time_out_real                         305.
% 2.08/0.99  --time_out_virtual                      -1.
% 2.08/0.99  --symbol_type_check                     false
% 2.08/0.99  --clausify_out                          false
% 2.08/0.99  --sig_cnt_out                           false
% 2.08/0.99  --trig_cnt_out                          false
% 2.08/0.99  --trig_cnt_out_tolerance                1.
% 2.08/0.99  --trig_cnt_out_sk_spl                   false
% 2.08/0.99  --abstr_cl_out                          false
% 2.08/0.99  
% 2.08/0.99  ------ Global Options
% 2.08/0.99  
% 2.08/0.99  --schedule                              default
% 2.08/0.99  --add_important_lit                     false
% 2.08/0.99  --prop_solver_per_cl                    1000
% 2.08/0.99  --min_unsat_core                        false
% 2.08/0.99  --soft_assumptions                      false
% 2.08/0.99  --soft_lemma_size                       3
% 2.08/0.99  --prop_impl_unit_size                   0
% 2.08/0.99  --prop_impl_unit                        []
% 2.08/0.99  --share_sel_clauses                     true
% 2.08/0.99  --reset_solvers                         false
% 2.08/0.99  --bc_imp_inh                            [conj_cone]
% 2.08/0.99  --conj_cone_tolerance                   3.
% 2.08/0.99  --extra_neg_conj                        none
% 2.08/0.99  --large_theory_mode                     true
% 2.08/0.99  --prolific_symb_bound                   200
% 2.08/0.99  --lt_threshold                          2000
% 2.08/0.99  --clause_weak_htbl                      true
% 2.08/0.99  --gc_record_bc_elim                     false
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing Options
% 2.08/0.99  
% 2.08/0.99  --preprocessing_flag                    true
% 2.08/0.99  --time_out_prep_mult                    0.1
% 2.08/0.99  --splitting_mode                        input
% 2.08/0.99  --splitting_grd                         true
% 2.08/0.99  --splitting_cvd                         false
% 2.08/0.99  --splitting_cvd_svl                     false
% 2.08/0.99  --splitting_nvd                         32
% 2.08/0.99  --sub_typing                            true
% 2.08/0.99  --prep_gs_sim                           true
% 2.08/0.99  --prep_unflatten                        true
% 2.08/0.99  --prep_res_sim                          true
% 2.08/0.99  --prep_upred                            true
% 2.08/0.99  --prep_sem_filter                       exhaustive
% 2.08/0.99  --prep_sem_filter_out                   false
% 2.08/0.99  --pred_elim                             true
% 2.08/0.99  --res_sim_input                         true
% 2.08/0.99  --eq_ax_congr_red                       true
% 2.08/0.99  --pure_diseq_elim                       true
% 2.08/0.99  --brand_transform                       false
% 2.08/0.99  --non_eq_to_eq                          false
% 2.08/0.99  --prep_def_merge                        true
% 2.08/0.99  --prep_def_merge_prop_impl              false
% 2.08/0.99  --prep_def_merge_mbd                    true
% 2.08/0.99  --prep_def_merge_tr_red                 false
% 2.08/0.99  --prep_def_merge_tr_cl                  false
% 2.08/0.99  --smt_preprocessing                     true
% 2.08/0.99  --smt_ac_axioms                         fast
% 2.08/0.99  --preprocessed_out                      false
% 2.08/0.99  --preprocessed_stats                    false
% 2.08/0.99  
% 2.08/0.99  ------ Abstraction refinement Options
% 2.08/0.99  
% 2.08/0.99  --abstr_ref                             []
% 2.08/0.99  --abstr_ref_prep                        false
% 2.08/0.99  --abstr_ref_until_sat                   false
% 2.08/0.99  --abstr_ref_sig_restrict                funpre
% 2.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.99  --abstr_ref_under                       []
% 2.08/0.99  
% 2.08/0.99  ------ SAT Options
% 2.08/0.99  
% 2.08/0.99  --sat_mode                              false
% 2.08/0.99  --sat_fm_restart_options                ""
% 2.08/0.99  --sat_gr_def                            false
% 2.08/0.99  --sat_epr_types                         true
% 2.08/0.99  --sat_non_cyclic_types                  false
% 2.08/0.99  --sat_finite_models                     false
% 2.08/0.99  --sat_fm_lemmas                         false
% 2.08/0.99  --sat_fm_prep                           false
% 2.08/0.99  --sat_fm_uc_incr                        true
% 2.08/0.99  --sat_out_model                         small
% 2.08/0.99  --sat_out_clauses                       false
% 2.08/0.99  
% 2.08/0.99  ------ QBF Options
% 2.08/0.99  
% 2.08/0.99  --qbf_mode                              false
% 2.08/0.99  --qbf_elim_univ                         false
% 2.08/0.99  --qbf_dom_inst                          none
% 2.08/0.99  --qbf_dom_pre_inst                      false
% 2.08/0.99  --qbf_sk_in                             false
% 2.08/0.99  --qbf_pred_elim                         true
% 2.08/0.99  --qbf_split                             512
% 2.08/0.99  
% 2.08/0.99  ------ BMC1 Options
% 2.08/0.99  
% 2.08/0.99  --bmc1_incremental                      false
% 2.08/0.99  --bmc1_axioms                           reachable_all
% 2.08/0.99  --bmc1_min_bound                        0
% 2.08/0.99  --bmc1_max_bound                        -1
% 2.08/0.99  --bmc1_max_bound_default                -1
% 2.08/0.99  --bmc1_symbol_reachability              true
% 2.08/0.99  --bmc1_property_lemmas                  false
% 2.08/0.99  --bmc1_k_induction                      false
% 2.08/0.99  --bmc1_non_equiv_states                 false
% 2.08/0.99  --bmc1_deadlock                         false
% 2.08/0.99  --bmc1_ucm                              false
% 2.08/0.99  --bmc1_add_unsat_core                   none
% 2.08/0.99  --bmc1_unsat_core_children              false
% 2.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.99  --bmc1_out_stat                         full
% 2.08/0.99  --bmc1_ground_init                      false
% 2.08/0.99  --bmc1_pre_inst_next_state              false
% 2.08/0.99  --bmc1_pre_inst_state                   false
% 2.08/0.99  --bmc1_pre_inst_reach_state             false
% 2.08/0.99  --bmc1_out_unsat_core                   false
% 2.08/0.99  --bmc1_aig_witness_out                  false
% 2.08/0.99  --bmc1_verbose                          false
% 2.08/0.99  --bmc1_dump_clauses_tptp                false
% 2.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.99  --bmc1_dump_file                        -
% 2.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.99  --bmc1_ucm_extend_mode                  1
% 2.08/0.99  --bmc1_ucm_init_mode                    2
% 2.08/0.99  --bmc1_ucm_cone_mode                    none
% 2.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.99  --bmc1_ucm_relax_model                  4
% 2.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.99  --bmc1_ucm_layered_model                none
% 2.08/0.99  --bmc1_ucm_max_lemma_size               10
% 2.08/0.99  
% 2.08/0.99  ------ AIG Options
% 2.08/0.99  
% 2.08/0.99  --aig_mode                              false
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation Options
% 2.08/0.99  
% 2.08/0.99  --instantiation_flag                    true
% 2.08/0.99  --inst_sos_flag                         false
% 2.08/0.99  --inst_sos_phase                        true
% 2.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel_side                     num_symb
% 2.08/0.99  --inst_solver_per_active                1400
% 2.08/0.99  --inst_solver_calls_frac                1.
% 2.08/0.99  --inst_passive_queue_type               priority_queues
% 2.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.99  --inst_passive_queues_freq              [25;2]
% 2.08/0.99  --inst_dismatching                      true
% 2.08/0.99  --inst_eager_unprocessed_to_passive     true
% 2.08/0.99  --inst_prop_sim_given                   true
% 2.08/0.99  --inst_prop_sim_new                     false
% 2.08/0.99  --inst_subs_new                         false
% 2.08/0.99  --inst_eq_res_simp                      false
% 2.08/0.99  --inst_subs_given                       false
% 2.08/0.99  --inst_orphan_elimination               true
% 2.08/0.99  --inst_learning_loop_flag               true
% 2.08/0.99  --inst_learning_start                   3000
% 2.08/0.99  --inst_learning_factor                  2
% 2.08/0.99  --inst_start_prop_sim_after_learn       3
% 2.08/0.99  --inst_sel_renew                        solver
% 2.08/0.99  --inst_lit_activity_flag                true
% 2.08/0.99  --inst_restr_to_given                   false
% 2.08/0.99  --inst_activity_threshold               500
% 2.08/0.99  --inst_out_proof                        true
% 2.08/0.99  
% 2.08/0.99  ------ Resolution Options
% 2.08/0.99  
% 2.08/0.99  --resolution_flag                       true
% 2.08/0.99  --res_lit_sel                           adaptive
% 2.08/0.99  --res_lit_sel_side                      none
% 2.08/0.99  --res_ordering                          kbo
% 2.08/0.99  --res_to_prop_solver                    active
% 2.08/0.99  --res_prop_simpl_new                    false
% 2.08/0.99  --res_prop_simpl_given                  true
% 2.08/0.99  --res_passive_queue_type                priority_queues
% 2.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.99  --res_passive_queues_freq               [15;5]
% 2.08/0.99  --res_forward_subs                      full
% 2.08/0.99  --res_backward_subs                     full
% 2.08/0.99  --res_forward_subs_resolution           true
% 2.08/0.99  --res_backward_subs_resolution          true
% 2.08/0.99  --res_orphan_elimination                true
% 2.08/0.99  --res_time_limit                        2.
% 2.08/0.99  --res_out_proof                         true
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Options
% 2.08/0.99  
% 2.08/0.99  --superposition_flag                    true
% 2.08/0.99  --sup_passive_queue_type                priority_queues
% 2.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.99  --demod_completeness_check              fast
% 2.08/0.99  --demod_use_ground                      true
% 2.08/0.99  --sup_to_prop_solver                    passive
% 2.08/0.99  --sup_prop_simpl_new                    true
% 2.08/0.99  --sup_prop_simpl_given                  true
% 2.08/0.99  --sup_fun_splitting                     false
% 2.08/0.99  --sup_smt_interval                      50000
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Simplification Setup
% 2.08/0.99  
% 2.08/0.99  --sup_indices_passive                   []
% 2.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_full_bw                           [BwDemod]
% 2.08/0.99  --sup_immed_triv                        [TrivRules]
% 2.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_immed_bw_main                     []
% 2.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  
% 2.08/0.99  ------ Combination Options
% 2.08/0.99  
% 2.08/0.99  --comb_res_mult                         3
% 2.08/0.99  --comb_sup_mult                         2
% 2.08/0.99  --comb_inst_mult                        10
% 2.08/0.99  
% 2.08/0.99  ------ Debug Options
% 2.08/0.99  
% 2.08/0.99  --dbg_backtrace                         false
% 2.08/0.99  --dbg_dump_prop_clauses                 false
% 2.08/0.99  --dbg_dump_prop_clauses_file            -
% 2.08/0.99  --dbg_out_stat                          false
% 2.08/0.99  ------ Parsing...
% 2.08/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/0.99  ------ Proving...
% 2.08/0.99  ------ Problem Properties 
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  clauses                                 18
% 2.08/0.99  conjectures                             4
% 2.08/0.99  EPR                                     2
% 2.08/0.99  Horn                                    13
% 2.08/0.99  unary                                   6
% 2.08/0.99  binary                                  8
% 2.08/0.99  lits                                    36
% 2.08/0.99  lits eq                                 4
% 2.08/0.99  fd_pure                                 0
% 2.08/0.99  fd_pseudo                               0
% 2.08/0.99  fd_cond                                 0
% 2.08/0.99  fd_pseudo_cond                          0
% 2.08/0.99  AC symbols                              0
% 2.08/0.99  
% 2.08/0.99  ------ Schedule dynamic 5 is on 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  ------ 
% 2.08/0.99  Current options:
% 2.08/0.99  ------ 
% 2.08/0.99  
% 2.08/0.99  ------ Input Options
% 2.08/0.99  
% 2.08/0.99  --out_options                           all
% 2.08/0.99  --tptp_safe_out                         true
% 2.08/0.99  --problem_path                          ""
% 2.08/0.99  --include_path                          ""
% 2.08/0.99  --clausifier                            res/vclausify_rel
% 2.08/0.99  --clausifier_options                    --mode clausify
% 2.08/0.99  --stdin                                 false
% 2.08/0.99  --stats_out                             all
% 2.08/0.99  
% 2.08/0.99  ------ General Options
% 2.08/0.99  
% 2.08/0.99  --fof                                   false
% 2.08/0.99  --time_out_real                         305.
% 2.08/0.99  --time_out_virtual                      -1.
% 2.08/0.99  --symbol_type_check                     false
% 2.08/0.99  --clausify_out                          false
% 2.08/0.99  --sig_cnt_out                           false
% 2.08/0.99  --trig_cnt_out                          false
% 2.08/0.99  --trig_cnt_out_tolerance                1.
% 2.08/0.99  --trig_cnt_out_sk_spl                   false
% 2.08/0.99  --abstr_cl_out                          false
% 2.08/0.99  
% 2.08/0.99  ------ Global Options
% 2.08/0.99  
% 2.08/0.99  --schedule                              default
% 2.08/0.99  --add_important_lit                     false
% 2.08/0.99  --prop_solver_per_cl                    1000
% 2.08/0.99  --min_unsat_core                        false
% 2.08/0.99  --soft_assumptions                      false
% 2.08/0.99  --soft_lemma_size                       3
% 2.08/0.99  --prop_impl_unit_size                   0
% 2.08/0.99  --prop_impl_unit                        []
% 2.08/0.99  --share_sel_clauses                     true
% 2.08/0.99  --reset_solvers                         false
% 2.08/0.99  --bc_imp_inh                            [conj_cone]
% 2.08/0.99  --conj_cone_tolerance                   3.
% 2.08/0.99  --extra_neg_conj                        none
% 2.08/0.99  --large_theory_mode                     true
% 2.08/0.99  --prolific_symb_bound                   200
% 2.08/0.99  --lt_threshold                          2000
% 2.08/0.99  --clause_weak_htbl                      true
% 2.08/0.99  --gc_record_bc_elim                     false
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing Options
% 2.08/0.99  
% 2.08/0.99  --preprocessing_flag                    true
% 2.08/0.99  --time_out_prep_mult                    0.1
% 2.08/0.99  --splitting_mode                        input
% 2.08/0.99  --splitting_grd                         true
% 2.08/0.99  --splitting_cvd                         false
% 2.08/0.99  --splitting_cvd_svl                     false
% 2.08/0.99  --splitting_nvd                         32
% 2.08/0.99  --sub_typing                            true
% 2.08/0.99  --prep_gs_sim                           true
% 2.08/0.99  --prep_unflatten                        true
% 2.08/0.99  --prep_res_sim                          true
% 2.08/0.99  --prep_upred                            true
% 2.08/0.99  --prep_sem_filter                       exhaustive
% 2.08/0.99  --prep_sem_filter_out                   false
% 2.08/0.99  --pred_elim                             true
% 2.08/0.99  --res_sim_input                         true
% 2.08/0.99  --eq_ax_congr_red                       true
% 2.08/0.99  --pure_diseq_elim                       true
% 2.08/0.99  --brand_transform                       false
% 2.08/0.99  --non_eq_to_eq                          false
% 2.08/0.99  --prep_def_merge                        true
% 2.08/0.99  --prep_def_merge_prop_impl              false
% 2.08/0.99  --prep_def_merge_mbd                    true
% 2.08/0.99  --prep_def_merge_tr_red                 false
% 2.08/0.99  --prep_def_merge_tr_cl                  false
% 2.08/0.99  --smt_preprocessing                     true
% 2.08/0.99  --smt_ac_axioms                         fast
% 2.08/0.99  --preprocessed_out                      false
% 2.08/0.99  --preprocessed_stats                    false
% 2.08/0.99  
% 2.08/0.99  ------ Abstraction refinement Options
% 2.08/0.99  
% 2.08/0.99  --abstr_ref                             []
% 2.08/0.99  --abstr_ref_prep                        false
% 2.08/0.99  --abstr_ref_until_sat                   false
% 2.08/0.99  --abstr_ref_sig_restrict                funpre
% 2.08/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.99  --abstr_ref_under                       []
% 2.08/0.99  
% 2.08/0.99  ------ SAT Options
% 2.08/0.99  
% 2.08/0.99  --sat_mode                              false
% 2.08/0.99  --sat_fm_restart_options                ""
% 2.08/0.99  --sat_gr_def                            false
% 2.08/0.99  --sat_epr_types                         true
% 2.08/0.99  --sat_non_cyclic_types                  false
% 2.08/0.99  --sat_finite_models                     false
% 2.08/0.99  --sat_fm_lemmas                         false
% 2.08/0.99  --sat_fm_prep                           false
% 2.08/0.99  --sat_fm_uc_incr                        true
% 2.08/0.99  --sat_out_model                         small
% 2.08/0.99  --sat_out_clauses                       false
% 2.08/0.99  
% 2.08/0.99  ------ QBF Options
% 2.08/0.99  
% 2.08/0.99  --qbf_mode                              false
% 2.08/0.99  --qbf_elim_univ                         false
% 2.08/0.99  --qbf_dom_inst                          none
% 2.08/0.99  --qbf_dom_pre_inst                      false
% 2.08/0.99  --qbf_sk_in                             false
% 2.08/0.99  --qbf_pred_elim                         true
% 2.08/0.99  --qbf_split                             512
% 2.08/0.99  
% 2.08/0.99  ------ BMC1 Options
% 2.08/0.99  
% 2.08/0.99  --bmc1_incremental                      false
% 2.08/0.99  --bmc1_axioms                           reachable_all
% 2.08/0.99  --bmc1_min_bound                        0
% 2.08/0.99  --bmc1_max_bound                        -1
% 2.08/0.99  --bmc1_max_bound_default                -1
% 2.08/0.99  --bmc1_symbol_reachability              true
% 2.08/0.99  --bmc1_property_lemmas                  false
% 2.08/0.99  --bmc1_k_induction                      false
% 2.08/0.99  --bmc1_non_equiv_states                 false
% 2.08/0.99  --bmc1_deadlock                         false
% 2.08/0.99  --bmc1_ucm                              false
% 2.08/0.99  --bmc1_add_unsat_core                   none
% 2.08/0.99  --bmc1_unsat_core_children              false
% 2.08/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.99  --bmc1_out_stat                         full
% 2.08/0.99  --bmc1_ground_init                      false
% 2.08/0.99  --bmc1_pre_inst_next_state              false
% 2.08/0.99  --bmc1_pre_inst_state                   false
% 2.08/0.99  --bmc1_pre_inst_reach_state             false
% 2.08/0.99  --bmc1_out_unsat_core                   false
% 2.08/0.99  --bmc1_aig_witness_out                  false
% 2.08/0.99  --bmc1_verbose                          false
% 2.08/0.99  --bmc1_dump_clauses_tptp                false
% 2.08/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.99  --bmc1_dump_file                        -
% 2.08/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.99  --bmc1_ucm_extend_mode                  1
% 2.08/0.99  --bmc1_ucm_init_mode                    2
% 2.08/0.99  --bmc1_ucm_cone_mode                    none
% 2.08/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.99  --bmc1_ucm_relax_model                  4
% 2.08/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.99  --bmc1_ucm_layered_model                none
% 2.08/0.99  --bmc1_ucm_max_lemma_size               10
% 2.08/0.99  
% 2.08/0.99  ------ AIG Options
% 2.08/0.99  
% 2.08/0.99  --aig_mode                              false
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation Options
% 2.08/0.99  
% 2.08/0.99  --instantiation_flag                    true
% 2.08/0.99  --inst_sos_flag                         false
% 2.08/0.99  --inst_sos_phase                        true
% 2.08/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.99  --inst_lit_sel_side                     none
% 2.08/0.99  --inst_solver_per_active                1400
% 2.08/0.99  --inst_solver_calls_frac                1.
% 2.08/0.99  --inst_passive_queue_type               priority_queues
% 2.08/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.99  --inst_passive_queues_freq              [25;2]
% 2.08/0.99  --inst_dismatching                      true
% 2.08/0.99  --inst_eager_unprocessed_to_passive     true
% 2.08/0.99  --inst_prop_sim_given                   true
% 2.08/0.99  --inst_prop_sim_new                     false
% 2.08/0.99  --inst_subs_new                         false
% 2.08/0.99  --inst_eq_res_simp                      false
% 2.08/0.99  --inst_subs_given                       false
% 2.08/0.99  --inst_orphan_elimination               true
% 2.08/0.99  --inst_learning_loop_flag               true
% 2.08/0.99  --inst_learning_start                   3000
% 2.08/0.99  --inst_learning_factor                  2
% 2.08/0.99  --inst_start_prop_sim_after_learn       3
% 2.08/0.99  --inst_sel_renew                        solver
% 2.08/0.99  --inst_lit_activity_flag                true
% 2.08/0.99  --inst_restr_to_given                   false
% 2.08/0.99  --inst_activity_threshold               500
% 2.08/0.99  --inst_out_proof                        true
% 2.08/0.99  
% 2.08/0.99  ------ Resolution Options
% 2.08/0.99  
% 2.08/0.99  --resolution_flag                       false
% 2.08/0.99  --res_lit_sel                           adaptive
% 2.08/0.99  --res_lit_sel_side                      none
% 2.08/0.99  --res_ordering                          kbo
% 2.08/0.99  --res_to_prop_solver                    active
% 2.08/0.99  --res_prop_simpl_new                    false
% 2.08/0.99  --res_prop_simpl_given                  true
% 2.08/0.99  --res_passive_queue_type                priority_queues
% 2.08/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.99  --res_passive_queues_freq               [15;5]
% 2.08/0.99  --res_forward_subs                      full
% 2.08/0.99  --res_backward_subs                     full
% 2.08/0.99  --res_forward_subs_resolution           true
% 2.08/0.99  --res_backward_subs_resolution          true
% 2.08/0.99  --res_orphan_elimination                true
% 2.08/0.99  --res_time_limit                        2.
% 2.08/0.99  --res_out_proof                         true
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Options
% 2.08/0.99  
% 2.08/0.99  --superposition_flag                    true
% 2.08/0.99  --sup_passive_queue_type                priority_queues
% 2.08/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.99  --demod_completeness_check              fast
% 2.08/0.99  --demod_use_ground                      true
% 2.08/0.99  --sup_to_prop_solver                    passive
% 2.08/0.99  --sup_prop_simpl_new                    true
% 2.08/0.99  --sup_prop_simpl_given                  true
% 2.08/0.99  --sup_fun_splitting                     false
% 2.08/0.99  --sup_smt_interval                      50000
% 2.08/0.99  
% 2.08/0.99  ------ Superposition Simplification Setup
% 2.08/0.99  
% 2.08/0.99  --sup_indices_passive                   []
% 2.08/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_full_bw                           [BwDemod]
% 2.08/0.99  --sup_immed_triv                        [TrivRules]
% 2.08/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_immed_bw_main                     []
% 2.08/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.99  
% 2.08/0.99  ------ Combination Options
% 2.08/0.99  
% 2.08/0.99  --comb_res_mult                         3
% 2.08/0.99  --comb_sup_mult                         2
% 2.08/0.99  --comb_inst_mult                        10
% 2.08/0.99  
% 2.08/0.99  ------ Debug Options
% 2.08/0.99  
% 2.08/0.99  --dbg_backtrace                         false
% 2.08/0.99  --dbg_dump_prop_clauses                 false
% 2.08/0.99  --dbg_dump_prop_clauses_file            -
% 2.08/0.99  --dbg_out_stat                          false
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  ------ Proving...
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  % SZS status Theorem for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99   Resolution empty clause
% 2.08/0.99  
% 2.08/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  fof(f94,plain,(
% 2.08/0.99    m1_subset_1(sK6,u1_struct_0(sK4))),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f19,conjecture,(
% 2.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f20,negated_conjecture,(
% 2.08/0.99    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.08/0.99    inference(negated_conjecture,[],[f19])).
% 2.08/0.99  
% 2.08/0.99  fof(f36,plain,(
% 2.08/0.99    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f20])).
% 2.08/0.99  
% 2.08/0.99  fof(f37,plain,(
% 2.08/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f36])).
% 2.08/0.99  
% 2.08/0.99  fof(f55,plain,(
% 2.08/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK7)) & sK7 = X3 & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f54,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK6 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f53,plain,(
% 2.08/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK5,X0,X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK5,X0,X1) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f52,plain,(
% 2.08/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k6_domain_1(u1_struct_0(sK4),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK4))) & v3_borsuk_1(X2,X0,sK4) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v5_pre_topc(X2,X0,sK4) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & m1_pre_topc(sK4,X0) & v4_tex_2(sK4,X0) & ~v2_struct_0(sK4))) )),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f51,plain,(
% 2.08/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK3,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v5_pre_topc(X2,sK3,X1) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & v4_tex_2(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f56,plain,(
% 2.08/0.99    ((((k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & v3_borsuk_1(sK5,sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v5_pre_topc(sK5,sK3,sK4) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & v4_tex_2(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f37,f55,f54,f53,f52,f51])).
% 2.08/0.99  
% 2.08/0.99  fof(f96,plain,(
% 2.08/0.99    sK6 = sK7),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f107,plain,(
% 2.08/0.99    m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.08/0.99    inference(definition_unfolding,[],[f94,f96])).
% 2.08/0.99  
% 2.08/0.99  fof(f13,axiom,(
% 2.08/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f25,plain,(
% 2.08/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f13])).
% 2.08/0.99  
% 2.08/0.99  fof(f26,plain,(
% 2.08/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.08/0.99    inference(flattening,[],[f25])).
% 2.08/0.99  
% 2.08/0.99  fof(f73,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f26])).
% 2.08/0.99  
% 2.08/0.99  fof(f3,axiom,(
% 2.08/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f62,plain,(
% 2.08/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f3])).
% 2.08/0.99  
% 2.08/0.99  fof(f4,axiom,(
% 2.08/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f63,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f4])).
% 2.08/0.99  
% 2.08/0.99  fof(f5,axiom,(
% 2.08/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f64,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f5])).
% 2.08/0.99  
% 2.08/0.99  fof(f6,axiom,(
% 2.08/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f65,plain,(
% 2.08/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f6])).
% 2.08/0.99  
% 2.08/0.99  fof(f7,axiom,(
% 2.08/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f66,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f7])).
% 2.08/0.99  
% 2.08/0.99  fof(f8,axiom,(
% 2.08/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f67,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f8])).
% 2.08/0.99  
% 2.08/0.99  fof(f9,axiom,(
% 2.08/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f68,plain,(
% 2.08/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f9])).
% 2.08/0.99  
% 2.08/0.99  fof(f98,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f67,f68])).
% 2.08/0.99  
% 2.08/0.99  fof(f99,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f66,f98])).
% 2.08/0.99  
% 2.08/0.99  fof(f100,plain,(
% 2.08/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f65,f99])).
% 2.08/0.99  
% 2.08/0.99  fof(f101,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f64,f100])).
% 2.08/0.99  
% 2.08/0.99  fof(f102,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f63,f101])).
% 2.08/0.99  
% 2.08/0.99  fof(f103,plain,(
% 2.08/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f62,f102])).
% 2.08/0.99  
% 2.08/0.99  fof(f104,plain,(
% 2.08/0.99    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f73,f103])).
% 2.08/0.99  
% 2.08/0.99  fof(f85,plain,(
% 2.08/0.99    l1_pre_topc(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f15,axiom,(
% 2.08/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f29,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/0.99    inference(ennf_transformation,[],[f15])).
% 2.08/0.99  
% 2.08/0.99  fof(f75,plain,(
% 2.08/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f29])).
% 2.08/0.99  
% 2.08/0.99  fof(f88,plain,(
% 2.08/0.99    m1_pre_topc(sK4,sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f17,axiom,(
% 2.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f32,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f17])).
% 2.08/0.99  
% 2.08/0.99  fof(f33,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f32])).
% 2.08/0.99  
% 2.08/0.99  fof(f80,plain,(
% 2.08/0.99    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f33])).
% 2.08/0.99  
% 2.08/0.99  fof(f83,plain,(
% 2.08/0.99    v2_pre_topc(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f82,plain,(
% 2.08/0.99    ~v2_struct_0(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f16,axiom,(
% 2.08/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f30,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f16])).
% 2.08/0.99  
% 2.08/0.99  fof(f31,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f30])).
% 2.08/0.99  
% 2.08/0.99  fof(f47,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(nnf_transformation,[],[f31])).
% 2.08/0.99  
% 2.08/0.99  fof(f48,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(rectify,[],[f47])).
% 2.08/0.99  
% 2.08/0.99  fof(f49,plain,(
% 2.08/0.99    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f50,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 2.08/0.99  
% 2.08/0.99  fof(f76,plain,(
% 2.08/0.99    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f50])).
% 2.08/0.99  
% 2.08/0.99  fof(f108,plain,(
% 2.08/0.99    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(equality_resolution,[],[f76])).
% 2.08/0.99  
% 2.08/0.99  fof(f87,plain,(
% 2.08/0.99    v4_tex_2(sK4,sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f95,plain,(
% 2.08/0.99    m1_subset_1(sK7,u1_struct_0(sK3))),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f1,axiom,(
% 2.08/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f38,plain,(
% 2.08/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.99    inference(nnf_transformation,[],[f1])).
% 2.08/0.99  
% 2.08/0.99  fof(f39,plain,(
% 2.08/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.99    inference(rectify,[],[f38])).
% 2.08/0.99  
% 2.08/0.99  fof(f40,plain,(
% 2.08/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f41,plain,(
% 2.08/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.08/0.99  
% 2.08/0.99  fof(f58,plain,(
% 2.08/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f41])).
% 2.08/0.99  
% 2.08/0.99  fof(f10,axiom,(
% 2.08/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f46,plain,(
% 2.08/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.08/0.99    inference(nnf_transformation,[],[f10])).
% 2.08/0.99  
% 2.08/0.99  fof(f69,plain,(
% 2.08/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.08/0.99    inference(cnf_transformation,[],[f46])).
% 2.08/0.99  
% 2.08/0.99  fof(f2,axiom,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f21,plain,(
% 2.08/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f2])).
% 2.08/0.99  
% 2.08/0.99  fof(f42,plain,(
% 2.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.99    inference(nnf_transformation,[],[f21])).
% 2.08/0.99  
% 2.08/0.99  fof(f43,plain,(
% 2.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.99    inference(rectify,[],[f42])).
% 2.08/0.99  
% 2.08/0.99  fof(f44,plain,(
% 2.08/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.08/0.99    introduced(choice_axiom,[])).
% 2.08/0.99  
% 2.08/0.99  fof(f45,plain,(
% 2.08/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.08/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f43,f44])).
% 2.08/0.99  
% 2.08/0.99  fof(f59,plain,(
% 2.08/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f45])).
% 2.08/0.99  
% 2.08/0.99  fof(f57,plain,(
% 2.08/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f41])).
% 2.08/0.99  
% 2.08/0.99  fof(f12,axiom,(
% 2.08/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f23,plain,(
% 2.08/0.99    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f12])).
% 2.08/0.99  
% 2.08/0.99  fof(f24,plain,(
% 2.08/0.99    ! [X0,X1,X2] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.08/0.99    inference(flattening,[],[f23])).
% 2.08/0.99  
% 2.08/0.99  fof(f72,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f24])).
% 2.08/0.99  
% 2.08/0.99  fof(f11,axiom,(
% 2.08/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f22,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.08/0.99    inference(ennf_transformation,[],[f11])).
% 2.08/0.99  
% 2.08/0.99  fof(f71,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f22])).
% 2.08/0.99  
% 2.08/0.99  fof(f18,axiom,(
% 2.08/0.99    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f34,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f18])).
% 2.08/0.99  
% 2.08/0.99  fof(f35,plain,(
% 2.08/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.08/0.99    inference(flattening,[],[f34])).
% 2.08/0.99  
% 2.08/0.99  fof(f81,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f35])).
% 2.08/0.99  
% 2.08/0.99  fof(f109,plain,(
% 2.08/0.99    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.08/0.99    inference(equality_resolution,[],[f81])).
% 2.08/0.99  
% 2.08/0.99  fof(f93,plain,(
% 2.08/0.99    v3_borsuk_1(sK5,sK3,sK4)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f84,plain,(
% 2.08/0.99    v3_tdlat_3(sK3)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f86,plain,(
% 2.08/0.99    ~v2_struct_0(sK4)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f89,plain,(
% 2.08/0.99    v1_funct_1(sK5)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f90,plain,(
% 2.08/0.99    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f91,plain,(
% 2.08/0.99    v5_pre_topc(sK5,sK3,sK4)),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f92,plain,(
% 2.08/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f14,axiom,(
% 2.08/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,X0) & m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2))),
% 2.08/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.08/0.99  
% 2.08/0.99  fof(f27,plain,(
% 2.08/0.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) | (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.08/0.99    inference(ennf_transformation,[],[f14])).
% 2.08/0.99  
% 2.08/0.99  fof(f28,plain,(
% 2.08/0.99    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.08/0.99    inference(flattening,[],[f27])).
% 2.08/0.99  
% 2.08/0.99  fof(f74,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.99    inference(cnf_transformation,[],[f28])).
% 2.08/0.99  
% 2.08/0.99  fof(f105,plain,(
% 2.08/0.99    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k7_domain_1(X0,X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.08/0.99    inference(definition_unfolding,[],[f74,f102])).
% 2.08/0.99  
% 2.08/0.99  fof(f97,plain,(
% 2.08/0.99    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))),
% 2.08/0.99    inference(cnf_transformation,[],[f56])).
% 2.08/0.99  
% 2.08/0.99  fof(f106,plain,(
% 2.08/0.99    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))),
% 2.08/0.99    inference(definition_unfolding,[],[f97,f96])).
% 2.08/0.99  
% 2.08/0.99  cnf(c_20,negated_conjecture,
% 2.08/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.08/0.99      inference(cnf_transformation,[],[f107]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1154,negated_conjecture,
% 2.08/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1634,plain,
% 2.08/0.99      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_9,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,X1)
% 2.08/0.99      | v1_xboole_0(X1)
% 2.08/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1158,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0_58,X1_58)
% 2.08/0.99      | v1_xboole_0(X1_58)
% 2.08/0.99      | k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58) = k6_domain_1(X1_58,X0_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1631,plain,
% 2.08/0.99      ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58) = k6_domain_1(X1_58,X0_58)
% 2.08/0.99      | m1_subset_1(X0_58,X1_58) != iProver_top
% 2.08/0.99      | v1_xboole_0(X1_58) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1158]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2372,plain,
% 2.08/0.99      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7)
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1634,c_1631]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_29,negated_conjecture,
% 2.08/0.99      ( l1_pre_topc(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_11,plain,
% 2.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.08/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | ~ l1_pre_topc(X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_26,negated_conjecture,
% 2.08/0.99      ( m1_pre_topc(sK4,sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_623,plain,
% 2.08/0.99      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | ~ l1_pre_topc(X1)
% 2.08/0.99      | sK4 != X0
% 2.08/0.99      | sK3 != X1 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_624,plain,
% 2.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ l1_pre_topc(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_623]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_16,plain,
% 2.08/0.99      ( ~ v3_tex_2(X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | ~ v2_pre_topc(X1)
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | ~ l1_pre_topc(X1)
% 2.08/0.99      | ~ v1_xboole_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_31,negated_conjecture,
% 2.08/0.99      ( v2_pre_topc(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_451,plain,
% 2.08/0.99      ( ~ v3_tex_2(X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | ~ l1_pre_topc(X1)
% 2.08/0.99      | ~ v1_xboole_0(X0)
% 2.08/0.99      | sK3 != X1 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_452,plain,
% 2.08/0.99      ( ~ v3_tex_2(X0,sK3)
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | v2_struct_0(sK3)
% 2.08/0.99      | ~ l1_pre_topc(sK3)
% 2.08/0.99      | ~ v1_xboole_0(X0) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_451]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_32,negated_conjecture,
% 2.08/0.99      ( ~ v2_struct_0(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_456,plain,
% 2.08/0.99      ( ~ v3_tex_2(X0,sK3)
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ v1_xboole_0(X0) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_452,c_32,c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_15,plain,
% 2.08/0.99      ( v3_tex_2(u1_struct_0(X0),X1)
% 2.08/0.99      | ~ v4_tex_2(X0,X1)
% 2.08/0.99      | ~ m1_pre_topc(X0,X1)
% 2.08/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | ~ l1_pre_topc(X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f108]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_178,plain,
% 2.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.08/0.99      | ~ v4_tex_2(X0,X1)
% 2.08/0.99      | v3_tex_2(u1_struct_0(X0),X1)
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | ~ l1_pre_topc(X1) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_15,c_11]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_179,plain,
% 2.08/0.99      ( v3_tex_2(u1_struct_0(X0),X1)
% 2.08/0.99      | ~ v4_tex_2(X0,X1)
% 2.08/0.99      | ~ m1_pre_topc(X0,X1)
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | ~ l1_pre_topc(X1) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_178]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_608,plain,
% 2.08/0.99      ( v3_tex_2(u1_struct_0(X0),X1)
% 2.08/0.99      | ~ v4_tex_2(X0,X1)
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | ~ l1_pre_topc(X1)
% 2.08/0.99      | sK4 != X0
% 2.08/0.99      | sK3 != X1 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_179,c_26]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_609,plain,
% 2.08/0.99      ( v3_tex_2(u1_struct_0(sK4),sK3)
% 2.08/0.99      | ~ v4_tex_2(sK4,sK3)
% 2.08/0.99      | v2_struct_0(sK3)
% 2.08/0.99      | ~ l1_pre_topc(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_608]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_27,negated_conjecture,
% 2.08/0.99      ( v4_tex_2(sK4,sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_611,plain,
% 2.08/0.99      ( v3_tex_2(u1_struct_0(sK4),sK3) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_609,c_32,c_29,c_27]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_665,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ v1_xboole_0(X0)
% 2.08/0.99      | u1_struct_0(sK4) != X0
% 2.08/0.99      | sK3 != sK3 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_456,c_611]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_666,plain,
% 2.08/0.99      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_665]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1798,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0_58,u1_struct_0(sK4))
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.08/0.99      | k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58) = k6_domain_1(u1_struct_0(sK4),X0_58) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_1158]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2011,plain,
% 2.08/0.99      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK4))
% 2.08/0.99      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
% 2.08/0.99      inference(instantiation,[status(thm)],[c_1798]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2636,plain,
% 2.08/0.99      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_2372,c_29,c_20,c_624,c_666,c_2011]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_19,negated_conjecture,
% 2.08/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1155,negated_conjecture,
% 2.08/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1633,plain,
% 2.08/0.99      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1155]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2371,plain,
% 2.08/0.99      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7)
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1633,c_1631]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2639,plain,
% 2.08/0.99      ( k6_domain_1(u1_struct_0(sK3),sK7) = k6_domain_1(u1_struct_0(sK4),sK7)
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(demodulation,[status(thm)],[c_2636,c_2371]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_0,plain,
% 2.08/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1166,plain,
% 2.08/0.99      ( r2_hidden(sK0(X0_58),X0_58) | v1_xboole_0(X0_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1623,plain,
% 2.08/0.99      ( r2_hidden(sK0(X0_58),X0_58) = iProver_top
% 2.08/0.99      | v1_xboole_0(X0_58) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1166]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_626,plain,
% 2.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_624,c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1152,plain,
% 2.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_626]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1636,plain,
% 2.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1152]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_6,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1160,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(X1_58)) | r1_tarski(X0_58,X1_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1629,plain,
% 2.08/0.99      ( m1_subset_1(X0_58,k1_zfmisc_1(X1_58)) != iProver_top
% 2.08/0.99      | r1_tarski(X0_58,X1_58) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1160]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2046,plain,
% 2.08/0.99      ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1636,c_1629]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_4,plain,
% 2.08/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1162,plain,
% 2.08/0.99      ( ~ r1_tarski(X0_58,X1_58)
% 2.08/0.99      | ~ r2_hidden(X0_61,X0_58)
% 2.08/0.99      | r2_hidden(X0_61,X1_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1627,plain,
% 2.08/0.99      ( r1_tarski(X0_58,X1_58) != iProver_top
% 2.08/0.99      | r2_hidden(X0_61,X0_58) != iProver_top
% 2.08/0.99      | r2_hidden(X0_61,X1_58) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1162]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2348,plain,
% 2.08/0.99      ( r2_hidden(X0_61,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | r2_hidden(X0_61,u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_2046,c_1627]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2998,plain,
% 2.08/0.99      ( r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1623,c_2348]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_36,plain,
% 2.08/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_625,plain,
% 2.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.08/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_667,plain,
% 2.08/0.99      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3090,plain,
% 2.08/0.99      ( r2_hidden(sK0(u1_struct_0(sK4)),u1_struct_0(sK3)) = iProver_top ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_2998,c_36,c_625,c_667]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1,plain,
% 2.08/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1165,plain,
% 2.08/0.99      ( ~ r2_hidden(X0_61,X0_58) | ~ v1_xboole_0(X0_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1624,plain,
% 2.08/0.99      ( r2_hidden(X0_61,X0_58) != iProver_top
% 2.08/0.99      | v1_xboole_0(X0_58) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3095,plain,
% 2.08/0.99      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_3090,c_1624]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3278,plain,
% 2.08/0.99      ( k6_domain_1(u1_struct_0(sK3),sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2639,c_3095]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_8,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X2,X1)
% 2.08/0.99      | m1_subset_1(k7_domain_1(X1,X2,X0),k1_zfmisc_1(X1))
% 2.08/0.99      | v1_xboole_0(X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1159,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0_58,X1_58)
% 2.08/0.99      | ~ m1_subset_1(X2_58,X1_58)
% 2.08/0.99      | m1_subset_1(k7_domain_1(X1_58,X2_58,X0_58),k1_zfmisc_1(X1_58))
% 2.08/0.99      | v1_xboole_0(X1_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1630,plain,
% 2.08/0.99      ( m1_subset_1(X0_58,X1_58) != iProver_top
% 2.08/0.99      | m1_subset_1(X2_58,X1_58) != iProver_top
% 2.08/0.99      | m1_subset_1(k7_domain_1(X1_58,X2_58,X0_58),k1_zfmisc_1(X1_58)) = iProver_top
% 2.08/0.99      | v1_xboole_0(X1_58) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1159]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_7,plain,
% 2.08/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.08/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | ~ l1_pre_topc(X1) ),
% 2.08/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_634,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/0.99      | ~ l1_pre_topc(X2)
% 2.08/0.99      | sK4 != X1
% 2.08/0.99      | sK3 != X2 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_635,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.08/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ l1_pre_topc(sK3) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_634]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_639,plain,
% 2.08/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.08/0.99      inference(global_propositional_subsumption,[status(thm)],[c_635,c_29]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_640,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.08/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_639]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_17,plain,
% 2.08/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.08/0.99      | ~ v5_pre_topc(X0,X1,X2)
% 2.08/0.99      | ~ v3_borsuk_1(X0,X1,X2)
% 2.08/0.99      | ~ v4_tex_2(X2,X1)
% 2.08/0.99      | ~ m1_pre_topc(X2,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.08/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/0.99      | ~ v3_tdlat_3(X1)
% 2.08/0.99      | ~ v1_funct_1(X0)
% 2.08/0.99      | ~ v2_pre_topc(X1)
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | v2_struct_0(X2)
% 2.08/0.99      | ~ l1_pre_topc(X1)
% 2.08/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f109]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_21,negated_conjecture,
% 2.08/0.99      ( v3_borsuk_1(sK5,sK3,sK4) ),
% 2.08/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_426,plain,
% 2.08/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.08/0.99      | ~ v5_pre_topc(X0,X1,X2)
% 2.08/0.99      | ~ v4_tex_2(X2,X1)
% 2.08/0.99      | ~ m1_pre_topc(X2,X1)
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.08/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.08/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.08/0.99      | ~ v3_tdlat_3(X1)
% 2.08/0.99      | ~ v1_funct_1(X0)
% 2.08/0.99      | ~ v2_pre_topc(X1)
% 2.08/0.99      | v2_struct_0(X1)
% 2.08/0.99      | v2_struct_0(X2)
% 2.08/0.99      | ~ l1_pre_topc(X1)
% 2.08/0.99      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 2.08/0.99      | sK5 != X0
% 2.08/0.99      | sK4 != X2
% 2.08/0.99      | sK3 != X1 ),
% 2.08/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_427,plain,
% 2.08/0.99      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 2.08/0.99      | ~ v5_pre_topc(sK5,sK3,sK4)
% 2.08/0.99      | ~ v4_tex_2(sK4,sK3)
% 2.08/0.99      | ~ m1_pre_topc(sK4,sK3)
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 2.08/0.99      | ~ v3_tdlat_3(sK3)
% 2.08/0.99      | ~ v1_funct_1(sK5)
% 2.08/0.99      | ~ v2_pre_topc(sK3)
% 2.08/0.99      | v2_struct_0(sK4)
% 2.08/0.99      | v2_struct_0(sK3)
% 2.08/0.99      | ~ l1_pre_topc(sK3)
% 2.08/0.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 2.08/0.99      inference(unflattening,[status(thm)],[c_426]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_30,negated_conjecture,
% 2.08/0.99      ( v3_tdlat_3(sK3) ),
% 2.08/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_28,negated_conjecture,
% 2.08/0.99      ( ~ v2_struct_0(sK4) ),
% 2.08/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_25,negated_conjecture,
% 2.08/0.99      ( v1_funct_1(sK5) ),
% 2.08/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_24,negated_conjecture,
% 2.08/0.99      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 2.08/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_23,negated_conjecture,
% 2.08/0.99      ( v5_pre_topc(sK5,sK3,sK4) ),
% 2.08/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_22,negated_conjecture,
% 2.08/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 2.08/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_431,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.08/0.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_427,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_432,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.08/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.08/0.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_431]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_660,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.08/0.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 2.08/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_640,c_432]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1150,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.08/0.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_58) = k2_pre_topc(sK3,X0_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_660]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1638,plain,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_58) = k2_pre_topc(sK3,X0_58)
% 2.08/0.99      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1150]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2249,plain,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58))
% 2.08/0.99      | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1630,c_1638]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2905,plain,
% 2.08/0.99      ( m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_2249,c_36,c_625,c_667]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2906,plain,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),X0_58,X1_58))
% 2.08/0.99      | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | m1_subset_1(X1_58,u1_struct_0(sK4)) != iProver_top ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_2905]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2914,plain,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),sK7,X0_58)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),sK7,X0_58))
% 2.08/0.99      | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1634,c_2906]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3147,plain,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k7_domain_1(u1_struct_0(sK4),sK7,sK7)) = k2_pre_topc(sK3,k7_domain_1(u1_struct_0(sK4),sK7,sK7)) ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1634,c_2914]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_10,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0,X1)
% 2.08/0.99      | ~ m1_subset_1(X2,X1)
% 2.08/0.99      | v1_xboole_0(X1)
% 2.08/0.99      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0) = k7_domain_1(X1,X2,X0) ),
% 2.08/0.99      inference(cnf_transformation,[],[f105]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1157,plain,
% 2.08/0.99      ( ~ m1_subset_1(X0_58,X1_58)
% 2.08/0.99      | ~ m1_subset_1(X2_58,X1_58)
% 2.08/0.99      | v1_xboole_0(X1_58)
% 2.08/0.99      | k6_enumset1(X2_58,X2_58,X2_58,X2_58,X2_58,X2_58,X2_58,X0_58) = k7_domain_1(X1_58,X2_58,X0_58) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1632,plain,
% 2.08/0.99      ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X1_58) = k7_domain_1(X2_58,X0_58,X1_58)
% 2.08/0.99      | m1_subset_1(X1_58,X2_58) != iProver_top
% 2.08/0.99      | m1_subset_1(X0_58,X2_58) != iProver_top
% 2.08/0.99      | v1_xboole_0(X2_58) = iProver_top ),
% 2.08/0.99      inference(predicate_to_equality,[status(thm)],[c_1157]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2491,plain,
% 2.08/0.99      ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,sK7) = k7_domain_1(u1_struct_0(sK4),X0_58,sK7)
% 2.08/0.99      | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1634,c_1632]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2763,plain,
% 2.08/0.99      ( m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top
% 2.08/0.99      | k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,sK7) = k7_domain_1(u1_struct_0(sK4),X0_58,sK7) ),
% 2.08/0.99      inference(global_propositional_subsumption,
% 2.08/0.99                [status(thm)],
% 2.08/0.99                [c_2491,c_36,c_625,c_667]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2764,plain,
% 2.08/0.99      ( k6_enumset1(X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,X0_58,sK7) = k7_domain_1(u1_struct_0(sK4),X0_58,sK7)
% 2.08/0.99      | m1_subset_1(X0_58,u1_struct_0(sK4)) != iProver_top ),
% 2.08/0.99      inference(renaming,[status(thm)],[c_2763]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2771,plain,
% 2.08/0.99      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k7_domain_1(u1_struct_0(sK4),sK7,sK7) ),
% 2.08/0.99      inference(superposition,[status(thm)],[c_1634,c_2764]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_2772,plain,
% 2.08/0.99      ( k7_domain_1(u1_struct_0(sK4),sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
% 2.08/0.99      inference(light_normalisation,[status(thm)],[c_2771,c_2636]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3148,plain,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK4),sK7)) ),
% 2.08/0.99      inference(light_normalisation,[status(thm)],[c_3147,c_2772]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_18,negated_conjecture,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 2.08/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_1156,negated_conjecture,
% 2.08/0.99      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 2.08/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3219,plain,
% 2.08/0.99      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 2.08/0.99      inference(demodulation,[status(thm)],[c_3148,c_1156]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3281,plain,
% 2.08/0.99      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 2.08/0.99      inference(demodulation,[status(thm)],[c_3278,c_3219]) ).
% 2.08/0.99  
% 2.08/0.99  cnf(c_3291,plain,
% 2.08/0.99      ( $false ),
% 2.08/0.99      inference(equality_resolution_simp,[status(thm)],[c_3281]) ).
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/0.99  
% 2.08/0.99  ------                               Statistics
% 2.08/0.99  
% 2.08/0.99  ------ General
% 2.08/0.99  
% 2.08/0.99  abstr_ref_over_cycles:                  0
% 2.08/0.99  abstr_ref_under_cycles:                 0
% 2.08/0.99  gc_basic_clause_elim:                   0
% 2.08/0.99  forced_gc_time:                         0
% 2.08/0.99  parsing_time:                           0.009
% 2.08/0.99  unif_index_cands_time:                  0.
% 2.08/0.99  unif_index_add_time:                    0.
% 2.08/0.99  orderings_time:                         0.
% 2.08/0.99  out_proof_time:                         0.011
% 2.08/0.99  total_time:                             0.088
% 2.08/0.99  num_of_symbols:                         68
% 2.08/0.99  num_of_terms:                           2508
% 2.08/0.99  
% 2.08/0.99  ------ Preprocessing
% 2.08/0.99  
% 2.08/0.99  num_of_splits:                          0
% 2.08/0.99  num_of_split_atoms:                     0
% 2.08/0.99  num_of_reused_defs:                     0
% 2.08/0.99  num_eq_ax_congr_red:                    57
% 2.08/0.99  num_of_sem_filtered_clauses:            1
% 2.08/0.99  num_of_subtypes:                        4
% 2.08/0.99  monotx_restored_types:                  0
% 2.08/0.99  sat_num_of_epr_types:                   0
% 2.08/0.99  sat_num_of_non_cyclic_types:            0
% 2.08/0.99  sat_guarded_non_collapsed_types:        0
% 2.08/0.99  num_pure_diseq_elim:                    0
% 2.08/0.99  simp_replaced_by:                       0
% 2.08/0.99  res_preprocessed:                       114
% 2.08/0.99  prep_upred:                             0
% 2.08/0.99  prep_unflattend:                        30
% 2.08/0.99  smt_new_axioms:                         0
% 2.08/0.99  pred_elim_cands:                        4
% 2.08/0.99  pred_elim:                              11
% 2.08/0.99  pred_elim_cl:                           15
% 2.08/0.99  pred_elim_cycles:                       16
% 2.08/0.99  merged_defs:                            8
% 2.08/0.99  merged_defs_ncl:                        0
% 2.08/0.99  bin_hyper_res:                          8
% 2.08/0.99  prep_cycles:                            4
% 2.08/0.99  pred_elim_time:                         0.006
% 2.08/0.99  splitting_time:                         0.
% 2.08/0.99  sem_filter_time:                        0.
% 2.08/0.99  monotx_time:                            0.
% 2.08/0.99  subtype_inf_time:                       0.
% 2.08/0.99  
% 2.08/0.99  ------ Problem properties
% 2.08/0.99  
% 2.08/0.99  clauses:                                18
% 2.08/0.99  conjectures:                            4
% 2.08/0.99  epr:                                    2
% 2.08/0.99  horn:                                   13
% 2.08/0.99  ground:                                 6
% 2.08/0.99  unary:                                  6
% 2.08/0.99  binary:                                 8
% 2.08/0.99  lits:                                   36
% 2.08/0.99  lits_eq:                                4
% 2.08/0.99  fd_pure:                                0
% 2.08/0.99  fd_pseudo:                              0
% 2.08/0.99  fd_cond:                                0
% 2.08/0.99  fd_pseudo_cond:                         0
% 2.08/0.99  ac_symbols:                             0
% 2.08/0.99  
% 2.08/0.99  ------ Propositional Solver
% 2.08/0.99  
% 2.08/0.99  prop_solver_calls:                      29
% 2.08/0.99  prop_fast_solver_calls:                 758
% 2.08/0.99  smt_solver_calls:                       0
% 2.08/0.99  smt_fast_solver_calls:                  0
% 2.08/0.99  prop_num_of_clauses:                    882
% 2.08/0.99  prop_preprocess_simplified:             3665
% 2.08/0.99  prop_fo_subsumed:                       27
% 2.08/0.99  prop_solver_time:                       0.
% 2.08/0.99  smt_solver_time:                        0.
% 2.08/0.99  smt_fast_solver_time:                   0.
% 2.08/0.99  prop_fast_solver_time:                  0.
% 2.08/0.99  prop_unsat_core_time:                   0.
% 2.08/0.99  
% 2.08/0.99  ------ QBF
% 2.08/0.99  
% 2.08/0.99  qbf_q_res:                              0
% 2.08/0.99  qbf_num_tautologies:                    0
% 2.08/0.99  qbf_prep_cycles:                        0
% 2.08/0.99  
% 2.08/0.99  ------ BMC1
% 2.08/0.99  
% 2.08/0.99  bmc1_current_bound:                     -1
% 2.08/0.99  bmc1_last_solved_bound:                 -1
% 2.08/0.99  bmc1_unsat_core_size:                   -1
% 2.08/0.99  bmc1_unsat_core_parents_size:           -1
% 2.08/0.99  bmc1_merge_next_fun:                    0
% 2.08/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.08/0.99  
% 2.08/0.99  ------ Instantiation
% 2.08/0.99  
% 2.08/0.99  inst_num_of_clauses:                    229
% 2.08/0.99  inst_num_in_passive:                    20
% 2.08/0.99  inst_num_in_active:                     183
% 2.08/0.99  inst_num_in_unprocessed:                26
% 2.08/0.99  inst_num_of_loops:                      220
% 2.08/0.99  inst_num_of_learning_restarts:          0
% 2.08/0.99  inst_num_moves_active_passive:          32
% 2.08/0.99  inst_lit_activity:                      0
% 2.08/0.99  inst_lit_activity_moves:                0
% 2.08/0.99  inst_num_tautologies:                   0
% 2.08/0.99  inst_num_prop_implied:                  0
% 2.08/0.99  inst_num_existing_simplified:           0
% 2.08/0.99  inst_num_eq_res_simplified:             0
% 2.08/0.99  inst_num_child_elim:                    0
% 2.08/0.99  inst_num_of_dismatching_blockings:      72
% 2.08/0.99  inst_num_of_non_proper_insts:           309
% 2.08/0.99  inst_num_of_duplicates:                 0
% 2.08/0.99  inst_inst_num_from_inst_to_res:         0
% 2.08/0.99  inst_dismatching_checking_time:         0.
% 2.08/0.99  
% 2.08/0.99  ------ Resolution
% 2.08/0.99  
% 2.08/0.99  res_num_of_clauses:                     0
% 2.08/0.99  res_num_in_passive:                     0
% 2.08/0.99  res_num_in_active:                      0
% 2.08/0.99  res_num_of_loops:                       118
% 2.08/0.99  res_forward_subset_subsumed:            64
% 2.08/0.99  res_backward_subset_subsumed:           2
% 2.08/0.99  res_forward_subsumed:                   0
% 2.08/0.99  res_backward_subsumed:                  0
% 2.08/0.99  res_forward_subsumption_resolution:     0
% 2.08/0.99  res_backward_subsumption_resolution:    1
% 2.08/0.99  res_clause_to_clause_subsumption:       129
% 2.08/0.99  res_orphan_elimination:                 0
% 2.08/0.99  res_tautology_del:                      71
% 2.08/0.99  res_num_eq_res_simplified:              0
% 2.08/0.99  res_num_sel_changes:                    0
% 2.08/0.99  res_moves_from_active_to_pass:          0
% 2.08/0.99  
% 2.08/0.99  ------ Superposition
% 2.08/0.99  
% 2.08/0.99  sup_time_total:                         0.
% 2.08/0.99  sup_time_generating:                    0.
% 2.08/0.99  sup_time_sim_full:                      0.
% 2.08/0.99  sup_time_sim_immed:                     0.
% 2.08/0.99  
% 2.08/0.99  sup_num_of_clauses:                     59
% 2.08/0.99  sup_num_in_active:                      36
% 2.08/0.99  sup_num_in_passive:                     23
% 2.08/0.99  sup_num_of_loops:                       42
% 2.08/0.99  sup_fw_superposition:                   31
% 2.08/0.99  sup_bw_superposition:                   19
% 2.08/0.99  sup_immediate_simplified:               5
% 2.08/0.99  sup_given_eliminated:                   0
% 2.08/0.99  comparisons_done:                       0
% 2.08/0.99  comparisons_avoided:                    0
% 2.08/0.99  
% 2.08/0.99  ------ Simplifications
% 2.08/0.99  
% 2.08/0.99  
% 2.08/0.99  sim_fw_subset_subsumed:                 0
% 2.08/0.99  sim_bw_subset_subsumed:                 0
% 2.08/0.99  sim_fw_subsumed:                        2
% 2.08/0.99  sim_bw_subsumed:                        0
% 2.08/0.99  sim_fw_subsumption_res:                 0
% 2.08/0.99  sim_bw_subsumption_res:                 0
% 2.08/0.99  sim_tautology_del:                      3
% 2.08/0.99  sim_eq_tautology_del:                   0
% 2.08/0.99  sim_eq_res_simp:                        0
% 2.08/0.99  sim_fw_demodulated:                     0
% 2.08/0.99  sim_bw_demodulated:                     6
% 2.08/0.99  sim_light_normalised:                   3
% 2.08/0.99  sim_joinable_taut:                      0
% 2.08/0.99  sim_joinable_simp:                      0
% 2.08/0.99  sim_ac_normalised:                      0
% 2.08/0.99  sim_smt_subsumption:                    0
% 2.08/0.99  
%------------------------------------------------------------------------------
