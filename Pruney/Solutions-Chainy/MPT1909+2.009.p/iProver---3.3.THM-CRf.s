%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:55 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  248 (1357 expanded)
%              Number of clauses        :  152 ( 316 expanded)
%              Number of leaves         :   30 ( 515 expanded)
%              Depth                    :   21
%              Number of atoms          :  835 (13598 expanded)
%              Number of equality atoms :  237 (2469 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))
        & sK5 = X3
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f37,f47,f46,f45,f44,f43])).

fof(f84,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(definition_unfolding,[],[f82,f84])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(definition_unfolding,[],[f85,f84])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f86])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f88])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f89])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f90])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f66,f91])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f91])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(cnf_transformation,[],[f35])).

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
    v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_975,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1438,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_975])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_437,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_438,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_440,plain,
    ( v2_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_27,c_25])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_440])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_426,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_427,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_25,c_24,c_427])).

cnf(c_967,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK2))
    | m1_subset_1(k1_connsp_2(sK2,X0_55),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subtyping,[status(esa)],[c_518])).

cnf(c_1446,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK2,X0_55),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_967])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_979,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1435,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_979])).

cnf(c_1962,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_connsp_2(sK2,X0_55),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_1435])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_440])).

cnf(c_496,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_25,c_24,c_427])).

cnf(c_968,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK2))
    | r2_hidden(X0_55,k1_connsp_2(sK2,X0_55)) ),
    inference(subtyping,[status(esa)],[c_500])).

cnf(c_1445,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_55,k1_connsp_2(sK2,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_968])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_982,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | r2_hidden(X0_55,X2_55)
    | ~ r1_tarski(X1_55,X2_55) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1432,plain,
    ( r2_hidden(X0_55,X1_55) != iProver_top
    | r2_hidden(X0_55,X2_55) = iProver_top
    | r1_tarski(X1_55,X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_2255,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_55,X1_55) = iProver_top
    | r1_tarski(k1_connsp_2(sK2,X0_55),X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1432])).

cnf(c_3369,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0_55,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_2255])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_986,plain,
    ( X0_55 = X0_55 ),
    theory(equality)).

cnf(c_1005,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_14,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_977,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k1_connsp_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_subset_1(k1_connsp_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_28,c_25])).

cnf(c_969,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
    | m1_subset_1(k1_connsp_2(sK1,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_482])).

cnf(c_1553,plain,
    ( m1_subset_1(k1_connsp_2(sK1,sK5),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_connsp_2(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_connsp_2(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_28,c_25])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
    | r2_hidden(X0_55,k1_connsp_2(sK1,X0_55)) ),
    inference(subtyping,[status(esa)],[c_464])).

cnf(c_1556,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | r2_hidden(sK5,k1_connsp_2(sK1,sK5)) ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_1559,plain,
    ( m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1560,plain,
    ( m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1559])).

cnf(c_1562,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK5,k1_connsp_2(sK2,sK5)) ),
    inference(instantiation,[status(thm)],[c_968])).

cnf(c_1563,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,k1_connsp_2(sK2,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_978,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | v1_xboole_0(X1_55)
    | k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1599,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_1602,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_1603,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5)
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_995,plain,
    ( k2_pre_topc(X0_56,X0_55) = k2_pre_topc(X0_56,X1_55)
    | X0_55 != X1_55 ),
    theory(equality)).

cnf(c_1673,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,X0_55)
    | k6_domain_1(u1_struct_0(sK1),sK5) != X0_55 ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_1788,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | k6_domain_1(u1_struct_0(sK1),sK5) != k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_1789,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_989,plain,
    ( X0_57 != X1_57
    | X2_57 != X1_57
    | X2_57 = X0_57 ),
    theory(equality)).

cnf(c_1671,plain,
    ( X0_57 != X1_57
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != X1_57
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = X0_57 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_1855,plain,
    ( X0_57 != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = X0_57
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_1946,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(instantiation,[status(thm)],[c_1855])).

cnf(c_1573,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != X0_57
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != X0_57 ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_2045,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(instantiation,[status(thm)],[c_1573])).

cnf(c_1732,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0_55,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_2225,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1732])).

cnf(c_2226,plain,
    ( m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2225])).

cnf(c_1747,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK1,sK5),k1_zfmisc_1(X0_55))
    | r1_tarski(k1_connsp_2(sK1,sK5),X0_55) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_2287,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK1,sK5),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_connsp_2(sK1,sK5),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1747])).

cnf(c_2430,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_2434,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_988,plain,
    ( X0_55 != X1_55
    | X2_55 != X1_55
    | X2_55 = X0_55 ),
    theory(equality)).

cnf(c_1790,plain,
    ( X0_55 != X1_55
    | k6_domain_1(u1_struct_0(sK1),sK5) != X1_55
    | k6_domain_1(u1_struct_0(sK1),sK5) = X0_55 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_1989,plain,
    ( X0_55 != k6_domain_1(u1_struct_0(sK1),sK5)
    | k6_domain_1(u1_struct_0(sK1),sK5) = X0_55
    | k6_domain_1(u1_struct_0(sK1),sK5) != k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_2466,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_domain_1(u1_struct_0(sK1),sK5)
    | k6_domain_1(u1_struct_0(sK1),sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k6_domain_1(u1_struct_0(sK1),sK5) != k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_1642,plain,
    ( r2_hidden(sK5,X0_55)
    | ~ r2_hidden(sK5,k1_connsp_2(sK2,sK5))
    | ~ r1_tarski(k1_connsp_2(sK2,sK5),X0_55) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_2542,plain,
    ( ~ r2_hidden(sK5,k1_connsp_2(sK2,sK5))
    | r2_hidden(sK5,u1_struct_0(sK2))
    | ~ r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_2543,plain,
    ( r2_hidden(sK5,k1_connsp_2(sK2,sK5)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top
    | r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2542])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_196,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_253,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_197])).

cnf(c_973,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | ~ r1_tarski(X1_55,X2_55)
    | ~ v1_xboole_0(X2_55) ),
    inference(subtyping,[status(esa)],[c_253])).

cnf(c_1655,plain,
    ( ~ r2_hidden(X0_55,X1_55)
    | ~ r1_tarski(X1_55,u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_2691,plain,
    ( ~ r2_hidden(sK5,k1_connsp_2(sK1,sK5))
    | ~ r1_tarski(k1_connsp_2(sK1,sK5),u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_976,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1437,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_976])).

cnf(c_1436,plain,
    ( k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55)
    | m1_subset_1(X0_55,X1_55) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_2087,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1437,c_1436])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_983,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X0_55)
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1431,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X0_55) = iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_983])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_984,plain,
    ( ~ r2_hidden(sK0(X0_55,X1_55),X1_55)
    | r1_tarski(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1430,plain,
    ( r2_hidden(sK0(X0_55,X1_55),X1_55) != iProver_top
    | r1_tarski(X0_55,X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_1883,plain,
    ( r1_tarski(X0_55,X0_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_1430])).

cnf(c_1444,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK1,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_969])).

cnf(c_1827,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k1_connsp_2(sK1,X0_55),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1444,c_1435])).

cnf(c_1443,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_55,k1_connsp_2(sK1,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_970])).

cnf(c_2256,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_55,X1_55) = iProver_top
    | r1_tarski(k1_connsp_2(sK1,X0_55),X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_1432])).

cnf(c_2507,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_55,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1827,c_2256])).

cnf(c_2610,plain,
    ( r2_hidden(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1437,c_2507])).

cnf(c_1440,plain,
    ( r2_hidden(X0_55,X1_55) != iProver_top
    | r1_tarski(X1_55,X2_55) != iProver_top
    | v1_xboole_0(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_2715,plain,
    ( r1_tarski(u1_struct_0(sK1),X0_55) != iProver_top
    | v1_xboole_0(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2610,c_1440])).

cnf(c_2875,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_2715])).

cnf(c_2972,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(superposition,[status(thm)],[c_2087,c_2875])).

cnf(c_3,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_981,plain,
    ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55))
    | ~ r2_hidden(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1433,plain,
    ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55)) = iProver_top
    | r2_hidden(X0_55,X1_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_2977,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK5),k1_zfmisc_1(X0_55)) = iProver_top
    | r2_hidden(sK5,X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_1433])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_408,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_413,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_409,c_25])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_413])).

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
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_17,negated_conjecture,
    ( v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_383,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v1_funct_1(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_384,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_tex_2(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v3_tdlat_3(sK1)
    | ~ v1_funct_1(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_26,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_19,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(renaming,[status(thm)],[c_388])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_414,c_389])).

cnf(c_971,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_55) = k2_pre_topc(sK1,X0_55) ),
    inference(subtyping,[status(esa)],[c_450])).

cnf(c_1442,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_55) = k2_pre_topc(sK1,X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_971])).

cnf(c_3112,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | r2_hidden(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_1442])).

cnf(c_2712,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(k1_connsp_2(sK2,X0_55),X1_55) != iProver_top
    | v1_xboole_0(X1_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1440])).

cnf(c_3390,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1962,c_2712])).

cnf(c_994,plain,
    ( k8_relset_1(X0_55,X1_55,X2_55,X3_55) = k8_relset_1(X4_55,X5_55,X6_55,X7_55)
    | X0_55 != X4_55
    | X1_55 != X5_55
    | X2_55 != X6_55
    | X3_55 != X7_55 ),
    theory(equality)).

cnf(c_3409,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5))
    | k6_domain_1(u1_struct_0(sK2),sK5) != k6_domain_1(u1_struct_0(sK1),sK5)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_3082,plain,
    ( X0_55 != X1_55
    | X0_55 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X1_55 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_3758,plain,
    ( X0_55 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | X0_55 != k6_domain_1(u1_struct_0(sK2),sK5)
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_4009,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_domain_1(u1_struct_0(sK2),sK5)
    | k6_domain_1(u1_struct_0(sK2),sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k6_domain_1(u1_struct_0(sK2),sK5) != k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(instantiation,[status(thm)],[c_3758])).

cnf(c_4010,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_2452,plain,
    ( X0_55 != X1_55
    | X0_55 = k6_domain_1(u1_struct_0(sK1),sK5)
    | k6_domain_1(u1_struct_0(sK1),sK5) != X1_55 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_2998,plain,
    ( X0_55 != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | X0_55 = k6_domain_1(u1_struct_0(sK1),sK5)
    | k6_domain_1(u1_struct_0(sK1),sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2452])).

cnf(c_4623,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | k6_domain_1(u1_struct_0(sK2),sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
    | k6_domain_1(u1_struct_0(sK1),sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2998])).

cnf(c_4626,plain,
    ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3369,c_41,c_15,c_1005,c_977,c_1553,c_1556,c_1560,c_1563,c_1599,c_1603,c_1788,c_1789,c_1946,c_2045,c_2226,c_2287,c_2430,c_2434,c_2466,c_2543,c_2691,c_3112,c_3390,c_3409,c_4009,c_4010,c_4623])).

cnf(c_4633,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1438,c_4626])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.32/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/0.99  
% 2.32/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/0.99  
% 2.32/0.99  ------  iProver source info
% 2.32/0.99  
% 2.32/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.32/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/0.99  git: non_committed_changes: false
% 2.32/0.99  git: last_make_outside_of_git: false
% 2.32/0.99  
% 2.32/0.99  ------ 
% 2.32/0.99  
% 2.32/0.99  ------ Input Options
% 2.32/0.99  
% 2.32/0.99  --out_options                           all
% 2.32/0.99  --tptp_safe_out                         true
% 2.32/0.99  --problem_path                          ""
% 2.32/0.99  --include_path                          ""
% 2.32/0.99  --clausifier                            res/vclausify_rel
% 2.32/0.99  --clausifier_options                    --mode clausify
% 2.32/0.99  --stdin                                 false
% 2.32/0.99  --stats_out                             all
% 2.32/0.99  
% 2.32/0.99  ------ General Options
% 2.32/0.99  
% 2.32/0.99  --fof                                   false
% 2.32/0.99  --time_out_real                         305.
% 2.32/0.99  --time_out_virtual                      -1.
% 2.32/0.99  --symbol_type_check                     false
% 2.32/0.99  --clausify_out                          false
% 2.32/0.99  --sig_cnt_out                           false
% 2.32/0.99  --trig_cnt_out                          false
% 2.32/0.99  --trig_cnt_out_tolerance                1.
% 2.32/0.99  --trig_cnt_out_sk_spl                   false
% 2.32/0.99  --abstr_cl_out                          false
% 2.32/0.99  
% 2.32/0.99  ------ Global Options
% 2.32/0.99  
% 2.32/0.99  --schedule                              default
% 2.32/0.99  --add_important_lit                     false
% 2.32/0.99  --prop_solver_per_cl                    1000
% 2.32/0.99  --min_unsat_core                        false
% 2.32/0.99  --soft_assumptions                      false
% 2.32/0.99  --soft_lemma_size                       3
% 2.32/0.99  --prop_impl_unit_size                   0
% 2.32/0.99  --prop_impl_unit                        []
% 2.32/0.99  --share_sel_clauses                     true
% 2.32/0.99  --reset_solvers                         false
% 2.32/0.99  --bc_imp_inh                            [conj_cone]
% 2.32/0.99  --conj_cone_tolerance                   3.
% 2.32/0.99  --extra_neg_conj                        none
% 2.32/0.99  --large_theory_mode                     true
% 2.32/0.99  --prolific_symb_bound                   200
% 2.32/0.99  --lt_threshold                          2000
% 2.32/0.99  --clause_weak_htbl                      true
% 2.32/0.99  --gc_record_bc_elim                     false
% 2.32/0.99  
% 2.32/0.99  ------ Preprocessing Options
% 2.32/0.99  
% 2.32/0.99  --preprocessing_flag                    true
% 2.32/0.99  --time_out_prep_mult                    0.1
% 2.32/0.99  --splitting_mode                        input
% 2.32/0.99  --splitting_grd                         true
% 2.32/0.99  --splitting_cvd                         false
% 2.32/0.99  --splitting_cvd_svl                     false
% 2.32/0.99  --splitting_nvd                         32
% 2.32/0.99  --sub_typing                            true
% 2.32/0.99  --prep_gs_sim                           true
% 2.32/0.99  --prep_unflatten                        true
% 2.32/0.99  --prep_res_sim                          true
% 2.32/0.99  --prep_upred                            true
% 2.32/0.99  --prep_sem_filter                       exhaustive
% 2.32/0.99  --prep_sem_filter_out                   false
% 2.32/0.99  --pred_elim                             true
% 2.32/0.99  --res_sim_input                         true
% 2.32/0.99  --eq_ax_congr_red                       true
% 2.32/0.99  --pure_diseq_elim                       true
% 2.32/0.99  --brand_transform                       false
% 2.32/0.99  --non_eq_to_eq                          false
% 2.32/0.99  --prep_def_merge                        true
% 2.32/0.99  --prep_def_merge_prop_impl              false
% 2.32/0.99  --prep_def_merge_mbd                    true
% 2.32/0.99  --prep_def_merge_tr_red                 false
% 2.32/0.99  --prep_def_merge_tr_cl                  false
% 2.32/0.99  --smt_preprocessing                     true
% 2.32/0.99  --smt_ac_axioms                         fast
% 2.32/0.99  --preprocessed_out                      false
% 2.32/0.99  --preprocessed_stats                    false
% 2.32/0.99  
% 2.32/0.99  ------ Abstraction refinement Options
% 2.32/0.99  
% 2.32/0.99  --abstr_ref                             []
% 2.32/0.99  --abstr_ref_prep                        false
% 2.32/0.99  --abstr_ref_until_sat                   false
% 2.32/0.99  --abstr_ref_sig_restrict                funpre
% 2.32/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/0.99  --abstr_ref_under                       []
% 2.32/0.99  
% 2.32/0.99  ------ SAT Options
% 2.32/0.99  
% 2.32/0.99  --sat_mode                              false
% 2.32/0.99  --sat_fm_restart_options                ""
% 2.32/0.99  --sat_gr_def                            false
% 2.32/0.99  --sat_epr_types                         true
% 2.32/0.99  --sat_non_cyclic_types                  false
% 2.32/0.99  --sat_finite_models                     false
% 2.32/0.99  --sat_fm_lemmas                         false
% 2.32/0.99  --sat_fm_prep                           false
% 2.32/0.99  --sat_fm_uc_incr                        true
% 2.32/0.99  --sat_out_model                         small
% 2.32/0.99  --sat_out_clauses                       false
% 2.32/0.99  
% 2.32/0.99  ------ QBF Options
% 2.32/0.99  
% 2.32/0.99  --qbf_mode                              false
% 2.32/0.99  --qbf_elim_univ                         false
% 2.32/0.99  --qbf_dom_inst                          none
% 2.32/0.99  --qbf_dom_pre_inst                      false
% 2.32/0.99  --qbf_sk_in                             false
% 2.32/0.99  --qbf_pred_elim                         true
% 2.32/0.99  --qbf_split                             512
% 2.32/0.99  
% 2.32/0.99  ------ BMC1 Options
% 2.32/0.99  
% 2.32/0.99  --bmc1_incremental                      false
% 2.32/0.99  --bmc1_axioms                           reachable_all
% 2.32/0.99  --bmc1_min_bound                        0
% 2.32/0.99  --bmc1_max_bound                        -1
% 2.32/0.99  --bmc1_max_bound_default                -1
% 2.32/0.99  --bmc1_symbol_reachability              true
% 2.32/0.99  --bmc1_property_lemmas                  false
% 2.32/0.99  --bmc1_k_induction                      false
% 2.32/0.99  --bmc1_non_equiv_states                 false
% 2.32/0.99  --bmc1_deadlock                         false
% 2.32/0.99  --bmc1_ucm                              false
% 2.32/0.99  --bmc1_add_unsat_core                   none
% 2.32/0.99  --bmc1_unsat_core_children              false
% 2.32/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/0.99  --bmc1_out_stat                         full
% 2.32/0.99  --bmc1_ground_init                      false
% 2.32/0.99  --bmc1_pre_inst_next_state              false
% 2.32/0.99  --bmc1_pre_inst_state                   false
% 2.32/0.99  --bmc1_pre_inst_reach_state             false
% 2.32/0.99  --bmc1_out_unsat_core                   false
% 2.32/0.99  --bmc1_aig_witness_out                  false
% 2.32/0.99  --bmc1_verbose                          false
% 2.32/0.99  --bmc1_dump_clauses_tptp                false
% 2.32/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.32/0.99  --bmc1_dump_file                        -
% 2.32/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.32/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.32/0.99  --bmc1_ucm_extend_mode                  1
% 2.32/0.99  --bmc1_ucm_init_mode                    2
% 2.32/0.99  --bmc1_ucm_cone_mode                    none
% 2.32/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.32/0.99  --bmc1_ucm_relax_model                  4
% 2.32/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.32/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/0.99  --bmc1_ucm_layered_model                none
% 2.32/0.99  --bmc1_ucm_max_lemma_size               10
% 2.32/0.99  
% 2.32/0.99  ------ AIG Options
% 2.32/0.99  
% 2.32/0.99  --aig_mode                              false
% 2.32/0.99  
% 2.32/0.99  ------ Instantiation Options
% 2.32/0.99  
% 2.32/0.99  --instantiation_flag                    true
% 2.32/0.99  --inst_sos_flag                         false
% 2.32/0.99  --inst_sos_phase                        true
% 2.32/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/0.99  --inst_lit_sel_side                     num_symb
% 2.32/0.99  --inst_solver_per_active                1400
% 2.32/0.99  --inst_solver_calls_frac                1.
% 2.32/0.99  --inst_passive_queue_type               priority_queues
% 2.32/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/0.99  --inst_passive_queues_freq              [25;2]
% 2.32/0.99  --inst_dismatching                      true
% 2.32/0.99  --inst_eager_unprocessed_to_passive     true
% 2.32/0.99  --inst_prop_sim_given                   true
% 2.32/0.99  --inst_prop_sim_new                     false
% 2.32/0.99  --inst_subs_new                         false
% 2.32/0.99  --inst_eq_res_simp                      false
% 2.32/0.99  --inst_subs_given                       false
% 2.32/0.99  --inst_orphan_elimination               true
% 2.32/0.99  --inst_learning_loop_flag               true
% 2.32/0.99  --inst_learning_start                   3000
% 2.32/0.99  --inst_learning_factor                  2
% 2.32/0.99  --inst_start_prop_sim_after_learn       3
% 2.32/0.99  --inst_sel_renew                        solver
% 2.32/0.99  --inst_lit_activity_flag                true
% 2.32/0.99  --inst_restr_to_given                   false
% 2.32/0.99  --inst_activity_threshold               500
% 2.32/0.99  --inst_out_proof                        true
% 2.32/0.99  
% 2.32/0.99  ------ Resolution Options
% 2.32/0.99  
% 2.32/0.99  --resolution_flag                       true
% 2.32/0.99  --res_lit_sel                           adaptive
% 2.32/0.99  --res_lit_sel_side                      none
% 2.32/0.99  --res_ordering                          kbo
% 2.32/0.99  --res_to_prop_solver                    active
% 2.32/0.99  --res_prop_simpl_new                    false
% 2.32/0.99  --res_prop_simpl_given                  true
% 2.32/0.99  --res_passive_queue_type                priority_queues
% 2.32/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  ------ Parsing...
% 2.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.00  ------ Proving...
% 2.32/1.00  ------ Problem Properties 
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  clauses                                 18
% 2.32/1.00  conjectures                             4
% 2.32/1.00  EPR                                     2
% 2.32/1.00  Horn                                    16
% 2.32/1.00  unary                                   4
% 2.32/1.00  binary                                  11
% 2.32/1.00  lits                                    35
% 2.32/1.00  lits eq                                 3
% 2.32/1.00  fd_pure                                 0
% 2.32/1.00  fd_pseudo                               0
% 2.32/1.00  fd_cond                                 0
% 2.32/1.00  fd_pseudo_cond                          0
% 2.32/1.00  AC symbols                              0
% 2.32/1.00  
% 2.32/1.00  ------ Schedule dynamic 5 is on 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  Current options:
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     none
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       false
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ Proving...
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS status Theorem for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00   Resolution empty clause
% 2.32/1.00  
% 2.32/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  fof(f82,plain,(
% 2.32/1.00    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f19,conjecture,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f20,negated_conjecture,(
% 2.32/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.32/1.00    inference(negated_conjecture,[],[f19])).
% 2.32/1.00  
% 2.32/1.00  fof(f36,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f20])).
% 2.32/1.00  
% 2.32/1.00  fof(f37,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f47,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) & sK5 = X3 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f46,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK4 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f45,plain,(
% 2.32/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK3,X0,X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK3,X0,X1) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f44,plain,(
% 2.32/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(X2,X0,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v5_pre_topc(X2,X0,sK2) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & v4_tex_2(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f43,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X2,sK1,X1) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & v4_tex_2(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f48,plain,(
% 2.32/1.00    ((((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2))) & v3_borsuk_1(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & v4_tex_2(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f37,f47,f46,f45,f44,f43])).
% 2.32/1.00  
% 2.32/1.00  fof(f84,plain,(
% 2.32/1.00    sK4 = sK5),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f95,plain,(
% 2.32/1.00    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.32/1.00    inference(definition_unfolding,[],[f82,f84])).
% 2.32/1.00  
% 2.32/1.00  fof(f16,axiom,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f30,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f16])).
% 2.32/1.00  
% 2.32/1.00  fof(f31,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f30])).
% 2.32/1.00  
% 2.32/1.00  fof(f67,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f31])).
% 2.32/1.00  
% 2.32/1.00  fof(f12,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f24,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f12])).
% 2.32/1.00  
% 2.32/1.00  fof(f25,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f24])).
% 2.32/1.00  
% 2.32/1.00  fof(f63,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f25])).
% 2.32/1.00  
% 2.32/1.00  fof(f76,plain,(
% 2.32/1.00    m1_pre_topc(sK2,sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f71,plain,(
% 2.32/1.00    v2_pre_topc(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f73,plain,(
% 2.32/1.00    l1_pre_topc(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f74,plain,(
% 2.32/1.00    ~v2_struct_0(sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f13,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f26,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f13])).
% 2.32/1.00  
% 2.32/1.00  fof(f64,plain,(
% 2.32/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f26])).
% 2.32/1.00  
% 2.32/1.00  fof(f10,axiom,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f42,plain,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.32/1.00    inference(nnf_transformation,[],[f10])).
% 2.32/1.00  
% 2.32/1.00  fof(f60,plain,(
% 2.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f42])).
% 2.32/1.00  
% 2.32/1.00  fof(f17,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f32,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f17])).
% 2.32/1.00  
% 2.32/1.00  fof(f33,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f32])).
% 2.32/1.00  
% 2.32/1.00  fof(f68,plain,(
% 2.32/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f33])).
% 2.32/1.00  
% 2.32/1.00  fof(f1,axiom,(
% 2.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f21,plain,(
% 2.32/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f1])).
% 2.32/1.00  
% 2.32/1.00  fof(f38,plain,(
% 2.32/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.00    inference(nnf_transformation,[],[f21])).
% 2.32/1.00  
% 2.32/1.00  fof(f39,plain,(
% 2.32/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.00    inference(rectify,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f40,plain,(
% 2.32/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f41,plain,(
% 2.32/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 2.32/1.00  
% 2.32/1.00  fof(f49,plain,(
% 2.32/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f41])).
% 2.32/1.00  
% 2.32/1.00  fof(f83,plain,(
% 2.32/1.00    m1_subset_1(sK5,u1_struct_0(sK1))),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f85,plain,(
% 2.32/1.00    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f94,plain,(
% 2.32/1.00    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 2.32/1.00    inference(definition_unfolding,[],[f85,f84])).
% 2.32/1.00  
% 2.32/1.00  fof(f70,plain,(
% 2.32/1.00    ~v2_struct_0(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f15,axiom,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f28,plain,(
% 2.32/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f29,plain,(
% 2.32/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.32/1.00    inference(flattening,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f66,plain,(
% 2.32/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f29])).
% 2.32/1.00  
% 2.32/1.00  fof(f2,axiom,(
% 2.32/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f52,plain,(
% 2.32/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f2])).
% 2.32/1.00  
% 2.32/1.00  fof(f3,axiom,(
% 2.32/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f53,plain,(
% 2.32/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f3])).
% 2.32/1.00  
% 2.32/1.00  fof(f4,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f54,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f4])).
% 2.32/1.00  
% 2.32/1.00  fof(f5,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f55,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f5])).
% 2.32/1.00  
% 2.32/1.00  fof(f6,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f56,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f6])).
% 2.32/1.00  
% 2.32/1.00  fof(f7,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f57,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f7])).
% 2.32/1.00  
% 2.32/1.00  fof(f8,axiom,(
% 2.32/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f58,plain,(
% 2.32/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f8])).
% 2.32/1.00  
% 2.32/1.00  fof(f86,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f57,f58])).
% 2.32/1.00  
% 2.32/1.00  fof(f87,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f56,f86])).
% 2.32/1.00  
% 2.32/1.00  fof(f88,plain,(
% 2.32/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f55,f87])).
% 2.32/1.00  
% 2.32/1.00  fof(f89,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f54,f88])).
% 2.32/1.00  
% 2.32/1.00  fof(f90,plain,(
% 2.32/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f53,f89])).
% 2.32/1.00  
% 2.32/1.00  fof(f91,plain,(
% 2.32/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f52,f90])).
% 2.32/1.00  
% 2.32/1.00  fof(f93,plain,(
% 2.32/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f66,f91])).
% 2.32/1.00  
% 2.32/1.00  fof(f11,axiom,(
% 2.32/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f23,plain,(
% 2.32/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.32/1.00    inference(ennf_transformation,[],[f11])).
% 2.32/1.00  
% 2.32/1.00  fof(f62,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f61,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f42])).
% 2.32/1.00  
% 2.32/1.00  fof(f50,plain,(
% 2.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f41])).
% 2.32/1.00  
% 2.32/1.00  fof(f51,plain,(
% 2.32/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f41])).
% 2.32/1.00  
% 2.32/1.00  fof(f9,axiom,(
% 2.32/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f22,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.32/1.00    inference(ennf_transformation,[],[f9])).
% 2.32/1.00  
% 2.32/1.00  fof(f59,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f22])).
% 2.32/1.00  
% 2.32/1.00  fof(f92,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.32/1.00    inference(definition_unfolding,[],[f59,f91])).
% 2.32/1.00  
% 2.32/1.00  fof(f14,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f27,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f14])).
% 2.32/1.00  
% 2.32/1.00  fof(f65,plain,(
% 2.32/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f18,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 2.32/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f34,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f18])).
% 2.32/1.00  
% 2.32/1.00  fof(f35,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f34])).
% 2.32/1.00  
% 2.32/1.00  fof(f69,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f35])).
% 2.32/1.00  
% 2.32/1.00  fof(f96,plain,(
% 2.32/1.00    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(equality_resolution,[],[f69])).
% 2.32/1.00  
% 2.32/1.00  fof(f81,plain,(
% 2.32/1.00    v3_borsuk_1(sK3,sK1,sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f72,plain,(
% 2.32/1.00    v3_tdlat_3(sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f75,plain,(
% 2.32/1.00    v4_tex_2(sK2,sK1)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f77,plain,(
% 2.32/1.00    v1_funct_1(sK3)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f78,plain,(
% 2.32/1.00    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f79,plain,(
% 2.32/1.00    v5_pre_topc(sK3,sK1,sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  fof(f80,plain,(
% 2.32/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.32/1.00    inference(cnf_transformation,[],[f48])).
% 2.32/1.00  
% 2.32/1.00  cnf(c_16,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_975,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1438,plain,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_975]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_11,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_7,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | v2_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_22,negated_conjecture,
% 2.32/1.00      ( m1_pre_topc(sK2,sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_437,plain,
% 2.32/1.00      ( ~ l1_pre_topc(X0)
% 2.32/1.00      | ~ v2_pre_topc(X0)
% 2.32/1.00      | v2_pre_topc(X1)
% 2.32/1.00      | sK2 != X1
% 2.32/1.00      | sK1 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_438,plain,
% 2.32/1.00      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_437]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_27,negated_conjecture,
% 2.32/1.00      ( v2_pre_topc(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_25,negated_conjecture,
% 2.32/1.00      ( l1_pre_topc(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_440,plain,
% 2.32/1.00      ( v2_pre_topc(sK2) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_438,c_27,c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_513,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | sK2 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_440]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_514,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_513]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_24,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_8,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_426,plain,
% 2.32/1.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X1 | sK1 != X0 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_427,plain,
% 2.32/1.00      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_426]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_518,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_514,c_25,c_24,c_427]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_967,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK2))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK2,X0_55),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_518]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1446,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK2,X0_55),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_967]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_979,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) | r1_tarski(X0_55,X1_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1435,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
% 2.32/1.00      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_979]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1962,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK2,X0_55),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1446,c_1435]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_12,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_495,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | sK2 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_440]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_496,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.32/1.00      | r2_hidden(X0,k1_connsp_2(sK2,X0))
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_495]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_500,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.32/1.00      | r2_hidden(X0,k1_connsp_2(sK2,X0)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_496,c_25,c_24,c_427]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_968,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK2))
% 2.32/1.00      | r2_hidden(X0_55,k1_connsp_2(sK2,X0_55)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_500]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1445,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | r2_hidden(X0_55,k1_connsp_2(sK2,X0_55)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_968]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2,plain,
% 2.32/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_982,plain,
% 2.32/1.00      ( ~ r2_hidden(X0_55,X1_55)
% 2.32/1.00      | r2_hidden(X0_55,X2_55)
% 2.32/1.00      | ~ r1_tarski(X1_55,X2_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1432,plain,
% 2.32/1.00      ( r2_hidden(X0_55,X1_55) != iProver_top
% 2.32/1.00      | r2_hidden(X0_55,X2_55) = iProver_top
% 2.32/1.00      | r1_tarski(X1_55,X2_55) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2255,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | r2_hidden(X0_55,X1_55) = iProver_top
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK2,X0_55),X1_55) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1445,c_1432]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3369,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | r2_hidden(X0_55,u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1962,c_2255]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_41,plain,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_15,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_986,plain,( X0_55 = X0_55 ),theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1005,plain,
% 2.32/1.00      ( sK3 = sK3 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_14,negated_conjecture,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_977,negated_conjecture,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_477,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | sK1 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_478,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | v2_struct_0(sK1)
% 2.32/1.00      | ~ l1_pre_topc(sK1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_477]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_28,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_482,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_478,c_28,c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_969,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK1,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_482]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1553,plain,
% 2.32/1.00      ( m1_subset_1(k1_connsp_2(sK1,sK5),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_969]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_459,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | sK1 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_460,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.32/1.00      | r2_hidden(X0,k1_connsp_2(sK1,X0))
% 2.32/1.00      | v2_struct_0(sK1)
% 2.32/1.00      | ~ l1_pre_topc(sK1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_459]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_464,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.32/1.00      | r2_hidden(X0,k1_connsp_2(sK1,X0)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_460,c_28,c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_970,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,u1_struct_0(sK1))
% 2.32/1.00      | r2_hidden(X0_55,k1_connsp_2(sK1,X0_55)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_464]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1556,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 2.32/1.00      | r2_hidden(sK5,k1_connsp_2(sK1,sK5)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_970]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1559,plain,
% 2.32/1.00      ( m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_967]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1560,plain,
% 2.32/1.00      ( m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.32/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1559]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1562,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 2.32/1.00      | r2_hidden(sK5,k1_connsp_2(sK2,sK5)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_968]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1563,plain,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | r2_hidden(sK5,k1_connsp_2(sK2,sK5)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1562]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_10,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,X1)
% 2.32/1.00      | v1_xboole_0(X1)
% 2.32/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_978,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,X1_55)
% 2.32/1.00      | v1_xboole_0(X1_55)
% 2.32/1.00      | k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1599,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK1))
% 2.32/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_978]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1602,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK2))
% 2.32/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_978]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1603,plain,
% 2.32/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5)
% 2.32/1.00      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_995,plain,
% 2.32/1.00      ( k2_pre_topc(X0_56,X0_55) = k2_pre_topc(X0_56,X1_55) | X0_55 != X1_55 ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1673,plain,
% 2.32/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,X0_55)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != X0_55 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_995]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1788,plain,
% 2.32/1.00      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1673]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1789,plain,
% 2.32/1.00      ( k6_domain_1(u1_struct_0(sK1),sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_989,plain,
% 2.32/1.00      ( X0_57 != X1_57 | X2_57 != X1_57 | X2_57 = X0_57 ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1671,plain,
% 2.32/1.00      ( X0_57 != X1_57
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != X1_57
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = X0_57 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_989]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1855,plain,
% 2.32/1.00      ( X0_57 != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = X0_57
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1671]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1946,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1855]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1573,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != X0_57
% 2.32/1.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != X0_57 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_989]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2045,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1573]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1732,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | r1_tarski(X0_55,u1_struct_0(sK2)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_979]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2225,plain,
% 2.32/1.00      ( ~ m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1732]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2226,plain,
% 2.32/1.00      ( m1_subset_1(k1_connsp_2(sK2,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2225]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1747,plain,
% 2.32/1.00      ( ~ m1_subset_1(k1_connsp_2(sK1,sK5),k1_zfmisc_1(X0_55))
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK1,sK5),X0_55) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_979]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2287,plain,
% 2.32/1.00      ( ~ m1_subset_1(k1_connsp_2(sK1,sK5),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK1,sK5),u1_struct_0(sK1)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1747]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2430,plain,
% 2.32/1.00      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2434,plain,
% 2.32/1.00      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_988,plain,
% 2.32/1.00      ( X0_55 != X1_55 | X2_55 != X1_55 | X2_55 = X0_55 ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1790,plain,
% 2.32/1.00      ( X0_55 != X1_55
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != X1_55
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) = X0_55 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_988]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1989,plain,
% 2.32/1.00      ( X0_55 != k6_domain_1(u1_struct_0(sK1),sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) = X0_55
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1790]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2466,plain,
% 2.32/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_domain_1(u1_struct_0(sK1),sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1989]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1642,plain,
% 2.32/1.00      ( r2_hidden(sK5,X0_55)
% 2.32/1.00      | ~ r2_hidden(sK5,k1_connsp_2(sK2,sK5))
% 2.32/1.00      | ~ r1_tarski(k1_connsp_2(sK2,sK5),X0_55) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_982]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2542,plain,
% 2.32/1.00      ( ~ r2_hidden(sK5,k1_connsp_2(sK2,sK5))
% 2.32/1.00      | r2_hidden(sK5,u1_struct_0(sK2))
% 2.32/1.00      | ~ r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1642]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2543,plain,
% 2.32/1.00      ( r2_hidden(sK5,k1_connsp_2(sK2,sK5)) != iProver_top
% 2.32/1.00      | r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK2,sK5),u1_struct_0(sK2)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2542]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_6,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/1.00      | ~ r2_hidden(X2,X0)
% 2.32/1.00      | ~ v1_xboole_0(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4,plain,
% 2.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_196,plain,
% 2.32/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.32/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_197,plain,
% 2.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_196]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_253,plain,
% 2.32/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.32/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_197]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_973,plain,
% 2.32/1.00      ( ~ r2_hidden(X0_55,X1_55)
% 2.32/1.00      | ~ r1_tarski(X1_55,X2_55)
% 2.32/1.00      | ~ v1_xboole_0(X2_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_253]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1655,plain,
% 2.32/1.00      ( ~ r2_hidden(X0_55,X1_55)
% 2.32/1.00      | ~ r1_tarski(X1_55,u1_struct_0(sK1))
% 2.32/1.00      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_973]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2691,plain,
% 2.32/1.00      ( ~ r2_hidden(sK5,k1_connsp_2(sK1,sK5))
% 2.32/1.00      | ~ r1_tarski(k1_connsp_2(sK1,sK5),u1_struct_0(sK1))
% 2.32/1.00      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1655]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_976,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1437,plain,
% 2.32/1.00      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_976]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1436,plain,
% 2.32/1.00      ( k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55) = k6_domain_1(X1_55,X0_55)
% 2.32/1.00      | m1_subset_1(X0_55,X1_55) != iProver_top
% 2.32/1.00      | v1_xboole_0(X1_55) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2087,plain,
% 2.32/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1437,c_1436]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1,plain,
% 2.32/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_983,plain,
% 2.32/1.00      ( r2_hidden(sK0(X0_55,X1_55),X0_55) | r1_tarski(X0_55,X1_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1431,plain,
% 2.32/1.00      ( r2_hidden(sK0(X0_55,X1_55),X0_55) = iProver_top
% 2.32/1.00      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_983]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_0,plain,
% 2.32/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_984,plain,
% 2.32/1.00      ( ~ r2_hidden(sK0(X0_55,X1_55),X1_55) | r1_tarski(X0_55,X1_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1430,plain,
% 2.32/1.00      ( r2_hidden(sK0(X0_55,X1_55),X1_55) != iProver_top
% 2.32/1.00      | r1_tarski(X0_55,X1_55) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1883,plain,
% 2.32/1.00      ( r1_tarski(X0_55,X0_55) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1431,c_1430]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1444,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | m1_subset_1(k1_connsp_2(sK1,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_969]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1827,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK1,X0_55),u1_struct_0(sK1)) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1444,c_1435]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1443,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | r2_hidden(X0_55,k1_connsp_2(sK1,X0_55)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_970]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2256,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | r2_hidden(X0_55,X1_55) = iProver_top
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK1,X0_55),X1_55) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1443,c_1432]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2507,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK1)) != iProver_top
% 2.32/1.00      | r2_hidden(X0_55,u1_struct_0(sK1)) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1827,c_2256]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2610,plain,
% 2.32/1.00      ( r2_hidden(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1437,c_2507]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1440,plain,
% 2.32/1.00      ( r2_hidden(X0_55,X1_55) != iProver_top
% 2.32/1.00      | r1_tarski(X1_55,X2_55) != iProver_top
% 2.32/1.00      | v1_xboole_0(X2_55) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2715,plain,
% 2.32/1.00      ( r1_tarski(u1_struct_0(sK1),X0_55) != iProver_top
% 2.32/1.00      | v1_xboole_0(X0_55) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2610,c_1440]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2875,plain,
% 2.32/1.00      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1883,c_2715]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2972,plain,
% 2.32/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2087,c_2875]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3,plain,
% 2.32/1.00      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 2.32/1.00      | ~ r2_hidden(X0,X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_981,plain,
% 2.32/1.00      ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55))
% 2.32/1.00      | ~ r2_hidden(X0_55,X1_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1433,plain,
% 2.32/1.00      ( m1_subset_1(k6_enumset1(X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55,X0_55),k1_zfmisc_1(X1_55)) = iProver_top
% 2.32/1.00      | r2_hidden(X0_55,X1_55) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2977,plain,
% 2.32/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK5),k1_zfmisc_1(X0_55)) = iProver_top
% 2.32/1.00      | r2_hidden(sK5,X0_55) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2972,c_1433]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_9,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.32/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_408,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | sK2 != X1
% 2.32/1.00      | sK1 != X2 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_409,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | ~ l1_pre_topc(sK1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_413,plain,
% 2.32/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.32/1.00      inference(global_propositional_subsumption,[status(thm)],[c_409,c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_414,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_413]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_13,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | ~ v3_borsuk_1(X0,X1,X2)
% 2.32/1.00      | ~ v4_tex_2(X2,X1)
% 2.32/1.00      | ~ m1_pre_topc(X2,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.00      | ~ v3_tdlat_3(X1)
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X2)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 2.32/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_17,negated_conjecture,
% 2.32/1.00      ( v3_borsuk_1(sK3,sK1,sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_383,plain,
% 2.32/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.32/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 2.32/1.00      | ~ v4_tex_2(X2,X1)
% 2.32/1.00      | ~ m1_pre_topc(X2,X1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.32/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.32/1.00      | ~ v3_tdlat_3(X1)
% 2.32/1.00      | ~ v1_funct_1(X0)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X2)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | ~ v2_pre_topc(X1)
% 2.32/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 2.32/1.00      | sK3 != X0
% 2.32/1.00      | sK2 != X2
% 2.32/1.00      | sK1 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_384,plain,
% 2.32/1.00      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.32/1.00      | ~ v5_pre_topc(sK3,sK1,sK2)
% 2.32/1.00      | ~ v4_tex_2(sK2,sK1)
% 2.32/1.00      | ~ m1_pre_topc(sK2,sK1)
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.32/1.00      | ~ v3_tdlat_3(sK1)
% 2.32/1.00      | ~ v1_funct_1(sK3)
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | v2_struct_0(sK1)
% 2.32/1.00      | ~ l1_pre_topc(sK1)
% 2.32/1.00      | ~ v2_pre_topc(sK1)
% 2.32/1.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_383]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_26,negated_conjecture,
% 2.32/1.00      ( v3_tdlat_3(sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_23,negated_conjecture,
% 2.32/1.00      ( v4_tex_2(sK2,sK1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_21,negated_conjecture,
% 2.32/1.00      ( v1_funct_1(sK3) ),
% 2.32/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_20,negated_conjecture,
% 2.32/1.00      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_19,negated_conjecture,
% 2.32/1.00      ( v5_pre_topc(sK3,sK1,sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_18,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.32/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_388,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_384,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_389,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.32/1.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_388]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_450,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.32/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_414,c_389]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_971,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_55) = k2_pre_topc(sK1,X0_55) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_450]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1442,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_55) = k2_pre_topc(sK1,X0_55)
% 2.32/1.00      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_971]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3112,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | r2_hidden(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_2977,c_1442]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2712,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | r1_tarski(k1_connsp_2(sK2,X0_55),X1_55) != iProver_top
% 2.32/1.00      | v1_xboole_0(X1_55) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1445,c_1440]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3390,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1962,c_2712]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_994,plain,
% 2.32/1.00      ( k8_relset_1(X0_55,X1_55,X2_55,X3_55) = k8_relset_1(X4_55,X5_55,X6_55,X7_55)
% 2.32/1.00      | X0_55 != X4_55
% 2.32/1.00      | X1_55 != X5_55
% 2.32/1.00      | X2_55 != X6_55
% 2.32/1.00      | X3_55 != X7_55 ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3409,plain,
% 2.32/1.00      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK2),sK5) != k6_domain_1(u1_struct_0(sK1),sK5)
% 2.32/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.32/1.00      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.32/1.00      | sK3 != sK3 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_994]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3082,plain,
% 2.32/1.00      ( X0_55 != X1_55
% 2.32/1.00      | X0_55 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.32/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X1_55 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_988]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3758,plain,
% 2.32/1.00      ( X0_55 = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.32/1.00      | X0_55 != k6_domain_1(u1_struct_0(sK2),sK5)
% 2.32/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_domain_1(u1_struct_0(sK2),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3082]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4009,plain,
% 2.32/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_domain_1(u1_struct_0(sK2),sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK2),sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK2),sK5) != k6_domain_1(u1_struct_0(sK2),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3758]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4010,plain,
% 2.32/1.00      ( k6_domain_1(u1_struct_0(sK2),sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_986]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2452,plain,
% 2.32/1.00      ( X0_55 != X1_55
% 2.32/1.00      | X0_55 = k6_domain_1(u1_struct_0(sK1),sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != X1_55 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_988]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2998,plain,
% 2.32/1.00      ( X0_55 != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.32/1.00      | X0_55 = k6_domain_1(u1_struct_0(sK1),sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2452]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4623,plain,
% 2.32/1.00      ( k6_domain_1(u1_struct_0(sK2),sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK2),sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK1),sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2998]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4626,plain,
% 2.32/1.00      ( m1_subset_1(X0_55,u1_struct_0(sK2)) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_3369,c_41,c_15,c_1005,c_977,c_1553,c_1556,c_1560,c_1563,
% 2.32/1.00                 c_1599,c_1603,c_1788,c_1789,c_1946,c_2045,c_2226,c_2287,
% 2.32/1.00                 c_2430,c_2434,c_2466,c_2543,c_2691,c_3112,c_3390,c_3409,
% 2.32/1.00                 c_4009,c_4010,c_4623]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4633,plain,
% 2.32/1.00      ( $false ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_1438,c_4626]) ).
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  ------                               Statistics
% 2.32/1.00  
% 2.32/1.00  ------ General
% 2.32/1.00  
% 2.32/1.00  abstr_ref_over_cycles:                  0
% 2.32/1.00  abstr_ref_under_cycles:                 0
% 2.32/1.00  gc_basic_clause_elim:                   0
% 2.32/1.00  forced_gc_time:                         0
% 2.32/1.00  parsing_time:                           0.011
% 2.32/1.00  unif_index_cands_time:                  0.
% 2.32/1.00  unif_index_add_time:                    0.
% 2.32/1.00  orderings_time:                         0.
% 2.32/1.00  out_proof_time:                         0.012
% 2.32/1.00  total_time:                             0.167
% 2.32/1.00  num_of_symbols:                         61
% 2.32/1.00  num_of_terms:                           3113
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing
% 2.32/1.00  
% 2.32/1.00  num_of_splits:                          0
% 2.32/1.00  num_of_split_atoms:                     0
% 2.32/1.00  num_of_reused_defs:                     0
% 2.32/1.00  num_eq_ax_congr_red:                    46
% 2.32/1.00  num_of_sem_filtered_clauses:            1
% 2.32/1.00  num_of_subtypes:                        3
% 2.32/1.00  monotx_restored_types:                  0
% 2.32/1.00  sat_num_of_epr_types:                   0
% 2.32/1.00  sat_num_of_non_cyclic_types:            0
% 2.32/1.00  sat_guarded_non_collapsed_types:        0
% 2.32/1.00  num_pure_diseq_elim:                    0
% 2.32/1.00  simp_replaced_by:                       0
% 2.32/1.00  res_preprocessed:                       106
% 2.32/1.00  prep_upred:                             0
% 2.32/1.00  prep_unflattend:                        39
% 2.32/1.00  smt_new_axioms:                         0
% 2.32/1.00  pred_elim_cands:                        4
% 2.32/1.00  pred_elim:                              10
% 2.32/1.00  pred_elim_cl:                           11
% 2.32/1.00  pred_elim_cycles:                       14
% 2.32/1.00  merged_defs:                            8
% 2.32/1.00  merged_defs_ncl:                        0
% 2.32/1.00  bin_hyper_res:                          9
% 2.32/1.00  prep_cycles:                            4
% 2.32/1.00  pred_elim_time:                         0.007
% 2.32/1.00  splitting_time:                         0.
% 2.32/1.00  sem_filter_time:                        0.
% 2.32/1.00  monotx_time:                            0.
% 2.32/1.00  subtype_inf_time:                       0.
% 2.32/1.00  
% 2.32/1.00  ------ Problem properties
% 2.32/1.00  
% 2.32/1.00  clauses:                                18
% 2.32/1.00  conjectures:                            4
% 2.32/1.00  epr:                                    2
% 2.32/1.00  horn:                                   16
% 2.32/1.00  ground:                                 4
% 2.32/1.00  unary:                                  4
% 2.32/1.00  binary:                                 11
% 2.32/1.00  lits:                                   35
% 2.32/1.00  lits_eq:                                3
% 2.32/1.00  fd_pure:                                0
% 2.32/1.00  fd_pseudo:                              0
% 2.32/1.00  fd_cond:                                0
% 2.32/1.00  fd_pseudo_cond:                         0
% 2.32/1.00  ac_symbols:                             0
% 2.32/1.00  
% 2.32/1.00  ------ Propositional Solver
% 2.32/1.00  
% 2.32/1.00  prop_solver_calls:                      31
% 2.32/1.00  prop_fast_solver_calls:                 775
% 2.32/1.00  smt_solver_calls:                       0
% 2.32/1.00  smt_fast_solver_calls:                  0
% 2.32/1.00  prop_num_of_clauses:                    1389
% 2.32/1.00  prop_preprocess_simplified:             4121
% 2.32/1.00  prop_fo_subsumed:                       30
% 2.32/1.00  prop_solver_time:                       0.
% 2.32/1.00  smt_solver_time:                        0.
% 2.32/1.00  smt_fast_solver_time:                   0.
% 2.32/1.00  prop_fast_solver_time:                  0.
% 2.32/1.00  prop_unsat_core_time:                   0.
% 2.32/1.00  
% 2.32/1.00  ------ QBF
% 2.32/1.00  
% 2.32/1.00  qbf_q_res:                              0
% 2.32/1.00  qbf_num_tautologies:                    0
% 2.32/1.00  qbf_prep_cycles:                        0
% 2.32/1.00  
% 2.32/1.00  ------ BMC1
% 2.32/1.00  
% 2.32/1.00  bmc1_current_bound:                     -1
% 2.32/1.00  bmc1_last_solved_bound:                 -1
% 2.32/1.00  bmc1_unsat_core_size:                   -1
% 2.32/1.00  bmc1_unsat_core_parents_size:           -1
% 2.32/1.00  bmc1_merge_next_fun:                    0
% 2.32/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation
% 2.32/1.00  
% 2.32/1.00  inst_num_of_clauses:                    371
% 2.32/1.00  inst_num_in_passive:                    50
% 2.32/1.00  inst_num_in_active:                     318
% 2.32/1.00  inst_num_in_unprocessed:                3
% 2.32/1.00  inst_num_of_loops:                      420
% 2.32/1.00  inst_num_of_learning_restarts:          0
% 2.32/1.00  inst_num_moves_active_passive:          95
% 2.32/1.00  inst_lit_activity:                      0
% 2.32/1.00  inst_lit_activity_moves:                0
% 2.32/1.00  inst_num_tautologies:                   0
% 2.32/1.00  inst_num_prop_implied:                  0
% 2.32/1.00  inst_num_existing_simplified:           0
% 2.32/1.00  inst_num_eq_res_simplified:             0
% 2.32/1.00  inst_num_child_elim:                    0
% 2.32/1.00  inst_num_of_dismatching_blockings:      195
% 2.32/1.00  inst_num_of_non_proper_insts:           504
% 2.32/1.00  inst_num_of_duplicates:                 0
% 2.32/1.00  inst_inst_num_from_inst_to_res:         0
% 2.32/1.00  inst_dismatching_checking_time:         0.
% 2.32/1.00  
% 2.32/1.00  ------ Resolution
% 2.32/1.00  
% 2.32/1.00  res_num_of_clauses:                     0
% 2.32/1.00  res_num_in_passive:                     0
% 2.32/1.00  res_num_in_active:                      0
% 2.32/1.00  res_num_of_loops:                       110
% 2.32/1.00  res_forward_subset_subsumed:            70
% 2.32/1.00  res_backward_subset_subsumed:           2
% 2.32/1.00  res_forward_subsumed:                   0
% 2.32/1.00  res_backward_subsumed:                  0
% 2.32/1.00  res_forward_subsumption_resolution:     0
% 2.32/1.00  res_backward_subsumption_resolution:    1
% 2.32/1.00  res_clause_to_clause_subsumption:       429
% 2.32/1.00  res_orphan_elimination:                 0
% 2.32/1.00  res_tautology_del:                      103
% 2.32/1.00  res_num_eq_res_simplified:              0
% 2.32/1.00  res_num_sel_changes:                    0
% 2.32/1.00  res_moves_from_active_to_pass:          0
% 2.32/1.00  
% 2.32/1.00  ------ Superposition
% 2.32/1.00  
% 2.32/1.00  sup_time_total:                         0.
% 2.32/1.00  sup_time_generating:                    0.
% 2.32/1.00  sup_time_sim_full:                      0.
% 2.32/1.00  sup_time_sim_immed:                     0.
% 2.32/1.00  
% 2.32/1.00  sup_num_of_clauses:                     101
% 2.32/1.00  sup_num_in_active:                      74
% 2.32/1.00  sup_num_in_passive:                     27
% 2.32/1.00  sup_num_of_loops:                       82
% 2.32/1.00  sup_fw_superposition:                   93
% 2.32/1.00  sup_bw_superposition:                   47
% 2.32/1.00  sup_immediate_simplified:               10
% 2.32/1.00  sup_given_eliminated:                   0
% 2.32/1.00  comparisons_done:                       0
% 2.32/1.00  comparisons_avoided:                    0
% 2.32/1.00  
% 2.32/1.00  ------ Simplifications
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  sim_fw_subset_subsumed:                 6
% 2.32/1.00  sim_bw_subset_subsumed:                 15
% 2.32/1.00  sim_fw_subsumed:                        3
% 2.32/1.00  sim_bw_subsumed:                        0
% 2.32/1.00  sim_fw_subsumption_res:                 0
% 2.32/1.00  sim_bw_subsumption_res:                 0
% 2.32/1.00  sim_tautology_del:                      2
% 2.32/1.00  sim_eq_tautology_del:                   0
% 2.32/1.00  sim_eq_res_simp:                        0
% 2.32/1.00  sim_fw_demodulated:                     0
% 2.32/1.00  sim_bw_demodulated:                     1
% 2.32/1.00  sim_light_normalised:                   1
% 2.32/1.00  sim_joinable_taut:                      0
% 2.32/1.00  sim_joinable_simp:                      0
% 2.32/1.00  sim_ac_normalised:                      0
% 2.32/1.00  sim_smt_subsumption:                    0
% 2.32/1.00  
%------------------------------------------------------------------------------
