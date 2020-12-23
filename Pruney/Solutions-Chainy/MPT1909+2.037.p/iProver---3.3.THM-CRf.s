%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:01 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  170 (1244 expanded)
%              Number of clauses        :   82 ( 209 expanded)
%              Number of leaves         :   23 ( 492 expanded)
%              Depth                    :   20
%              Number of atoms          :  676 (12912 expanded)
%              Number of equality atoms :  140 (2380 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))
        & sK5 = X3
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f34,f43,f42,f41,f40,f39])).

fof(f78,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(definition_unfolding,[],[f76,f78])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f27])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK0(X0,X1),X0)
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK0(X0,X1),X0)
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f69,plain,(
    v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f80])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f81])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f83])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f84])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f85])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f31])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f75,plain,(
    v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f56,f85])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(definition_unfolding,[],[f79,f78])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_838,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1070,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_1,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_843,plain,
    ( r2_hidden(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,X1_54)
    | v1_xboole_0(X1_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1066,plain,
    ( r2_hidden(X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,X1_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_1372,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_1066])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_534,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_535,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_536,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_10,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_346,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_347,plain,
    ( ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_351,plain,
    ( ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_26,c_23])).

cnf(c_9,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_144,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_145,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_519,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_145,c_20])).

cnf(c_520,plain,
    ( v3_tex_2(u1_struct_0(sK2),sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_21,negated_conjecture,
    ( v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_522,plain,
    ( v3_tex_2(u1_struct_0(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_520,c_26,c_23,c_21])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK2) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_522])).

cnf(c_575,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_576,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_1148,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1149,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_1620,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1372,c_30,c_39,c_536,c_576,c_1149])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_844,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | m1_subset_1(k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54),k1_zfmisc_1(X1_54)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1065,plain,
    ( r2_hidden(X0_54,X1_54) != iProver_top
    | m1_subset_1(k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54),k1_zfmisc_1(X1_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_844])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_23])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_550])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f91])).

cnf(c_15,negated_conjecture,
    ( v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_321,plain,
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
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_322,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v5_pre_topc(sK3,sK1,sK2)
    | ~ v4_tex_2(sK2,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v3_tdlat_3(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_24,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_17,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_551,c_327])).

cnf(c_834,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54) ),
    inference(subtyping,[status(esa)],[c_569])).

cnf(c_1074,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_1351,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54)) = k2_pre_topc(sK1,k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54))
    | r2_hidden(X0_54,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1065,c_1074])).

cnf(c_1782,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k2_pre_topc(sK1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(superposition,[status(thm)],[c_1620,c_1351])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_839,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1069,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | v1_xboole_0(X1_54)
    | k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1068,plain,
    ( k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54)
    | m1_subset_1(X0_54,X1_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_1489,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_1068])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_842,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X2_54))
    | ~ v1_xboole_0(X2_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1222,plain,
    ( ~ r2_hidden(X0_54,X1_54)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_1326,plain,
    ( ~ r2_hidden(X0_54,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_1423,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_1681,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1489,c_23,c_14,c_13,c_535,c_575,c_1148,c_1183,c_1423])).

cnf(c_1783,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1782,c_1681])).

cnf(c_1490,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1070,c_1068])).

cnf(c_1186,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1689,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1490,c_23,c_14,c_535,c_575,c_1186])).

cnf(c_1691,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(light_normalisation,[status(thm)],[c_1689,c_1681])).

cnf(c_12,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_840,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1693,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(demodulation,[status(thm)],[c_1691,c_840])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1783,c_1693])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.58/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.02  
% 1.58/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.58/1.02  
% 1.58/1.02  ------  iProver source info
% 1.58/1.02  
% 1.58/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.58/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.58/1.02  git: non_committed_changes: false
% 1.58/1.02  git: last_make_outside_of_git: false
% 1.58/1.02  
% 1.58/1.02  ------ 
% 1.58/1.02  
% 1.58/1.02  ------ Input Options
% 1.58/1.02  
% 1.58/1.02  --out_options                           all
% 1.58/1.02  --tptp_safe_out                         true
% 1.58/1.02  --problem_path                          ""
% 1.58/1.02  --include_path                          ""
% 1.58/1.02  --clausifier                            res/vclausify_rel
% 1.58/1.02  --clausifier_options                    --mode clausify
% 1.58/1.02  --stdin                                 false
% 1.58/1.02  --stats_out                             all
% 1.58/1.02  
% 1.58/1.02  ------ General Options
% 1.58/1.02  
% 1.58/1.02  --fof                                   false
% 1.58/1.02  --time_out_real                         305.
% 1.58/1.02  --time_out_virtual                      -1.
% 1.58/1.02  --symbol_type_check                     false
% 1.58/1.02  --clausify_out                          false
% 1.58/1.02  --sig_cnt_out                           false
% 1.58/1.02  --trig_cnt_out                          false
% 1.58/1.02  --trig_cnt_out_tolerance                1.
% 1.58/1.02  --trig_cnt_out_sk_spl                   false
% 1.58/1.02  --abstr_cl_out                          false
% 1.58/1.02  
% 1.58/1.02  ------ Global Options
% 1.58/1.02  
% 1.58/1.02  --schedule                              default
% 1.58/1.02  --add_important_lit                     false
% 1.58/1.02  --prop_solver_per_cl                    1000
% 1.58/1.02  --min_unsat_core                        false
% 1.58/1.02  --soft_assumptions                      false
% 1.58/1.02  --soft_lemma_size                       3
% 1.58/1.02  --prop_impl_unit_size                   0
% 1.58/1.02  --prop_impl_unit                        []
% 1.58/1.02  --share_sel_clauses                     true
% 1.58/1.02  --reset_solvers                         false
% 1.58/1.02  --bc_imp_inh                            [conj_cone]
% 1.58/1.02  --conj_cone_tolerance                   3.
% 1.58/1.02  --extra_neg_conj                        none
% 1.58/1.02  --large_theory_mode                     true
% 1.58/1.02  --prolific_symb_bound                   200
% 1.58/1.02  --lt_threshold                          2000
% 1.58/1.02  --clause_weak_htbl                      true
% 1.58/1.02  --gc_record_bc_elim                     false
% 1.58/1.02  
% 1.58/1.02  ------ Preprocessing Options
% 1.58/1.02  
% 1.58/1.02  --preprocessing_flag                    true
% 1.58/1.02  --time_out_prep_mult                    0.1
% 1.58/1.02  --splitting_mode                        input
% 1.58/1.02  --splitting_grd                         true
% 1.58/1.02  --splitting_cvd                         false
% 1.58/1.02  --splitting_cvd_svl                     false
% 1.58/1.02  --splitting_nvd                         32
% 1.58/1.02  --sub_typing                            true
% 1.58/1.02  --prep_gs_sim                           true
% 1.58/1.02  --prep_unflatten                        true
% 1.58/1.02  --prep_res_sim                          true
% 1.58/1.02  --prep_upred                            true
% 1.58/1.02  --prep_sem_filter                       exhaustive
% 1.58/1.02  --prep_sem_filter_out                   false
% 1.58/1.02  --pred_elim                             true
% 1.58/1.02  --res_sim_input                         true
% 1.58/1.02  --eq_ax_congr_red                       true
% 1.58/1.02  --pure_diseq_elim                       true
% 1.58/1.02  --brand_transform                       false
% 1.58/1.02  --non_eq_to_eq                          false
% 1.58/1.02  --prep_def_merge                        true
% 1.58/1.02  --prep_def_merge_prop_impl              false
% 1.58/1.02  --prep_def_merge_mbd                    true
% 1.58/1.02  --prep_def_merge_tr_red                 false
% 1.58/1.02  --prep_def_merge_tr_cl                  false
% 1.58/1.02  --smt_preprocessing                     true
% 1.58/1.02  --smt_ac_axioms                         fast
% 1.58/1.02  --preprocessed_out                      false
% 1.58/1.02  --preprocessed_stats                    false
% 1.58/1.02  
% 1.58/1.02  ------ Abstraction refinement Options
% 1.58/1.02  
% 1.58/1.02  --abstr_ref                             []
% 1.58/1.02  --abstr_ref_prep                        false
% 1.58/1.02  --abstr_ref_until_sat                   false
% 1.58/1.02  --abstr_ref_sig_restrict                funpre
% 1.58/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/1.02  --abstr_ref_under                       []
% 1.58/1.02  
% 1.58/1.02  ------ SAT Options
% 1.58/1.02  
% 1.58/1.02  --sat_mode                              false
% 1.58/1.02  --sat_fm_restart_options                ""
% 1.58/1.02  --sat_gr_def                            false
% 1.58/1.02  --sat_epr_types                         true
% 1.58/1.02  --sat_non_cyclic_types                  false
% 1.58/1.02  --sat_finite_models                     false
% 1.58/1.02  --sat_fm_lemmas                         false
% 1.58/1.02  --sat_fm_prep                           false
% 1.58/1.02  --sat_fm_uc_incr                        true
% 1.58/1.02  --sat_out_model                         small
% 1.58/1.02  --sat_out_clauses                       false
% 1.58/1.02  
% 1.58/1.02  ------ QBF Options
% 1.58/1.02  
% 1.58/1.02  --qbf_mode                              false
% 1.58/1.02  --qbf_elim_univ                         false
% 1.58/1.02  --qbf_dom_inst                          none
% 1.58/1.02  --qbf_dom_pre_inst                      false
% 1.58/1.02  --qbf_sk_in                             false
% 1.58/1.02  --qbf_pred_elim                         true
% 1.58/1.02  --qbf_split                             512
% 1.58/1.02  
% 1.58/1.02  ------ BMC1 Options
% 1.58/1.02  
% 1.58/1.02  --bmc1_incremental                      false
% 1.58/1.02  --bmc1_axioms                           reachable_all
% 1.58/1.02  --bmc1_min_bound                        0
% 1.58/1.02  --bmc1_max_bound                        -1
% 1.58/1.02  --bmc1_max_bound_default                -1
% 1.58/1.02  --bmc1_symbol_reachability              true
% 1.58/1.02  --bmc1_property_lemmas                  false
% 1.58/1.02  --bmc1_k_induction                      false
% 1.58/1.02  --bmc1_non_equiv_states                 false
% 1.58/1.02  --bmc1_deadlock                         false
% 1.58/1.02  --bmc1_ucm                              false
% 1.58/1.02  --bmc1_add_unsat_core                   none
% 1.58/1.02  --bmc1_unsat_core_children              false
% 1.58/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.02  --bmc1_out_stat                         full
% 1.58/1.02  --bmc1_ground_init                      false
% 1.58/1.02  --bmc1_pre_inst_next_state              false
% 1.58/1.02  --bmc1_pre_inst_state                   false
% 1.58/1.02  --bmc1_pre_inst_reach_state             false
% 1.58/1.02  --bmc1_out_unsat_core                   false
% 1.58/1.02  --bmc1_aig_witness_out                  false
% 1.58/1.02  --bmc1_verbose                          false
% 1.58/1.02  --bmc1_dump_clauses_tptp                false
% 1.58/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.02  --bmc1_dump_file                        -
% 1.58/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.02  --bmc1_ucm_extend_mode                  1
% 1.58/1.02  --bmc1_ucm_init_mode                    2
% 1.58/1.02  --bmc1_ucm_cone_mode                    none
% 1.58/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.02  --bmc1_ucm_relax_model                  4
% 1.58/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.02  --bmc1_ucm_layered_model                none
% 1.58/1.02  --bmc1_ucm_max_lemma_size               10
% 1.58/1.02  
% 1.58/1.02  ------ AIG Options
% 1.58/1.02  
% 1.58/1.02  --aig_mode                              false
% 1.58/1.02  
% 1.58/1.02  ------ Instantiation Options
% 1.58/1.02  
% 1.58/1.02  --instantiation_flag                    true
% 1.58/1.02  --inst_sos_flag                         false
% 1.58/1.02  --inst_sos_phase                        true
% 1.58/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.02  --inst_lit_sel_side                     num_symb
% 1.58/1.02  --inst_solver_per_active                1400
% 1.58/1.02  --inst_solver_calls_frac                1.
% 1.58/1.02  --inst_passive_queue_type               priority_queues
% 1.58/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.02  --inst_passive_queues_freq              [25;2]
% 1.58/1.02  --inst_dismatching                      true
% 1.58/1.02  --inst_eager_unprocessed_to_passive     true
% 1.58/1.02  --inst_prop_sim_given                   true
% 1.58/1.02  --inst_prop_sim_new                     false
% 1.58/1.02  --inst_subs_new                         false
% 1.58/1.02  --inst_eq_res_simp                      false
% 1.58/1.02  --inst_subs_given                       false
% 1.58/1.02  --inst_orphan_elimination               true
% 1.58/1.02  --inst_learning_loop_flag               true
% 1.58/1.02  --inst_learning_start                   3000
% 1.58/1.02  --inst_learning_factor                  2
% 1.58/1.02  --inst_start_prop_sim_after_learn       3
% 1.58/1.02  --inst_sel_renew                        solver
% 1.58/1.02  --inst_lit_activity_flag                true
% 1.58/1.02  --inst_restr_to_given                   false
% 1.58/1.02  --inst_activity_threshold               500
% 1.58/1.02  --inst_out_proof                        true
% 1.58/1.02  
% 1.58/1.02  ------ Resolution Options
% 1.58/1.02  
% 1.58/1.02  --resolution_flag                       true
% 1.58/1.02  --res_lit_sel                           adaptive
% 1.58/1.02  --res_lit_sel_side                      none
% 1.58/1.02  --res_ordering                          kbo
% 1.58/1.02  --res_to_prop_solver                    active
% 1.58/1.02  --res_prop_simpl_new                    false
% 1.58/1.02  --res_prop_simpl_given                  true
% 1.58/1.02  --res_passive_queue_type                priority_queues
% 1.58/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.02  --res_passive_queues_freq               [15;5]
% 1.58/1.02  --res_forward_subs                      full
% 1.58/1.02  --res_backward_subs                     full
% 1.58/1.02  --res_forward_subs_resolution           true
% 1.58/1.02  --res_backward_subs_resolution          true
% 1.58/1.02  --res_orphan_elimination                true
% 1.58/1.02  --res_time_limit                        2.
% 1.58/1.02  --res_out_proof                         true
% 1.58/1.02  
% 1.58/1.02  ------ Superposition Options
% 1.58/1.02  
% 1.58/1.02  --superposition_flag                    true
% 1.58/1.02  --sup_passive_queue_type                priority_queues
% 1.58/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.02  --demod_completeness_check              fast
% 1.58/1.02  --demod_use_ground                      true
% 1.58/1.02  --sup_to_prop_solver                    passive
% 1.58/1.02  --sup_prop_simpl_new                    true
% 1.58/1.02  --sup_prop_simpl_given                  true
% 1.58/1.02  --sup_fun_splitting                     false
% 1.58/1.02  --sup_smt_interval                      50000
% 1.58/1.02  
% 1.58/1.02  ------ Superposition Simplification Setup
% 1.58/1.02  
% 1.58/1.02  --sup_indices_passive                   []
% 1.58/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.02  --sup_full_bw                           [BwDemod]
% 1.58/1.02  --sup_immed_triv                        [TrivRules]
% 1.58/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.02  --sup_immed_bw_main                     []
% 1.58/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.02  
% 1.58/1.02  ------ Combination Options
% 1.58/1.02  
% 1.58/1.02  --comb_res_mult                         3
% 1.58/1.02  --comb_sup_mult                         2
% 1.58/1.02  --comb_inst_mult                        10
% 1.58/1.02  
% 1.58/1.02  ------ Debug Options
% 1.58/1.02  
% 1.58/1.02  --dbg_backtrace                         false
% 1.58/1.02  --dbg_dump_prop_clauses                 false
% 1.58/1.02  --dbg_dump_prop_clauses_file            -
% 1.58/1.02  --dbg_out_stat                          false
% 1.58/1.02  ------ Parsing...
% 1.58/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.58/1.02  
% 1.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.58/1.02  
% 1.58/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.58/1.02  
% 1.58/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.58/1.02  ------ Proving...
% 1.58/1.02  ------ Problem Properties 
% 1.58/1.02  
% 1.58/1.02  
% 1.58/1.02  clauses                                 12
% 1.58/1.02  conjectures                             4
% 1.58/1.02  EPR                                     1
% 1.58/1.02  Horn                                    10
% 1.58/1.02  unary                                   6
% 1.58/1.02  binary                                  3
% 1.58/1.02  lits                                    21
% 1.58/1.02  lits eq                                 3
% 1.58/1.02  fd_pure                                 0
% 1.58/1.02  fd_pseudo                               0
% 1.58/1.02  fd_cond                                 0
% 1.58/1.02  fd_pseudo_cond                          0
% 1.58/1.02  AC symbols                              0
% 1.58/1.02  
% 1.58/1.02  ------ Schedule dynamic 5 is on 
% 1.58/1.02  
% 1.58/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.58/1.02  
% 1.58/1.02  
% 1.58/1.02  ------ 
% 1.58/1.02  Current options:
% 1.58/1.02  ------ 
% 1.58/1.02  
% 1.58/1.02  ------ Input Options
% 1.58/1.02  
% 1.58/1.02  --out_options                           all
% 1.58/1.02  --tptp_safe_out                         true
% 1.58/1.02  --problem_path                          ""
% 1.58/1.02  --include_path                          ""
% 1.58/1.02  --clausifier                            res/vclausify_rel
% 1.58/1.02  --clausifier_options                    --mode clausify
% 1.58/1.02  --stdin                                 false
% 1.58/1.02  --stats_out                             all
% 1.58/1.02  
% 1.58/1.02  ------ General Options
% 1.58/1.02  
% 1.58/1.02  --fof                                   false
% 1.58/1.02  --time_out_real                         305.
% 1.58/1.02  --time_out_virtual                      -1.
% 1.58/1.02  --symbol_type_check                     false
% 1.58/1.02  --clausify_out                          false
% 1.58/1.02  --sig_cnt_out                           false
% 1.58/1.02  --trig_cnt_out                          false
% 1.58/1.02  --trig_cnt_out_tolerance                1.
% 1.58/1.02  --trig_cnt_out_sk_spl                   false
% 1.58/1.02  --abstr_cl_out                          false
% 1.58/1.02  
% 1.58/1.02  ------ Global Options
% 1.58/1.02  
% 1.58/1.02  --schedule                              default
% 1.58/1.02  --add_important_lit                     false
% 1.58/1.02  --prop_solver_per_cl                    1000
% 1.58/1.02  --min_unsat_core                        false
% 1.58/1.02  --soft_assumptions                      false
% 1.58/1.02  --soft_lemma_size                       3
% 1.58/1.02  --prop_impl_unit_size                   0
% 1.58/1.02  --prop_impl_unit                        []
% 1.58/1.02  --share_sel_clauses                     true
% 1.58/1.02  --reset_solvers                         false
% 1.58/1.02  --bc_imp_inh                            [conj_cone]
% 1.58/1.02  --conj_cone_tolerance                   3.
% 1.58/1.02  --extra_neg_conj                        none
% 1.58/1.02  --large_theory_mode                     true
% 1.58/1.02  --prolific_symb_bound                   200
% 1.58/1.02  --lt_threshold                          2000
% 1.58/1.02  --clause_weak_htbl                      true
% 1.58/1.02  --gc_record_bc_elim                     false
% 1.58/1.02  
% 1.58/1.02  ------ Preprocessing Options
% 1.58/1.02  
% 1.58/1.02  --preprocessing_flag                    true
% 1.58/1.02  --time_out_prep_mult                    0.1
% 1.58/1.02  --splitting_mode                        input
% 1.58/1.02  --splitting_grd                         true
% 1.58/1.02  --splitting_cvd                         false
% 1.58/1.02  --splitting_cvd_svl                     false
% 1.58/1.02  --splitting_nvd                         32
% 1.58/1.02  --sub_typing                            true
% 1.58/1.02  --prep_gs_sim                           true
% 1.58/1.02  --prep_unflatten                        true
% 1.58/1.02  --prep_res_sim                          true
% 1.58/1.02  --prep_upred                            true
% 1.58/1.02  --prep_sem_filter                       exhaustive
% 1.58/1.02  --prep_sem_filter_out                   false
% 1.58/1.02  --pred_elim                             true
% 1.58/1.02  --res_sim_input                         true
% 1.58/1.02  --eq_ax_congr_red                       true
% 1.58/1.02  --pure_diseq_elim                       true
% 1.58/1.02  --brand_transform                       false
% 1.58/1.02  --non_eq_to_eq                          false
% 1.58/1.02  --prep_def_merge                        true
% 1.58/1.02  --prep_def_merge_prop_impl              false
% 1.58/1.02  --prep_def_merge_mbd                    true
% 1.58/1.02  --prep_def_merge_tr_red                 false
% 1.58/1.02  --prep_def_merge_tr_cl                  false
% 1.58/1.02  --smt_preprocessing                     true
% 1.58/1.02  --smt_ac_axioms                         fast
% 1.58/1.02  --preprocessed_out                      false
% 1.58/1.02  --preprocessed_stats                    false
% 1.58/1.02  
% 1.58/1.02  ------ Abstraction refinement Options
% 1.58/1.02  
% 1.58/1.02  --abstr_ref                             []
% 1.58/1.02  --abstr_ref_prep                        false
% 1.58/1.02  --abstr_ref_until_sat                   false
% 1.58/1.02  --abstr_ref_sig_restrict                funpre
% 1.58/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.58/1.02  --abstr_ref_under                       []
% 1.58/1.02  
% 1.58/1.02  ------ SAT Options
% 1.58/1.02  
% 1.58/1.02  --sat_mode                              false
% 1.58/1.02  --sat_fm_restart_options                ""
% 1.58/1.02  --sat_gr_def                            false
% 1.58/1.02  --sat_epr_types                         true
% 1.58/1.02  --sat_non_cyclic_types                  false
% 1.58/1.02  --sat_finite_models                     false
% 1.58/1.02  --sat_fm_lemmas                         false
% 1.58/1.02  --sat_fm_prep                           false
% 1.58/1.02  --sat_fm_uc_incr                        true
% 1.58/1.02  --sat_out_model                         small
% 1.58/1.02  --sat_out_clauses                       false
% 1.58/1.02  
% 1.58/1.02  ------ QBF Options
% 1.58/1.02  
% 1.58/1.02  --qbf_mode                              false
% 1.58/1.02  --qbf_elim_univ                         false
% 1.58/1.02  --qbf_dom_inst                          none
% 1.58/1.02  --qbf_dom_pre_inst                      false
% 1.58/1.02  --qbf_sk_in                             false
% 1.58/1.02  --qbf_pred_elim                         true
% 1.58/1.02  --qbf_split                             512
% 1.58/1.02  
% 1.58/1.02  ------ BMC1 Options
% 1.58/1.02  
% 1.58/1.02  --bmc1_incremental                      false
% 1.58/1.02  --bmc1_axioms                           reachable_all
% 1.58/1.02  --bmc1_min_bound                        0
% 1.58/1.02  --bmc1_max_bound                        -1
% 1.58/1.02  --bmc1_max_bound_default                -1
% 1.58/1.02  --bmc1_symbol_reachability              true
% 1.58/1.02  --bmc1_property_lemmas                  false
% 1.58/1.02  --bmc1_k_induction                      false
% 1.58/1.02  --bmc1_non_equiv_states                 false
% 1.58/1.02  --bmc1_deadlock                         false
% 1.58/1.02  --bmc1_ucm                              false
% 1.58/1.02  --bmc1_add_unsat_core                   none
% 1.58/1.02  --bmc1_unsat_core_children              false
% 1.58/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.58/1.02  --bmc1_out_stat                         full
% 1.58/1.02  --bmc1_ground_init                      false
% 1.58/1.02  --bmc1_pre_inst_next_state              false
% 1.58/1.02  --bmc1_pre_inst_state                   false
% 1.58/1.02  --bmc1_pre_inst_reach_state             false
% 1.58/1.02  --bmc1_out_unsat_core                   false
% 1.58/1.02  --bmc1_aig_witness_out                  false
% 1.58/1.02  --bmc1_verbose                          false
% 1.58/1.02  --bmc1_dump_clauses_tptp                false
% 1.58/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.58/1.02  --bmc1_dump_file                        -
% 1.58/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.58/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.58/1.02  --bmc1_ucm_extend_mode                  1
% 1.58/1.02  --bmc1_ucm_init_mode                    2
% 1.58/1.02  --bmc1_ucm_cone_mode                    none
% 1.58/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.58/1.02  --bmc1_ucm_relax_model                  4
% 1.58/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.58/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.58/1.02  --bmc1_ucm_layered_model                none
% 1.58/1.02  --bmc1_ucm_max_lemma_size               10
% 1.58/1.02  
% 1.58/1.02  ------ AIG Options
% 1.58/1.02  
% 1.58/1.02  --aig_mode                              false
% 1.58/1.02  
% 1.58/1.02  ------ Instantiation Options
% 1.58/1.02  
% 1.58/1.02  --instantiation_flag                    true
% 1.58/1.02  --inst_sos_flag                         false
% 1.58/1.02  --inst_sos_phase                        true
% 1.58/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.58/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.58/1.02  --inst_lit_sel_side                     none
% 1.58/1.02  --inst_solver_per_active                1400
% 1.58/1.02  --inst_solver_calls_frac                1.
% 1.58/1.02  --inst_passive_queue_type               priority_queues
% 1.58/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.58/1.02  --inst_passive_queues_freq              [25;2]
% 1.58/1.02  --inst_dismatching                      true
% 1.58/1.02  --inst_eager_unprocessed_to_passive     true
% 1.58/1.02  --inst_prop_sim_given                   true
% 1.58/1.02  --inst_prop_sim_new                     false
% 1.58/1.02  --inst_subs_new                         false
% 1.58/1.02  --inst_eq_res_simp                      false
% 1.58/1.02  --inst_subs_given                       false
% 1.58/1.02  --inst_orphan_elimination               true
% 1.58/1.02  --inst_learning_loop_flag               true
% 1.58/1.02  --inst_learning_start                   3000
% 1.58/1.02  --inst_learning_factor                  2
% 1.58/1.02  --inst_start_prop_sim_after_learn       3
% 1.58/1.02  --inst_sel_renew                        solver
% 1.58/1.02  --inst_lit_activity_flag                true
% 1.58/1.02  --inst_restr_to_given                   false
% 1.58/1.02  --inst_activity_threshold               500
% 1.58/1.02  --inst_out_proof                        true
% 1.58/1.02  
% 1.58/1.02  ------ Resolution Options
% 1.58/1.02  
% 1.58/1.02  --resolution_flag                       false
% 1.58/1.02  --res_lit_sel                           adaptive
% 1.58/1.02  --res_lit_sel_side                      none
% 1.58/1.02  --res_ordering                          kbo
% 1.58/1.02  --res_to_prop_solver                    active
% 1.58/1.02  --res_prop_simpl_new                    false
% 1.58/1.02  --res_prop_simpl_given                  true
% 1.58/1.02  --res_passive_queue_type                priority_queues
% 1.58/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.58/1.02  --res_passive_queues_freq               [15;5]
% 1.58/1.02  --res_forward_subs                      full
% 1.58/1.02  --res_backward_subs                     full
% 1.58/1.02  --res_forward_subs_resolution           true
% 1.58/1.02  --res_backward_subs_resolution          true
% 1.58/1.02  --res_orphan_elimination                true
% 1.58/1.02  --res_time_limit                        2.
% 1.58/1.02  --res_out_proof                         true
% 1.58/1.02  
% 1.58/1.02  ------ Superposition Options
% 1.58/1.02  
% 1.58/1.02  --superposition_flag                    true
% 1.58/1.02  --sup_passive_queue_type                priority_queues
% 1.58/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.58/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.58/1.02  --demod_completeness_check              fast
% 1.58/1.02  --demod_use_ground                      true
% 1.58/1.02  --sup_to_prop_solver                    passive
% 1.58/1.02  --sup_prop_simpl_new                    true
% 1.58/1.02  --sup_prop_simpl_given                  true
% 1.58/1.02  --sup_fun_splitting                     false
% 1.58/1.02  --sup_smt_interval                      50000
% 1.58/1.02  
% 1.58/1.02  ------ Superposition Simplification Setup
% 1.58/1.02  
% 1.58/1.02  --sup_indices_passive                   []
% 1.58/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.58/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.58/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.02  --sup_full_bw                           [BwDemod]
% 1.58/1.02  --sup_immed_triv                        [TrivRules]
% 1.58/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.58/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.02  --sup_immed_bw_main                     []
% 1.58/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.58/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.58/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.58/1.02  
% 1.58/1.02  ------ Combination Options
% 1.58/1.02  
% 1.58/1.02  --comb_res_mult                         3
% 1.58/1.02  --comb_sup_mult                         2
% 1.58/1.02  --comb_inst_mult                        10
% 1.58/1.02  
% 1.58/1.02  ------ Debug Options
% 1.58/1.02  
% 1.58/1.02  --dbg_backtrace                         false
% 1.58/1.02  --dbg_dump_prop_clauses                 false
% 1.58/1.02  --dbg_dump_prop_clauses_file            -
% 1.58/1.02  --dbg_out_stat                          false
% 1.58/1.02  
% 1.58/1.02  
% 1.58/1.02  
% 1.58/1.02  
% 1.58/1.02  ------ Proving...
% 1.58/1.02  
% 1.58/1.02  
% 1.58/1.02  % SZS status Theorem for theBenchmark.p
% 1.58/1.02  
% 1.58/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.58/1.02  
% 1.58/1.02  fof(f76,plain,(
% 1.58/1.02    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f17,conjecture,(
% 1.58/1.02    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f18,negated_conjecture,(
% 1.58/1.02    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.58/1.02    inference(negated_conjecture,[],[f17])).
% 1.58/1.02  
% 1.58/1.02  fof(f33,plain,(
% 1.58/1.02    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.58/1.02    inference(ennf_transformation,[],[f18])).
% 1.58/1.02  
% 1.58/1.02  fof(f34,plain,(
% 1.58/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.58/1.02    inference(flattening,[],[f33])).
% 1.58/1.02  
% 1.58/1.02  fof(f43,plain,(
% 1.58/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) & sK5 = X3 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.58/1.02    introduced(choice_axiom,[])).
% 1.58/1.02  
% 1.58/1.02  fof(f42,plain,(
% 1.58/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK4 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.58/1.02    introduced(choice_axiom,[])).
% 1.58/1.02  
% 1.58/1.02  fof(f41,plain,(
% 1.58/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK3,X0,X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK3,X0,X1) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.58/1.02    introduced(choice_axiom,[])).
% 1.58/1.02  
% 1.58/1.02  fof(f40,plain,(
% 1.58/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(X2,X0,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v5_pre_topc(X2,X0,sK2) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & v4_tex_2(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.58/1.02    introduced(choice_axiom,[])).
% 1.58/1.02  
% 1.58/1.02  fof(f39,plain,(
% 1.58/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X2,sK1,X1) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & v4_tex_2(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.58/1.02    introduced(choice_axiom,[])).
% 1.58/1.02  
% 1.58/1.02  fof(f44,plain,(
% 1.58/1.02    ((((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2))) & v3_borsuk_1(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & v4_tex_2(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.58/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f34,f43,f42,f41,f40,f39])).
% 1.58/1.02  
% 1.58/1.02  fof(f78,plain,(
% 1.58/1.02    sK4 = sK5),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f89,plain,(
% 1.58/1.02    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.58/1.02    inference(definition_unfolding,[],[f76,f78])).
% 1.58/1.02  
% 1.58/1.02  fof(f9,axiom,(
% 1.58/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f20,plain,(
% 1.58/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.58/1.02    inference(ennf_transformation,[],[f9])).
% 1.58/1.02  
% 1.58/1.02  fof(f21,plain,(
% 1.58/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.58/1.02    inference(flattening,[],[f20])).
% 1.58/1.02  
% 1.58/1.02  fof(f53,plain,(
% 1.58/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f21])).
% 1.58/1.02  
% 1.58/1.02  fof(f67,plain,(
% 1.58/1.02    l1_pre_topc(sK1)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f13,axiom,(
% 1.58/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f26,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.58/1.02    inference(ennf_transformation,[],[f13])).
% 1.58/1.02  
% 1.58/1.02  fof(f57,plain,(
% 1.58/1.02    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f26])).
% 1.58/1.02  
% 1.58/1.02  fof(f70,plain,(
% 1.58/1.02    m1_pre_topc(sK2,sK1)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f15,axiom,(
% 1.58/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f29,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/1.02    inference(ennf_transformation,[],[f15])).
% 1.58/1.02  
% 1.58/1.02  fof(f30,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/1.02    inference(flattening,[],[f29])).
% 1.58/1.02  
% 1.58/1.02  fof(f62,plain,(
% 1.58/1.02    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f30])).
% 1.58/1.02  
% 1.58/1.02  fof(f65,plain,(
% 1.58/1.02    v2_pre_topc(sK1)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f64,plain,(
% 1.58/1.02    ~v2_struct_0(sK1)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f14,axiom,(
% 1.58/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f27,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/1.02    inference(ennf_transformation,[],[f14])).
% 1.58/1.02  
% 1.58/1.02  fof(f28,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/1.02    inference(flattening,[],[f27])).
% 1.58/1.02  
% 1.58/1.02  fof(f35,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/1.02    inference(nnf_transformation,[],[f28])).
% 1.58/1.02  
% 1.58/1.02  fof(f36,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/1.02    inference(rectify,[],[f35])).
% 1.58/1.02  
% 1.58/1.02  fof(f37,plain,(
% 1.58/1.02    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.58/1.02    introduced(choice_axiom,[])).
% 1.58/1.02  
% 1.58/1.02  fof(f38,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 1.58/1.02  
% 1.58/1.02  fof(f58,plain,(
% 1.58/1.02    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f38])).
% 1.58/1.02  
% 1.58/1.02  fof(f90,plain,(
% 1.58/1.02    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/1.02    inference(equality_resolution,[],[f58])).
% 1.58/1.02  
% 1.58/1.02  fof(f69,plain,(
% 1.58/1.02    v4_tex_2(sK2,sK1)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f8,axiom,(
% 1.58/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f19,plain,(
% 1.58/1.02    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.58/1.02    inference(ennf_transformation,[],[f8])).
% 1.58/1.02  
% 1.58/1.02  fof(f52,plain,(
% 1.58/1.02    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f19])).
% 1.58/1.02  
% 1.58/1.02  fof(f1,axiom,(
% 1.58/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f45,plain,(
% 1.58/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f1])).
% 1.58/1.02  
% 1.58/1.02  fof(f2,axiom,(
% 1.58/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f46,plain,(
% 1.58/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f2])).
% 1.58/1.02  
% 1.58/1.02  fof(f3,axiom,(
% 1.58/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f47,plain,(
% 1.58/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f3])).
% 1.58/1.02  
% 1.58/1.02  fof(f4,axiom,(
% 1.58/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f48,plain,(
% 1.58/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f4])).
% 1.58/1.02  
% 1.58/1.02  fof(f5,axiom,(
% 1.58/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f49,plain,(
% 1.58/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f5])).
% 1.58/1.02  
% 1.58/1.02  fof(f6,axiom,(
% 1.58/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f50,plain,(
% 1.58/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f6])).
% 1.58/1.02  
% 1.58/1.02  fof(f7,axiom,(
% 1.58/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f51,plain,(
% 1.58/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f7])).
% 1.58/1.02  
% 1.58/1.02  fof(f80,plain,(
% 1.58/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f50,f51])).
% 1.58/1.02  
% 1.58/1.02  fof(f81,plain,(
% 1.58/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f49,f80])).
% 1.58/1.02  
% 1.58/1.02  fof(f82,plain,(
% 1.58/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f48,f81])).
% 1.58/1.02  
% 1.58/1.02  fof(f83,plain,(
% 1.58/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f47,f82])).
% 1.58/1.02  
% 1.58/1.02  fof(f84,plain,(
% 1.58/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f46,f83])).
% 1.58/1.02  
% 1.58/1.02  fof(f85,plain,(
% 1.58/1.02    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f45,f84])).
% 1.58/1.02  
% 1.58/1.02  fof(f86,plain,(
% 1.58/1.02    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f52,f85])).
% 1.58/1.02  
% 1.58/1.02  fof(f11,axiom,(
% 1.58/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f23,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.58/1.02    inference(ennf_transformation,[],[f11])).
% 1.58/1.02  
% 1.58/1.02  fof(f55,plain,(
% 1.58/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f23])).
% 1.58/1.02  
% 1.58/1.02  fof(f16,axiom,(
% 1.58/1.02    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f31,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.58/1.02    inference(ennf_transformation,[],[f16])).
% 1.58/1.02  
% 1.58/1.02  fof(f32,plain,(
% 1.58/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.58/1.02    inference(flattening,[],[f31])).
% 1.58/1.02  
% 1.58/1.02  fof(f63,plain,(
% 1.58/1.02    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f32])).
% 1.58/1.02  
% 1.58/1.02  fof(f91,plain,(
% 1.58/1.02    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.58/1.02    inference(equality_resolution,[],[f63])).
% 1.58/1.02  
% 1.58/1.02  fof(f75,plain,(
% 1.58/1.02    v3_borsuk_1(sK3,sK1,sK2)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f66,plain,(
% 1.58/1.02    v3_tdlat_3(sK1)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f68,plain,(
% 1.58/1.02    ~v2_struct_0(sK2)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f71,plain,(
% 1.58/1.02    v1_funct_1(sK3)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f72,plain,(
% 1.58/1.02    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f73,plain,(
% 1.58/1.02    v5_pre_topc(sK3,sK1,sK2)),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f74,plain,(
% 1.58/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f77,plain,(
% 1.58/1.02    m1_subset_1(sK5,u1_struct_0(sK1))),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f12,axiom,(
% 1.58/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f24,plain,(
% 1.58/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.58/1.02    inference(ennf_transformation,[],[f12])).
% 1.58/1.02  
% 1.58/1.02  fof(f25,plain,(
% 1.58/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.58/1.02    inference(flattening,[],[f24])).
% 1.58/1.02  
% 1.58/1.02  fof(f56,plain,(
% 1.58/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f25])).
% 1.58/1.02  
% 1.58/1.02  fof(f87,plain,(
% 1.58/1.02    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.58/1.02    inference(definition_unfolding,[],[f56,f85])).
% 1.58/1.02  
% 1.58/1.02  fof(f10,axiom,(
% 1.58/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.58/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.58/1.02  
% 1.58/1.02  fof(f22,plain,(
% 1.58/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.58/1.02    inference(ennf_transformation,[],[f10])).
% 1.58/1.02  
% 1.58/1.02  fof(f54,plain,(
% 1.58/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.58/1.02    inference(cnf_transformation,[],[f22])).
% 1.58/1.02  
% 1.58/1.02  fof(f79,plain,(
% 1.58/1.02    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 1.58/1.02    inference(cnf_transformation,[],[f44])).
% 1.58/1.02  
% 1.58/1.02  fof(f88,plain,(
% 1.58/1.02    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 1.58/1.02    inference(definition_unfolding,[],[f79,f78])).
% 1.58/1.02  
% 1.58/1.02  cnf(c_14,negated_conjecture,
% 1.58/1.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.58/1.02      inference(cnf_transformation,[],[f89]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_838,negated_conjecture,
% 1.58/1.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.58/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_1070,plain,
% 1.58/1.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.58/1.02      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_1,plain,
% 1.58/1.02      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.58/1.02      inference(cnf_transformation,[],[f53]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_843,plain,
% 1.58/1.02      ( r2_hidden(X0_54,X1_54)
% 1.58/1.02      | ~ m1_subset_1(X0_54,X1_54)
% 1.58/1.02      | v1_xboole_0(X1_54) ),
% 1.58/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_1066,plain,
% 1.58/1.02      ( r2_hidden(X0_54,X1_54) = iProver_top
% 1.58/1.02      | m1_subset_1(X0_54,X1_54) != iProver_top
% 1.58/1.02      | v1_xboole_0(X1_54) = iProver_top ),
% 1.58/1.02      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_1372,plain,
% 1.58/1.02      ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top
% 1.58/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.58/1.02      inference(superposition,[status(thm)],[c_1070,c_1066]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_23,negated_conjecture,
% 1.58/1.02      ( l1_pre_topc(sK1) ),
% 1.58/1.02      inference(cnf_transformation,[],[f67]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_30,plain,
% 1.58/1.02      ( l1_pre_topc(sK1) = iProver_top ),
% 1.58/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_39,plain,
% 1.58/1.02      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.58/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.58/1.02  
% 1.58/1.02  cnf(c_5,plain,
% 1.58/1.02      ( ~ m1_pre_topc(X0,X1)
% 1.58/1.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | ~ l1_pre_topc(X1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_20,negated_conjecture,
% 1.58/1.03      ( m1_pre_topc(sK2,sK1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_534,plain,
% 1.58/1.03      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | ~ l1_pre_topc(X1)
% 1.58/1.03      | sK2 != X0
% 1.58/1.03      | sK1 != X1 ),
% 1.58/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_535,plain,
% 1.58/1.03      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ l1_pre_topc(sK1) ),
% 1.58/1.03      inference(unflattening,[status(thm)],[c_534]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_536,plain,
% 1.58/1.03      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.58/1.03      | l1_pre_topc(sK1) != iProver_top ),
% 1.58/1.03      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_10,plain,
% 1.58/1.03      ( ~ v3_tex_2(X0,X1)
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | ~ v2_pre_topc(X1)
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | ~ l1_pre_topc(X1)
% 1.58/1.03      | ~ v1_xboole_0(X0) ),
% 1.58/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_25,negated_conjecture,
% 1.58/1.03      ( v2_pre_topc(sK1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f65]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_346,plain,
% 1.58/1.03      ( ~ v3_tex_2(X0,X1)
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | ~ l1_pre_topc(X1)
% 1.58/1.03      | ~ v1_xboole_0(X0)
% 1.58/1.03      | sK1 != X1 ),
% 1.58/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_347,plain,
% 1.58/1.03      ( ~ v3_tex_2(X0,sK1)
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | v2_struct_0(sK1)
% 1.58/1.03      | ~ l1_pre_topc(sK1)
% 1.58/1.03      | ~ v1_xboole_0(X0) ),
% 1.58/1.03      inference(unflattening,[status(thm)],[c_346]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_26,negated_conjecture,
% 1.58/1.03      ( ~ v2_struct_0(sK1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_351,plain,
% 1.58/1.03      ( ~ v3_tex_2(X0,sK1)
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ v1_xboole_0(X0) ),
% 1.58/1.03      inference(global_propositional_subsumption,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_347,c_26,c_23]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_9,plain,
% 1.58/1.03      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.58/1.03      | ~ v4_tex_2(X0,X1)
% 1.58/1.03      | ~ m1_pre_topc(X0,X1)
% 1.58/1.03      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | ~ l1_pre_topc(X1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_144,plain,
% 1.58/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.58/1.03      | ~ v4_tex_2(X0,X1)
% 1.58/1.03      | v3_tex_2(u1_struct_0(X0),X1)
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | ~ l1_pre_topc(X1) ),
% 1.58/1.03      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_145,plain,
% 1.58/1.03      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.58/1.03      | ~ v4_tex_2(X0,X1)
% 1.58/1.03      | ~ m1_pre_topc(X0,X1)
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | ~ l1_pre_topc(X1) ),
% 1.58/1.03      inference(renaming,[status(thm)],[c_144]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_519,plain,
% 1.58/1.03      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.58/1.03      | ~ v4_tex_2(X0,X1)
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | ~ l1_pre_topc(X1)
% 1.58/1.03      | sK2 != X0
% 1.58/1.03      | sK1 != X1 ),
% 1.58/1.03      inference(resolution_lifted,[status(thm)],[c_145,c_20]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_520,plain,
% 1.58/1.03      ( v3_tex_2(u1_struct_0(sK2),sK1)
% 1.58/1.03      | ~ v4_tex_2(sK2,sK1)
% 1.58/1.03      | v2_struct_0(sK1)
% 1.58/1.03      | ~ l1_pre_topc(sK1) ),
% 1.58/1.03      inference(unflattening,[status(thm)],[c_519]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_21,negated_conjecture,
% 1.58/1.03      ( v4_tex_2(sK2,sK1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_522,plain,
% 1.58/1.03      ( v3_tex_2(u1_struct_0(sK2),sK1) ),
% 1.58/1.03      inference(global_propositional_subsumption,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_520,c_26,c_23,c_21]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_574,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ v1_xboole_0(X0)
% 1.58/1.03      | u1_struct_0(sK2) != X0
% 1.58/1.03      | sK1 != sK1 ),
% 1.58/1.03      inference(resolution_lifted,[status(thm)],[c_351,c_522]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_575,plain,
% 1.58/1.03      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.58/1.03      inference(unflattening,[status(thm)],[c_574]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_576,plain,
% 1.58/1.03      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.58/1.03      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 1.58/1.03      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1148,plain,
% 1.58/1.03      ( r2_hidden(sK5,u1_struct_0(sK2))
% 1.58/1.03      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 1.58/1.03      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.58/1.03      inference(instantiation,[status(thm)],[c_843]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1149,plain,
% 1.58/1.03      ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top
% 1.58/1.03      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 1.58/1.03      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.58/1.03      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1620,plain,
% 1.58/1.03      ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.58/1.03      inference(global_propositional_subsumption,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_1372,c_30,c_39,c_536,c_576,c_1149]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_0,plain,
% 1.58/1.03      ( ~ r2_hidden(X0,X1)
% 1.58/1.03      | m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) ),
% 1.58/1.03      inference(cnf_transformation,[],[f86]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_844,plain,
% 1.58/1.03      ( ~ r2_hidden(X0_54,X1_54)
% 1.58/1.03      | m1_subset_1(k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54),k1_zfmisc_1(X1_54)) ),
% 1.58/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1065,plain,
% 1.58/1.03      ( r2_hidden(X0_54,X1_54) != iProver_top
% 1.58/1.03      | m1_subset_1(k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54),k1_zfmisc_1(X1_54)) = iProver_top ),
% 1.58/1.03      inference(predicate_to_equality,[status(thm)],[c_844]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_3,plain,
% 1.58/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.58/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.58/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | ~ l1_pre_topc(X1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_545,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.58/1.03      | ~ l1_pre_topc(X2)
% 1.58/1.03      | sK2 != X1
% 1.58/1.03      | sK1 != X2 ),
% 1.58/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_546,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.58/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ l1_pre_topc(sK1) ),
% 1.58/1.03      inference(unflattening,[status(thm)],[c_545]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_550,plain,
% 1.58/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.58/1.03      inference(global_propositional_subsumption,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_546,c_23]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_551,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.58/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.58/1.03      inference(renaming,[status(thm)],[c_550]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_11,plain,
% 1.58/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.58/1.03      | ~ v5_pre_topc(X0,X1,X2)
% 1.58/1.03      | ~ v3_borsuk_1(X0,X1,X2)
% 1.58/1.03      | ~ v4_tex_2(X2,X1)
% 1.58/1.03      | ~ m1_pre_topc(X2,X1)
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.58/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.58/1.03      | ~ v3_tdlat_3(X1)
% 1.58/1.03      | ~ v1_funct_1(X0)
% 1.58/1.03      | ~ v2_pre_topc(X1)
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | v2_struct_0(X2)
% 1.58/1.03      | ~ l1_pre_topc(X1)
% 1.58/1.03      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 1.58/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_15,negated_conjecture,
% 1.58/1.03      ( v3_borsuk_1(sK3,sK1,sK2) ),
% 1.58/1.03      inference(cnf_transformation,[],[f75]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_321,plain,
% 1.58/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.58/1.03      | ~ v5_pre_topc(X0,X1,X2)
% 1.58/1.03      | ~ v4_tex_2(X2,X1)
% 1.58/1.03      | ~ m1_pre_topc(X2,X1)
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.58/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.58/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.58/1.03      | ~ v3_tdlat_3(X1)
% 1.58/1.03      | ~ v1_funct_1(X0)
% 1.58/1.03      | ~ v2_pre_topc(X1)
% 1.58/1.03      | v2_struct_0(X1)
% 1.58/1.03      | v2_struct_0(X2)
% 1.58/1.03      | ~ l1_pre_topc(X1)
% 1.58/1.03      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 1.58/1.03      | sK3 != X0
% 1.58/1.03      | sK2 != X2
% 1.58/1.03      | sK1 != X1 ),
% 1.58/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_322,plain,
% 1.58/1.03      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.58/1.03      | ~ v5_pre_topc(sK3,sK1,sK2)
% 1.58/1.03      | ~ v4_tex_2(sK2,sK1)
% 1.58/1.03      | ~ m1_pre_topc(sK2,sK1)
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.58/1.03      | ~ v3_tdlat_3(sK1)
% 1.58/1.03      | ~ v1_funct_1(sK3)
% 1.58/1.03      | ~ v2_pre_topc(sK1)
% 1.58/1.03      | v2_struct_0(sK2)
% 1.58/1.03      | v2_struct_0(sK1)
% 1.58/1.03      | ~ l1_pre_topc(sK1)
% 1.58/1.03      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 1.58/1.03      inference(unflattening,[status(thm)],[c_321]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_24,negated_conjecture,
% 1.58/1.03      ( v3_tdlat_3(sK1) ),
% 1.58/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_22,negated_conjecture,
% 1.58/1.03      ( ~ v2_struct_0(sK2) ),
% 1.58/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_19,negated_conjecture,
% 1.58/1.03      ( v1_funct_1(sK3) ),
% 1.58/1.03      inference(cnf_transformation,[],[f71]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_18,negated_conjecture,
% 1.58/1.03      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 1.58/1.03      inference(cnf_transformation,[],[f72]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_17,negated_conjecture,
% 1.58/1.03      ( v5_pre_topc(sK3,sK1,sK2) ),
% 1.58/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_16,negated_conjecture,
% 1.58/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.58/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_326,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.58/1.03      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 1.58/1.03      inference(global_propositional_subsumption,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_322,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,
% 1.58/1.03                 c_16]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_327,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.58/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 1.58/1.03      inference(renaming,[status(thm)],[c_326]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_569,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.58/1.03      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 1.58/1.03      inference(backward_subsumption_resolution,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_551,c_327]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_834,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.58/1.03      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54) ),
% 1.58/1.03      inference(subtyping,[status(esa)],[c_569]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1074,plain,
% 1.58/1.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54)
% 1.58/1.03      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.58/1.03      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1351,plain,
% 1.58/1.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54)) = k2_pre_topc(sK1,k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54))
% 1.58/1.03      | r2_hidden(X0_54,u1_struct_0(sK2)) != iProver_top ),
% 1.58/1.03      inference(superposition,[status(thm)],[c_1065,c_1074]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1782,plain,
% 1.58/1.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = k2_pre_topc(sK1,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 1.58/1.03      inference(superposition,[status(thm)],[c_1620,c_1351]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_13,negated_conjecture,
% 1.58/1.03      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.58/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_839,negated_conjecture,
% 1.58/1.03      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.58/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1069,plain,
% 1.58/1.03      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 1.58/1.03      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_4,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0,X1)
% 1.58/1.03      | v1_xboole_0(X1)
% 1.58/1.03      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 1.58/1.03      inference(cnf_transformation,[],[f87]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_841,plain,
% 1.58/1.03      ( ~ m1_subset_1(X0_54,X1_54)
% 1.58/1.03      | v1_xboole_0(X1_54)
% 1.58/1.03      | k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54) ),
% 1.58/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1068,plain,
% 1.58/1.03      ( k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54)
% 1.58/1.03      | m1_subset_1(X0_54,X1_54) != iProver_top
% 1.58/1.03      | v1_xboole_0(X1_54) = iProver_top ),
% 1.58/1.03      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1489,plain,
% 1.58/1.03      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
% 1.58/1.03      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.58/1.03      inference(superposition,[status(thm)],[c_1069,c_1068]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1183,plain,
% 1.58/1.03      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 1.58/1.03      | v1_xboole_0(u1_struct_0(sK1))
% 1.58/1.03      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
% 1.58/1.03      inference(instantiation,[status(thm)],[c_841]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_2,plain,
% 1.58/1.03      ( ~ r2_hidden(X0,X1)
% 1.58/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.58/1.03      | ~ v1_xboole_0(X2) ),
% 1.58/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_842,plain,
% 1.58/1.03      ( ~ r2_hidden(X0_54,X1_54)
% 1.58/1.03      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X2_54))
% 1.58/1.03      | ~ v1_xboole_0(X2_54) ),
% 1.58/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1222,plain,
% 1.58/1.03      ( ~ r2_hidden(X0_54,X1_54)
% 1.58/1.03      | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.58/1.03      inference(instantiation,[status(thm)],[c_842]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1326,plain,
% 1.58/1.03      ( ~ r2_hidden(X0_54,u1_struct_0(sK2))
% 1.58/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.58/1.03      inference(instantiation,[status(thm)],[c_1222]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1423,plain,
% 1.58/1.03      ( ~ r2_hidden(sK5,u1_struct_0(sK2))
% 1.58/1.03      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.58/1.03      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.58/1.03      inference(instantiation,[status(thm)],[c_1326]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1681,plain,
% 1.58/1.03      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
% 1.58/1.03      inference(global_propositional_subsumption,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_1489,c_23,c_14,c_13,c_535,c_575,c_1148,c_1183,c_1423]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1783,plain,
% 1.58/1.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 1.58/1.03      inference(light_normalisation,[status(thm)],[c_1782,c_1681]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1490,plain,
% 1.58/1.03      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5)
% 1.58/1.03      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.58/1.03      inference(superposition,[status(thm)],[c_1070,c_1068]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1186,plain,
% 1.58/1.03      ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 1.58/1.03      | v1_xboole_0(u1_struct_0(sK2))
% 1.58/1.03      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 1.58/1.03      inference(instantiation,[status(thm)],[c_841]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1689,plain,
% 1.58/1.03      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 1.58/1.03      inference(global_propositional_subsumption,
% 1.58/1.03                [status(thm)],
% 1.58/1.03                [c_1490,c_23,c_14,c_535,c_575,c_1186]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1691,plain,
% 1.58/1.03      ( k6_domain_1(u1_struct_0(sK1),sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 1.58/1.03      inference(light_normalisation,[status(thm)],[c_1689,c_1681]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_12,negated_conjecture,
% 1.58/1.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 1.58/1.03      inference(cnf_transformation,[],[f88]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_840,negated_conjecture,
% 1.58/1.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 1.58/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(c_1693,plain,
% 1.58/1.03      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 1.58/1.03      inference(demodulation,[status(thm)],[c_1691,c_840]) ).
% 1.58/1.03  
% 1.58/1.03  cnf(contradiction,plain,
% 1.58/1.03      ( $false ),
% 1.58/1.03      inference(minisat,[status(thm)],[c_1783,c_1693]) ).
% 1.58/1.03  
% 1.58/1.03  
% 1.58/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.58/1.03  
% 1.58/1.03  ------                               Statistics
% 1.58/1.03  
% 1.58/1.03  ------ General
% 1.58/1.03  
% 1.58/1.03  abstr_ref_over_cycles:                  0
% 1.58/1.03  abstr_ref_under_cycles:                 0
% 1.58/1.03  gc_basic_clause_elim:                   0
% 1.58/1.03  forced_gc_time:                         0
% 1.58/1.03  parsing_time:                           0.009
% 1.58/1.03  unif_index_cands_time:                  0.
% 1.58/1.03  unif_index_add_time:                    0.
% 1.58/1.03  orderings_time:                         0.
% 1.58/1.03  out_proof_time:                         0.013
% 1.58/1.03  total_time:                             0.089
% 1.58/1.03  num_of_symbols:                         63
% 1.58/1.03  num_of_terms:                           1581
% 1.58/1.03  
% 1.58/1.03  ------ Preprocessing
% 1.58/1.03  
% 1.58/1.03  num_of_splits:                          0
% 1.58/1.03  num_of_split_atoms:                     0
% 1.58/1.03  num_of_reused_defs:                     0
% 1.58/1.03  num_eq_ax_congr_red:                    36
% 1.58/1.03  num_of_sem_filtered_clauses:            1
% 1.58/1.03  num_of_subtypes:                        3
% 1.58/1.03  monotx_restored_types:                  0
% 1.58/1.03  sat_num_of_epr_types:                   0
% 1.58/1.03  sat_num_of_non_cyclic_types:            0
% 1.58/1.03  sat_guarded_non_collapsed_types:        0
% 1.58/1.03  num_pure_diseq_elim:                    0
% 1.58/1.03  simp_replaced_by:                       0
% 1.58/1.03  res_preprocessed:                       86
% 1.58/1.03  prep_upred:                             0
% 1.58/1.03  prep_unflattend:                        32
% 1.58/1.03  smt_new_axioms:                         0
% 1.58/1.03  pred_elim_cands:                        3
% 1.58/1.03  pred_elim:                              11
% 1.58/1.03  pred_elim_cl:                           15
% 1.58/1.03  pred_elim_cycles:                       17
% 1.58/1.03  merged_defs:                            0
% 1.58/1.03  merged_defs_ncl:                        0
% 1.58/1.03  bin_hyper_res:                          0
% 1.58/1.03  prep_cycles:                            4
% 1.58/1.03  pred_elim_time:                         0.007
% 1.58/1.03  splitting_time:                         0.
% 1.58/1.03  sem_filter_time:                        0.
% 1.58/1.03  monotx_time:                            0.
% 1.58/1.03  subtype_inf_time:                       0.
% 1.58/1.03  
% 1.58/1.03  ------ Problem properties
% 1.58/1.03  
% 1.58/1.03  clauses:                                12
% 1.58/1.03  conjectures:                            4
% 1.58/1.03  epr:                                    1
% 1.58/1.03  horn:                                   10
% 1.58/1.03  ground:                                 6
% 1.58/1.03  unary:                                  6
% 1.58/1.03  binary:                                 3
% 1.58/1.03  lits:                                   21
% 1.58/1.03  lits_eq:                                3
% 1.58/1.03  fd_pure:                                0
% 1.58/1.03  fd_pseudo:                              0
% 1.58/1.03  fd_cond:                                0
% 1.58/1.03  fd_pseudo_cond:                         0
% 1.58/1.03  ac_symbols:                             0
% 1.58/1.03  
% 1.58/1.03  ------ Propositional Solver
% 1.58/1.03  
% 1.58/1.03  prop_solver_calls:                      26
% 1.58/1.03  prop_fast_solver_calls:                 560
% 1.58/1.03  smt_solver_calls:                       0
% 1.58/1.03  smt_fast_solver_calls:                  0
% 1.58/1.03  prop_num_of_clauses:                    500
% 1.58/1.03  prop_preprocess_simplified:             2336
% 1.58/1.03  prop_fo_subsumed:                       27
% 1.58/1.03  prop_solver_time:                       0.
% 1.58/1.03  smt_solver_time:                        0.
% 1.58/1.03  smt_fast_solver_time:                   0.
% 1.58/1.03  prop_fast_solver_time:                  0.
% 1.58/1.03  prop_unsat_core_time:                   0.
% 1.58/1.03  
% 1.58/1.03  ------ QBF
% 1.58/1.03  
% 1.58/1.03  qbf_q_res:                              0
% 1.58/1.03  qbf_num_tautologies:                    0
% 1.58/1.03  qbf_prep_cycles:                        0
% 1.58/1.03  
% 1.58/1.03  ------ BMC1
% 1.58/1.03  
% 1.58/1.03  bmc1_current_bound:                     -1
% 1.58/1.03  bmc1_last_solved_bound:                 -1
% 1.58/1.03  bmc1_unsat_core_size:                   -1
% 1.58/1.03  bmc1_unsat_core_parents_size:           -1
% 1.58/1.03  bmc1_merge_next_fun:                    0
% 1.58/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.58/1.03  
% 1.58/1.03  ------ Instantiation
% 1.58/1.03  
% 1.58/1.03  inst_num_of_clauses:                    127
% 1.58/1.03  inst_num_in_passive:                    21
% 1.58/1.03  inst_num_in_active:                     103
% 1.58/1.03  inst_num_in_unprocessed:                3
% 1.58/1.03  inst_num_of_loops:                      110
% 1.58/1.03  inst_num_of_learning_restarts:          0
% 1.58/1.03  inst_num_moves_active_passive:          4
% 1.58/1.03  inst_lit_activity:                      0
% 1.58/1.03  inst_lit_activity_moves:                0
% 1.58/1.03  inst_num_tautologies:                   0
% 1.58/1.03  inst_num_prop_implied:                  0
% 1.58/1.03  inst_num_existing_simplified:           0
% 1.58/1.03  inst_num_eq_res_simplified:             0
% 1.58/1.03  inst_num_child_elim:                    0
% 1.58/1.03  inst_num_of_dismatching_blockings:      9
% 1.58/1.03  inst_num_of_non_proper_insts:           122
% 1.58/1.03  inst_num_of_duplicates:                 0
% 1.58/1.03  inst_inst_num_from_inst_to_res:         0
% 1.58/1.03  inst_dismatching_checking_time:         0.
% 1.58/1.03  
% 1.58/1.03  ------ Resolution
% 1.58/1.03  
% 1.58/1.03  res_num_of_clauses:                     0
% 1.58/1.03  res_num_in_passive:                     0
% 1.58/1.03  res_num_in_active:                      0
% 1.58/1.03  res_num_of_loops:                       90
% 1.58/1.03  res_forward_subset_subsumed:            23
% 1.58/1.03  res_backward_subset_subsumed:           2
% 1.58/1.03  res_forward_subsumed:                   0
% 1.58/1.03  res_backward_subsumed:                  0
% 1.58/1.03  res_forward_subsumption_resolution:     0
% 1.58/1.03  res_backward_subsumption_resolution:    1
% 1.58/1.03  res_clause_to_clause_subsumption:       35
% 1.58/1.03  res_orphan_elimination:                 0
% 1.58/1.03  res_tautology_del:                      23
% 1.58/1.03  res_num_eq_res_simplified:              0
% 1.58/1.03  res_num_sel_changes:                    0
% 1.58/1.03  res_moves_from_active_to_pass:          0
% 1.58/1.03  
% 1.58/1.03  ------ Superposition
% 1.58/1.03  
% 1.58/1.03  sup_time_total:                         0.
% 1.58/1.03  sup_time_generating:                    0.
% 1.58/1.03  sup_time_sim_full:                      0.
% 1.58/1.03  sup_time_sim_immed:                     0.
% 1.58/1.03  
% 1.58/1.03  sup_num_of_clauses:                     29
% 1.58/1.03  sup_num_in_active:                      21
% 1.58/1.03  sup_num_in_passive:                     8
% 1.58/1.03  sup_num_of_loops:                       21
% 1.58/1.03  sup_fw_superposition:                   14
% 1.58/1.03  sup_bw_superposition:                   3
% 1.58/1.03  sup_immediate_simplified:               1
% 1.58/1.03  sup_given_eliminated:                   0
% 1.58/1.03  comparisons_done:                       0
% 1.58/1.03  comparisons_avoided:                    0
% 1.58/1.03  
% 1.58/1.03  ------ Simplifications
% 1.58/1.03  
% 1.58/1.03  
% 1.58/1.03  sim_fw_subset_subsumed:                 0
% 1.58/1.03  sim_bw_subset_subsumed:                 0
% 1.58/1.03  sim_fw_subsumed:                        0
% 1.58/1.03  sim_bw_subsumed:                        0
% 1.58/1.03  sim_fw_subsumption_res:                 0
% 1.58/1.03  sim_bw_subsumption_res:                 0
% 1.58/1.03  sim_tautology_del:                      0
% 1.58/1.03  sim_eq_tautology_del:                   0
% 1.58/1.03  sim_eq_res_simp:                        0
% 1.58/1.03  sim_fw_demodulated:                     0
% 1.58/1.03  sim_bw_demodulated:                     1
% 1.58/1.03  sim_light_normalised:                   2
% 1.58/1.03  sim_joinable_taut:                      0
% 1.58/1.03  sim_joinable_simp:                      0
% 1.58/1.03  sim_ac_normalised:                      0
% 1.58/1.03  sim_smt_subsumption:                    0
% 1.58/1.03  
%------------------------------------------------------------------------------
