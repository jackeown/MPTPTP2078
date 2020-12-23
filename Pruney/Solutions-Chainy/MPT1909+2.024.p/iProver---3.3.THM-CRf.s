%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:58 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 891 expanded)
%              Number of clauses        :   92 ( 171 expanded)
%              Number of leaves         :   22 ( 358 expanded)
%              Depth                    :   20
%              Number of atoms          :  728 (10174 expanded)
%              Number of equality atoms :  127 (1784 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK7))
        & sK7 = X3
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
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
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
            & sK6 = X4
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f30,f48,f47,f46,f45,f44])).

fof(f83,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(definition_unfolding,[],[f81,f83])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f24])).

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
     => ( ~ v3_tex_2(sK2(X0,X1),X0)
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f74,plain,(
    v4_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f80,plain,(
    v3_borsuk_1(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f55])).

fof(f84,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(definition_unfolding,[],[f84,f83])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1189,plain,
    ( k2_pre_topc(X0_58,X0_57) = k2_pre_topc(X0_58,X1_57)
    | X0_57 != X1_57 ),
    theory(equality)).

cnf(c_1815,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,X0_57)
    | k6_domain_1(u1_struct_0(sK3),sK7) != X0_57 ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_3414,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,k2_tarski(sK7,sK7))
    | k6_domain_1(u1_struct_0(sK3),sK7) != k2_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1176,plain,
    ( ~ r2_hidden(X0_57,X1_57)
    | ~ v1_xboole_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2266,plain,
    ( ~ r2_hidden(sK7,X0_57)
    | ~ v1_xboole_0(X0_57) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_3242,plain,
    ( ~ r2_hidden(sK7,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2266])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1165,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1641,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1165])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(X0_57,X1_57)
    | r2_hidden(X0_57,X1_57)
    | v1_xboole_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1636,plain,
    ( m1_subset_1(X0_57,X1_57) != iProver_top
    | r2_hidden(X0_57,X1_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_2346,plain,
    ( r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1636])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_730,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_731,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_730])).

cnf(c_732,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_16,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f89])).

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

cnf(c_715,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_179,c_26])).

cnf(c_716,plain,
    ( v3_tex_2(u1_struct_0(sK4),sK3)
    | ~ v4_tex_2(sK4,sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_27,negated_conjecture,
    ( v4_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_718,plain,
    ( v3_tex_2(u1_struct_0(sK4),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_32,c_29,c_27])).

cnf(c_772,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK4) != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_456,c_718])).

cnf(c_773,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_774,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_1763,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK4))
    | r2_hidden(X0_57,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_1980,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | r2_hidden(sK7,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_1981,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_2682,plain,
    ( r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2346,c_36,c_45,c_732,c_774,c_1981])).

cnf(c_5,plain,
    ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1172,plain,
    ( m1_subset_1(k2_tarski(X0_57,X0_57),k1_zfmisc_1(X1_57))
    | ~ r2_hidden(X0_57,X1_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1635,plain,
    ( m1_subset_1(k2_tarski(X0_57,X0_57),k1_zfmisc_1(X1_57)) = iProver_top
    | r2_hidden(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_741,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK4 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_742,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_741])).

cnf(c_746,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_742,c_29])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_746])).

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
    inference(cnf_transformation,[],[f90])).

cnf(c_21,negated_conjecture,
    ( v3_borsuk_1(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f80])).

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
    inference(cnf_transformation,[],[f71])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_23,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f79])).

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

cnf(c_767,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_747,c_432])).

cnf(c_1161,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_57) = k2_pre_topc(sK3,X0_57) ),
    inference(subtyping,[status(esa)],[c_767])).

cnf(c_1645,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_57) = k2_pre_topc(sK3,X0_57)
    | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1161])).

cnf(c_1944,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_tarski(X0_57,X0_57)) = k2_pre_topc(sK3,k2_tarski(X0_57,X0_57))
    | r2_hidden(X0_57,u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1635,c_1645])).

cnf(c_2688,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_tarski(sK7,sK7)) = k2_pre_topc(sK3,k2_tarski(sK7,sK7)) ),
    inference(superposition,[status(thm)],[c_2682,c_1944])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1168,plain,
    ( ~ m1_subset_1(X0_57,X1_57)
    | v1_xboole_0(X1_57)
    | k6_domain_1(X1_57,X0_57) = k2_tarski(X0_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1639,plain,
    ( k6_domain_1(X0_57,X1_57) = k2_tarski(X1_57,X1_57)
    | m1_subset_1(X1_57,X0_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1168])).

cnf(c_2541,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK7) = k2_tarski(sK7,sK7)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1639])).

cnf(c_1774,plain,
    ( ~ m1_subset_1(X0_57,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),X0_57) = k2_tarski(X0_57,X0_57) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_2005,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK7) = k2_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_2739,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK7) = k2_tarski(sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_29,c_20,c_731,c_773,c_2005])).

cnf(c_18,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1167,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2742,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_tarski(sK7,sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(demodulation,[status(thm)],[c_2739,c_1167])).

cnf(c_2938,plain,
    ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) != k2_pre_topc(sK3,k2_tarski(sK7,sK7)) ),
    inference(demodulation,[status(thm)],[c_2688,c_2742])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1173,plain,
    ( ~ r1_tarski(X0_57,X1_57)
    | ~ r2_hidden(X2_57,X0_57)
    | r2_hidden(X2_57,X1_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2042,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),X0_57)
    | r2_hidden(sK7,X0_57)
    | ~ r2_hidden(sK7,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_2697,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ r2_hidden(sK7,u1_struct_0(sK4))
    | r2_hidden(sK7,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1166,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1640,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_2540,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK7) = k2_tarski(sK7,sK7)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_1639])).

cnf(c_2588,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK7) = k2_tarski(sK7,sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2540])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1169,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | r1_tarski(X0_57,X1_57) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_57))
    | r1_tarski(u1_struct_0(sK4),X0_57) ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_2205,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3414,c_3242,c_2938,c_2697,c_2588,c_2205,c_1980,c_773,c_731,c_20,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.88/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/0.99  
% 1.88/0.99  ------  iProver source info
% 1.88/0.99  
% 1.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/0.99  git: non_committed_changes: false
% 1.88/0.99  git: last_make_outside_of_git: false
% 1.88/0.99  
% 1.88/0.99  ------ 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options
% 1.88/0.99  
% 1.88/0.99  --out_options                           all
% 1.88/0.99  --tptp_safe_out                         true
% 1.88/0.99  --problem_path                          ""
% 1.88/0.99  --include_path                          ""
% 1.88/0.99  --clausifier                            res/vclausify_rel
% 1.88/0.99  --clausifier_options                    --mode clausify
% 1.88/0.99  --stdin                                 false
% 1.88/0.99  --stats_out                             all
% 1.88/0.99  
% 1.88/0.99  ------ General Options
% 1.88/0.99  
% 1.88/0.99  --fof                                   false
% 1.88/0.99  --time_out_real                         305.
% 1.88/0.99  --time_out_virtual                      -1.
% 1.88/0.99  --symbol_type_check                     false
% 1.88/0.99  --clausify_out                          false
% 1.88/0.99  --sig_cnt_out                           false
% 1.88/0.99  --trig_cnt_out                          false
% 1.88/0.99  --trig_cnt_out_tolerance                1.
% 1.88/0.99  --trig_cnt_out_sk_spl                   false
% 1.88/0.99  --abstr_cl_out                          false
% 1.88/0.99  
% 1.88/0.99  ------ Global Options
% 1.88/0.99  
% 1.88/0.99  --schedule                              default
% 1.88/0.99  --add_important_lit                     false
% 1.88/0.99  --prop_solver_per_cl                    1000
% 1.88/0.99  --min_unsat_core                        false
% 1.88/0.99  --soft_assumptions                      false
% 1.88/0.99  --soft_lemma_size                       3
% 1.88/0.99  --prop_impl_unit_size                   0
% 1.88/0.99  --prop_impl_unit                        []
% 1.88/0.99  --share_sel_clauses                     true
% 1.88/0.99  --reset_solvers                         false
% 1.88/0.99  --bc_imp_inh                            [conj_cone]
% 1.88/0.99  --conj_cone_tolerance                   3.
% 1.88/0.99  --extra_neg_conj                        none
% 1.88/0.99  --large_theory_mode                     true
% 1.88/0.99  --prolific_symb_bound                   200
% 1.88/0.99  --lt_threshold                          2000
% 1.88/0.99  --clause_weak_htbl                      true
% 1.88/0.99  --gc_record_bc_elim                     false
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing Options
% 1.88/0.99  
% 1.88/0.99  --preprocessing_flag                    true
% 1.88/0.99  --time_out_prep_mult                    0.1
% 1.88/0.99  --splitting_mode                        input
% 1.88/0.99  --splitting_grd                         true
% 1.88/0.99  --splitting_cvd                         false
% 1.88/0.99  --splitting_cvd_svl                     false
% 1.88/0.99  --splitting_nvd                         32
% 1.88/0.99  --sub_typing                            true
% 1.88/0.99  --prep_gs_sim                           true
% 1.88/0.99  --prep_unflatten                        true
% 1.88/0.99  --prep_res_sim                          true
% 1.88/0.99  --prep_upred                            true
% 1.88/0.99  --prep_sem_filter                       exhaustive
% 1.88/0.99  --prep_sem_filter_out                   false
% 1.88/0.99  --pred_elim                             true
% 1.88/0.99  --res_sim_input                         true
% 1.88/0.99  --eq_ax_congr_red                       true
% 1.88/0.99  --pure_diseq_elim                       true
% 1.88/0.99  --brand_transform                       false
% 1.88/0.99  --non_eq_to_eq                          false
% 1.88/0.99  --prep_def_merge                        true
% 1.88/0.99  --prep_def_merge_prop_impl              false
% 1.88/0.99  --prep_def_merge_mbd                    true
% 1.88/0.99  --prep_def_merge_tr_red                 false
% 1.88/0.99  --prep_def_merge_tr_cl                  false
% 1.88/0.99  --smt_preprocessing                     true
% 1.88/0.99  --smt_ac_axioms                         fast
% 1.88/0.99  --preprocessed_out                      false
% 1.88/0.99  --preprocessed_stats                    false
% 1.88/0.99  
% 1.88/0.99  ------ Abstraction refinement Options
% 1.88/0.99  
% 1.88/0.99  --abstr_ref                             []
% 1.88/0.99  --abstr_ref_prep                        false
% 1.88/0.99  --abstr_ref_until_sat                   false
% 1.88/0.99  --abstr_ref_sig_restrict                funpre
% 1.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.99  --abstr_ref_under                       []
% 1.88/0.99  
% 1.88/0.99  ------ SAT Options
% 1.88/0.99  
% 1.88/0.99  --sat_mode                              false
% 1.88/0.99  --sat_fm_restart_options                ""
% 1.88/0.99  --sat_gr_def                            false
% 1.88/0.99  --sat_epr_types                         true
% 1.88/0.99  --sat_non_cyclic_types                  false
% 1.88/0.99  --sat_finite_models                     false
% 1.88/0.99  --sat_fm_lemmas                         false
% 1.88/0.99  --sat_fm_prep                           false
% 1.88/0.99  --sat_fm_uc_incr                        true
% 1.88/0.99  --sat_out_model                         small
% 1.88/0.99  --sat_out_clauses                       false
% 1.88/0.99  
% 1.88/0.99  ------ QBF Options
% 1.88/0.99  
% 1.88/0.99  --qbf_mode                              false
% 1.88/0.99  --qbf_elim_univ                         false
% 1.88/0.99  --qbf_dom_inst                          none
% 1.88/0.99  --qbf_dom_pre_inst                      false
% 1.88/0.99  --qbf_sk_in                             false
% 1.88/0.99  --qbf_pred_elim                         true
% 1.88/0.99  --qbf_split                             512
% 1.88/0.99  
% 1.88/0.99  ------ BMC1 Options
% 1.88/0.99  
% 1.88/0.99  --bmc1_incremental                      false
% 1.88/0.99  --bmc1_axioms                           reachable_all
% 1.88/0.99  --bmc1_min_bound                        0
% 1.88/0.99  --bmc1_max_bound                        -1
% 1.88/0.99  --bmc1_max_bound_default                -1
% 1.88/0.99  --bmc1_symbol_reachability              true
% 1.88/0.99  --bmc1_property_lemmas                  false
% 1.88/0.99  --bmc1_k_induction                      false
% 1.88/0.99  --bmc1_non_equiv_states                 false
% 1.88/0.99  --bmc1_deadlock                         false
% 1.88/0.99  --bmc1_ucm                              false
% 1.88/0.99  --bmc1_add_unsat_core                   none
% 1.88/0.99  --bmc1_unsat_core_children              false
% 1.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.99  --bmc1_out_stat                         full
% 1.88/0.99  --bmc1_ground_init                      false
% 1.88/0.99  --bmc1_pre_inst_next_state              false
% 1.88/0.99  --bmc1_pre_inst_state                   false
% 1.88/0.99  --bmc1_pre_inst_reach_state             false
% 1.88/0.99  --bmc1_out_unsat_core                   false
% 1.88/0.99  --bmc1_aig_witness_out                  false
% 1.88/0.99  --bmc1_verbose                          false
% 1.88/0.99  --bmc1_dump_clauses_tptp                false
% 1.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.99  --bmc1_dump_file                        -
% 1.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.99  --bmc1_ucm_extend_mode                  1
% 1.88/0.99  --bmc1_ucm_init_mode                    2
% 1.88/0.99  --bmc1_ucm_cone_mode                    none
% 1.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.99  --bmc1_ucm_relax_model                  4
% 1.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.99  --bmc1_ucm_layered_model                none
% 1.88/0.99  --bmc1_ucm_max_lemma_size               10
% 1.88/0.99  
% 1.88/0.99  ------ AIG Options
% 1.88/0.99  
% 1.88/0.99  --aig_mode                              false
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation Options
% 1.88/0.99  
% 1.88/0.99  --instantiation_flag                    true
% 1.88/0.99  --inst_sos_flag                         false
% 1.88/0.99  --inst_sos_phase                        true
% 1.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel_side                     num_symb
% 1.88/0.99  --inst_solver_per_active                1400
% 1.88/0.99  --inst_solver_calls_frac                1.
% 1.88/0.99  --inst_passive_queue_type               priority_queues
% 1.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.99  --inst_passive_queues_freq              [25;2]
% 1.88/0.99  --inst_dismatching                      true
% 1.88/0.99  --inst_eager_unprocessed_to_passive     true
% 1.88/0.99  --inst_prop_sim_given                   true
% 1.88/0.99  --inst_prop_sim_new                     false
% 1.88/0.99  --inst_subs_new                         false
% 1.88/0.99  --inst_eq_res_simp                      false
% 1.88/0.99  --inst_subs_given                       false
% 1.88/0.99  --inst_orphan_elimination               true
% 1.88/0.99  --inst_learning_loop_flag               true
% 1.88/0.99  --inst_learning_start                   3000
% 1.88/0.99  --inst_learning_factor                  2
% 1.88/0.99  --inst_start_prop_sim_after_learn       3
% 1.88/0.99  --inst_sel_renew                        solver
% 1.88/0.99  --inst_lit_activity_flag                true
% 1.88/0.99  --inst_restr_to_given                   false
% 1.88/0.99  --inst_activity_threshold               500
% 1.88/0.99  --inst_out_proof                        true
% 1.88/0.99  
% 1.88/0.99  ------ Resolution Options
% 1.88/0.99  
% 1.88/0.99  --resolution_flag                       true
% 1.88/0.99  --res_lit_sel                           adaptive
% 1.88/0.99  --res_lit_sel_side                      none
% 1.88/0.99  --res_ordering                          kbo
% 1.88/0.99  --res_to_prop_solver                    active
% 1.88/0.99  --res_prop_simpl_new                    false
% 1.88/0.99  --res_prop_simpl_given                  true
% 1.88/0.99  --res_passive_queue_type                priority_queues
% 1.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/0.99  --res_passive_queues_freq               [15;5]
% 1.88/0.99  --res_forward_subs                      full
% 1.88/0.99  --res_backward_subs                     full
% 1.88/0.99  --res_forward_subs_resolution           true
% 1.88/0.99  --res_backward_subs_resolution          true
% 1.88/0.99  --res_orphan_elimination                true
% 1.88/0.99  --res_time_limit                        2.
% 1.88/0.99  --res_out_proof                         true
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Options
% 1.88/0.99  
% 1.88/0.99  --superposition_flag                    true
% 1.88/0.99  --sup_passive_queue_type                priority_queues
% 1.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.88/0.99  --demod_completeness_check              fast
% 1.88/0.99  --demod_use_ground                      true
% 1.88/0.99  --sup_to_prop_solver                    passive
% 1.88/0.99  --sup_prop_simpl_new                    true
% 1.88/0.99  --sup_prop_simpl_given                  true
% 1.88/0.99  --sup_fun_splitting                     false
% 1.88/0.99  --sup_smt_interval                      50000
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Simplification Setup
% 1.88/0.99  
% 1.88/0.99  --sup_indices_passive                   []
% 1.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_full_bw                           [BwDemod]
% 1.88/0.99  --sup_immed_triv                        [TrivRules]
% 1.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_immed_bw_main                     []
% 1.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  
% 1.88/0.99  ------ Combination Options
% 1.88/0.99  
% 1.88/0.99  --comb_res_mult                         3
% 1.88/0.99  --comb_sup_mult                         2
% 1.88/0.99  --comb_inst_mult                        10
% 1.88/0.99  
% 1.88/0.99  ------ Debug Options
% 1.88/0.99  
% 1.88/0.99  --dbg_backtrace                         false
% 1.88/0.99  --dbg_dump_prop_clauses                 false
% 1.88/0.99  --dbg_dump_prop_clauses_file            -
% 1.88/0.99  --dbg_out_stat                          false
% 1.88/0.99  ------ Parsing...
% 1.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/0.99  ------ Proving...
% 1.88/0.99  ------ Problem Properties 
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  clauses                                 18
% 1.88/0.99  conjectures                             4
% 1.88/0.99  EPR                                     3
% 1.88/0.99  Horn                                    14
% 1.88/0.99  unary                                   6
% 1.88/0.99  binary                                  9
% 1.88/0.99  lits                                    33
% 1.88/0.99  lits eq                                 3
% 1.88/0.99  fd_pure                                 0
% 1.88/0.99  fd_pseudo                               0
% 1.88/0.99  fd_cond                                 0
% 1.88/0.99  fd_pseudo_cond                          0
% 1.88/0.99  AC symbols                              0
% 1.88/0.99  
% 1.88/0.99  ------ Schedule dynamic 5 is on 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  ------ 
% 1.88/0.99  Current options:
% 1.88/0.99  ------ 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options
% 1.88/0.99  
% 1.88/0.99  --out_options                           all
% 1.88/0.99  --tptp_safe_out                         true
% 1.88/0.99  --problem_path                          ""
% 1.88/0.99  --include_path                          ""
% 1.88/0.99  --clausifier                            res/vclausify_rel
% 1.88/0.99  --clausifier_options                    --mode clausify
% 1.88/0.99  --stdin                                 false
% 1.88/0.99  --stats_out                             all
% 1.88/0.99  
% 1.88/0.99  ------ General Options
% 1.88/0.99  
% 1.88/0.99  --fof                                   false
% 1.88/0.99  --time_out_real                         305.
% 1.88/0.99  --time_out_virtual                      -1.
% 1.88/0.99  --symbol_type_check                     false
% 1.88/0.99  --clausify_out                          false
% 1.88/0.99  --sig_cnt_out                           false
% 1.88/0.99  --trig_cnt_out                          false
% 1.88/0.99  --trig_cnt_out_tolerance                1.
% 1.88/0.99  --trig_cnt_out_sk_spl                   false
% 1.88/0.99  --abstr_cl_out                          false
% 1.88/0.99  
% 1.88/0.99  ------ Global Options
% 1.88/0.99  
% 1.88/0.99  --schedule                              default
% 1.88/0.99  --add_important_lit                     false
% 1.88/0.99  --prop_solver_per_cl                    1000
% 1.88/0.99  --min_unsat_core                        false
% 1.88/0.99  --soft_assumptions                      false
% 1.88/0.99  --soft_lemma_size                       3
% 1.88/0.99  --prop_impl_unit_size                   0
% 1.88/0.99  --prop_impl_unit                        []
% 1.88/0.99  --share_sel_clauses                     true
% 1.88/0.99  --reset_solvers                         false
% 1.88/0.99  --bc_imp_inh                            [conj_cone]
% 1.88/0.99  --conj_cone_tolerance                   3.
% 1.88/0.99  --extra_neg_conj                        none
% 1.88/0.99  --large_theory_mode                     true
% 1.88/0.99  --prolific_symb_bound                   200
% 1.88/0.99  --lt_threshold                          2000
% 1.88/0.99  --clause_weak_htbl                      true
% 1.88/0.99  --gc_record_bc_elim                     false
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing Options
% 1.88/0.99  
% 1.88/0.99  --preprocessing_flag                    true
% 1.88/0.99  --time_out_prep_mult                    0.1
% 1.88/0.99  --splitting_mode                        input
% 1.88/0.99  --splitting_grd                         true
% 1.88/0.99  --splitting_cvd                         false
% 1.88/0.99  --splitting_cvd_svl                     false
% 1.88/0.99  --splitting_nvd                         32
% 1.88/0.99  --sub_typing                            true
% 1.88/0.99  --prep_gs_sim                           true
% 1.88/0.99  --prep_unflatten                        true
% 1.88/0.99  --prep_res_sim                          true
% 1.88/0.99  --prep_upred                            true
% 1.88/0.99  --prep_sem_filter                       exhaustive
% 1.88/0.99  --prep_sem_filter_out                   false
% 1.88/0.99  --pred_elim                             true
% 1.88/0.99  --res_sim_input                         true
% 1.88/0.99  --eq_ax_congr_red                       true
% 1.88/0.99  --pure_diseq_elim                       true
% 1.88/0.99  --brand_transform                       false
% 1.88/0.99  --non_eq_to_eq                          false
% 1.88/0.99  --prep_def_merge                        true
% 1.88/0.99  --prep_def_merge_prop_impl              false
% 1.88/0.99  --prep_def_merge_mbd                    true
% 1.88/0.99  --prep_def_merge_tr_red                 false
% 1.88/0.99  --prep_def_merge_tr_cl                  false
% 1.88/0.99  --smt_preprocessing                     true
% 1.88/0.99  --smt_ac_axioms                         fast
% 1.88/0.99  --preprocessed_out                      false
% 1.88/0.99  --preprocessed_stats                    false
% 1.88/0.99  
% 1.88/0.99  ------ Abstraction refinement Options
% 1.88/0.99  
% 1.88/0.99  --abstr_ref                             []
% 1.88/0.99  --abstr_ref_prep                        false
% 1.88/0.99  --abstr_ref_until_sat                   false
% 1.88/0.99  --abstr_ref_sig_restrict                funpre
% 1.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.99  --abstr_ref_under                       []
% 1.88/0.99  
% 1.88/0.99  ------ SAT Options
% 1.88/0.99  
% 1.88/0.99  --sat_mode                              false
% 1.88/0.99  --sat_fm_restart_options                ""
% 1.88/0.99  --sat_gr_def                            false
% 1.88/0.99  --sat_epr_types                         true
% 1.88/0.99  --sat_non_cyclic_types                  false
% 1.88/0.99  --sat_finite_models                     false
% 1.88/0.99  --sat_fm_lemmas                         false
% 1.88/0.99  --sat_fm_prep                           false
% 1.88/0.99  --sat_fm_uc_incr                        true
% 1.88/0.99  --sat_out_model                         small
% 1.88/0.99  --sat_out_clauses                       false
% 1.88/0.99  
% 1.88/0.99  ------ QBF Options
% 1.88/0.99  
% 1.88/0.99  --qbf_mode                              false
% 1.88/0.99  --qbf_elim_univ                         false
% 1.88/0.99  --qbf_dom_inst                          none
% 1.88/0.99  --qbf_dom_pre_inst                      false
% 1.88/0.99  --qbf_sk_in                             false
% 1.88/0.99  --qbf_pred_elim                         true
% 1.88/0.99  --qbf_split                             512
% 1.88/0.99  
% 1.88/0.99  ------ BMC1 Options
% 1.88/0.99  
% 1.88/0.99  --bmc1_incremental                      false
% 1.88/0.99  --bmc1_axioms                           reachable_all
% 1.88/0.99  --bmc1_min_bound                        0
% 1.88/0.99  --bmc1_max_bound                        -1
% 1.88/0.99  --bmc1_max_bound_default                -1
% 1.88/0.99  --bmc1_symbol_reachability              true
% 1.88/0.99  --bmc1_property_lemmas                  false
% 1.88/0.99  --bmc1_k_induction                      false
% 1.88/0.99  --bmc1_non_equiv_states                 false
% 1.88/0.99  --bmc1_deadlock                         false
% 1.88/0.99  --bmc1_ucm                              false
% 1.88/0.99  --bmc1_add_unsat_core                   none
% 1.88/0.99  --bmc1_unsat_core_children              false
% 1.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.99  --bmc1_out_stat                         full
% 1.88/0.99  --bmc1_ground_init                      false
% 1.88/0.99  --bmc1_pre_inst_next_state              false
% 1.88/0.99  --bmc1_pre_inst_state                   false
% 1.88/0.99  --bmc1_pre_inst_reach_state             false
% 1.88/0.99  --bmc1_out_unsat_core                   false
% 1.88/0.99  --bmc1_aig_witness_out                  false
% 1.88/0.99  --bmc1_verbose                          false
% 1.88/0.99  --bmc1_dump_clauses_tptp                false
% 1.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.99  --bmc1_dump_file                        -
% 1.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.99  --bmc1_ucm_extend_mode                  1
% 1.88/0.99  --bmc1_ucm_init_mode                    2
% 1.88/0.99  --bmc1_ucm_cone_mode                    none
% 1.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.99  --bmc1_ucm_relax_model                  4
% 1.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.99  --bmc1_ucm_layered_model                none
% 1.88/0.99  --bmc1_ucm_max_lemma_size               10
% 1.88/0.99  
% 1.88/0.99  ------ AIG Options
% 1.88/0.99  
% 1.88/0.99  --aig_mode                              false
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation Options
% 1.88/0.99  
% 1.88/0.99  --instantiation_flag                    true
% 1.88/0.99  --inst_sos_flag                         false
% 1.88/0.99  --inst_sos_phase                        true
% 1.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel_side                     none
% 1.88/0.99  --inst_solver_per_active                1400
% 1.88/0.99  --inst_solver_calls_frac                1.
% 1.88/0.99  --inst_passive_queue_type               priority_queues
% 1.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.99  --inst_passive_queues_freq              [25;2]
% 1.88/0.99  --inst_dismatching                      true
% 1.88/0.99  --inst_eager_unprocessed_to_passive     true
% 1.88/0.99  --inst_prop_sim_given                   true
% 1.88/0.99  --inst_prop_sim_new                     false
% 1.88/0.99  --inst_subs_new                         false
% 1.88/0.99  --inst_eq_res_simp                      false
% 1.88/0.99  --inst_subs_given                       false
% 1.88/0.99  --inst_orphan_elimination               true
% 1.88/0.99  --inst_learning_loop_flag               true
% 1.88/0.99  --inst_learning_start                   3000
% 1.88/0.99  --inst_learning_factor                  2
% 1.88/0.99  --inst_start_prop_sim_after_learn       3
% 1.88/0.99  --inst_sel_renew                        solver
% 1.88/0.99  --inst_lit_activity_flag                true
% 1.88/0.99  --inst_restr_to_given                   false
% 1.88/0.99  --inst_activity_threshold               500
% 1.88/0.99  --inst_out_proof                        true
% 1.88/0.99  
% 1.88/0.99  ------ Resolution Options
% 1.88/0.99  
% 1.88/0.99  --resolution_flag                       false
% 1.88/0.99  --res_lit_sel                           adaptive
% 1.88/0.99  --res_lit_sel_side                      none
% 1.88/1.00  --res_ordering                          kbo
% 1.88/1.00  --res_to_prop_solver                    active
% 1.88/1.00  --res_prop_simpl_new                    false
% 1.88/1.00  --res_prop_simpl_given                  true
% 1.88/1.00  --res_passive_queue_type                priority_queues
% 1.88/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.00  --res_passive_queues_freq               [15;5]
% 1.88/1.00  --res_forward_subs                      full
% 1.88/1.00  --res_backward_subs                     full
% 1.88/1.00  --res_forward_subs_resolution           true
% 1.88/1.00  --res_backward_subs_resolution          true
% 1.88/1.00  --res_orphan_elimination                true
% 1.88/1.00  --res_time_limit                        2.
% 1.88/1.00  --res_out_proof                         true
% 1.88/1.00  
% 1.88/1.00  ------ Superposition Options
% 1.88/1.00  
% 1.88/1.00  --superposition_flag                    true
% 1.88/1.00  --sup_passive_queue_type                priority_queues
% 1.88/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.00  --demod_completeness_check              fast
% 1.88/1.00  --demod_use_ground                      true
% 1.88/1.00  --sup_to_prop_solver                    passive
% 1.88/1.00  --sup_prop_simpl_new                    true
% 1.88/1.00  --sup_prop_simpl_given                  true
% 1.88/1.00  --sup_fun_splitting                     false
% 1.88/1.00  --sup_smt_interval                      50000
% 1.88/1.00  
% 1.88/1.00  ------ Superposition Simplification Setup
% 1.88/1.00  
% 1.88/1.00  --sup_indices_passive                   []
% 1.88/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_full_bw                           [BwDemod]
% 1.88/1.00  --sup_immed_triv                        [TrivRules]
% 1.88/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_immed_bw_main                     []
% 1.88/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.00  
% 1.88/1.00  ------ Combination Options
% 1.88/1.00  
% 1.88/1.00  --comb_res_mult                         3
% 1.88/1.00  --comb_sup_mult                         2
% 1.88/1.00  --comb_inst_mult                        10
% 1.88/1.00  
% 1.88/1.00  ------ Debug Options
% 1.88/1.00  
% 1.88/1.00  --dbg_backtrace                         false
% 1.88/1.00  --dbg_dump_prop_clauses                 false
% 1.88/1.00  --dbg_dump_prop_clauses_file            -
% 1.88/1.00  --dbg_out_stat                          false
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  ------ Proving...
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  % SZS status Theorem for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  fof(f1,axiom,(
% 1.88/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f31,plain,(
% 1.88/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.88/1.00    inference(nnf_transformation,[],[f1])).
% 1.88/1.00  
% 1.88/1.00  fof(f32,plain,(
% 1.88/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.88/1.00    inference(rectify,[],[f31])).
% 1.88/1.00  
% 1.88/1.00  fof(f33,plain,(
% 1.88/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f34,plain,(
% 1.88/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 1.88/1.00  
% 1.88/1.00  fof(f50,plain,(
% 1.88/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f34])).
% 1.88/1.00  
% 1.88/1.00  fof(f81,plain,(
% 1.88/1.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f13,conjecture,(
% 1.88/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f14,negated_conjecture,(
% 1.88/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.88/1.00    inference(negated_conjecture,[],[f13])).
% 1.88/1.00  
% 1.88/1.00  fof(f29,plain,(
% 1.88/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f14])).
% 1.88/1.00  
% 1.88/1.00  fof(f30,plain,(
% 1.88/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f29])).
% 1.88/1.00  
% 1.88/1.00  fof(f48,plain,(
% 1.88/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK7)) & sK7 = X3 & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f47,plain,(
% 1.88/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK6 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f46,plain,(
% 1.88/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK5,X0,X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK5,X0,X1) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f45,plain,(
% 1.88/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k6_domain_1(u1_struct_0(sK4),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK4))) & v3_borsuk_1(X2,X0,sK4) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v5_pre_topc(X2,X0,sK4) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & m1_pre_topc(sK4,X0) & v4_tex_2(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f44,plain,(
% 1.88/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK3,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v5_pre_topc(X2,sK3,X1) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & v4_tex_2(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f49,plain,(
% 1.88/1.00    ((((k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & v3_borsuk_1(sK5,sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v5_pre_topc(sK5,sK3,sK4) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & v4_tex_2(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f30,f48,f47,f46,f45,f44])).
% 1.88/1.00  
% 1.88/1.00  fof(f83,plain,(
% 1.88/1.00    sK6 = sK7),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f88,plain,(
% 1.88/1.00    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.88/1.00    inference(definition_unfolding,[],[f81,f83])).
% 1.88/1.00  
% 1.88/1.00  fof(f5,axiom,(
% 1.88/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f17,plain,(
% 1.88/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.88/1.00    inference(ennf_transformation,[],[f5])).
% 1.88/1.00  
% 1.88/1.00  fof(f18,plain,(
% 1.88/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.88/1.00    inference(flattening,[],[f17])).
% 1.88/1.00  
% 1.88/1.00  fof(f57,plain,(
% 1.88/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f18])).
% 1.88/1.00  
% 1.88/1.00  fof(f72,plain,(
% 1.88/1.00    l1_pre_topc(sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f9,axiom,(
% 1.88/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f22,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.88/1.00    inference(ennf_transformation,[],[f9])).
% 1.88/1.00  
% 1.88/1.00  fof(f62,plain,(
% 1.88/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f22])).
% 1.88/1.00  
% 1.88/1.00  fof(f75,plain,(
% 1.88/1.00    m1_pre_topc(sK4,sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f11,axiom,(
% 1.88/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f25,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f11])).
% 1.88/1.00  
% 1.88/1.00  fof(f26,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f25])).
% 1.88/1.00  
% 1.88/1.00  fof(f67,plain,(
% 1.88/1.00    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f26])).
% 1.88/1.00  
% 1.88/1.00  fof(f70,plain,(
% 1.88/1.00    v2_pre_topc(sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f69,plain,(
% 1.88/1.00    ~v2_struct_0(sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f10,axiom,(
% 1.88/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f23,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f10])).
% 1.88/1.00  
% 1.88/1.00  fof(f24,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f23])).
% 1.88/1.00  
% 1.88/1.00  fof(f40,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(nnf_transformation,[],[f24])).
% 1.88/1.00  
% 1.88/1.00  fof(f41,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(rectify,[],[f40])).
% 1.88/1.00  
% 1.88/1.00  fof(f42,plain,(
% 1.88/1.00    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f43,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK2(X0,X1),X0) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 1.88/1.00  
% 1.88/1.00  fof(f63,plain,(
% 1.88/1.00    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f43])).
% 1.88/1.00  
% 1.88/1.00  fof(f89,plain,(
% 1.88/1.00    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(equality_resolution,[],[f63])).
% 1.88/1.00  
% 1.88/1.00  fof(f74,plain,(
% 1.88/1.00    v4_tex_2(sK4,sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f4,axiom,(
% 1.88/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f16,plain,(
% 1.88/1.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.88/1.00    inference(ennf_transformation,[],[f4])).
% 1.88/1.00  
% 1.88/1.00  fof(f56,plain,(
% 1.88/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f16])).
% 1.88/1.00  
% 1.88/1.00  fof(f3,axiom,(
% 1.88/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f55,plain,(
% 1.88/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f3])).
% 1.88/1.00  
% 1.88/1.00  fof(f85,plain,(
% 1.88/1.00    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.88/1.00    inference(definition_unfolding,[],[f56,f55])).
% 1.88/1.00  
% 1.88/1.00  fof(f7,axiom,(
% 1.88/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f19,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.88/1.00    inference(ennf_transformation,[],[f7])).
% 1.88/1.00  
% 1.88/1.00  fof(f60,plain,(
% 1.88/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f19])).
% 1.88/1.00  
% 1.88/1.00  fof(f12,axiom,(
% 1.88/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f27,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f12])).
% 1.88/1.00  
% 1.88/1.00  fof(f28,plain,(
% 1.88/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.88/1.00    inference(flattening,[],[f27])).
% 1.88/1.00  
% 1.88/1.00  fof(f68,plain,(
% 1.88/1.00    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f28])).
% 1.88/1.00  
% 1.88/1.00  fof(f90,plain,(
% 1.88/1.00    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.88/1.00    inference(equality_resolution,[],[f68])).
% 1.88/1.00  
% 1.88/1.00  fof(f80,plain,(
% 1.88/1.00    v3_borsuk_1(sK5,sK3,sK4)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f71,plain,(
% 1.88/1.00    v3_tdlat_3(sK3)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f73,plain,(
% 1.88/1.00    ~v2_struct_0(sK4)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f76,plain,(
% 1.88/1.00    v1_funct_1(sK5)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f77,plain,(
% 1.88/1.00    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f78,plain,(
% 1.88/1.00    v5_pre_topc(sK5,sK3,sK4)),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f79,plain,(
% 1.88/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f8,axiom,(
% 1.88/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f20,plain,(
% 1.88/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f8])).
% 1.88/1.00  
% 1.88/1.00  fof(f21,plain,(
% 1.88/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.88/1.00    inference(flattening,[],[f20])).
% 1.88/1.00  
% 1.88/1.00  fof(f61,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f21])).
% 1.88/1.00  
% 1.88/1.00  fof(f86,plain,(
% 1.88/1.00    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.88/1.00    inference(definition_unfolding,[],[f61,f55])).
% 1.88/1.00  
% 1.88/1.00  fof(f84,plain,(
% 1.88/1.00    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f87,plain,(
% 1.88/1.00    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))),
% 1.88/1.00    inference(definition_unfolding,[],[f84,f83])).
% 1.88/1.00  
% 1.88/1.00  fof(f2,axiom,(
% 1.88/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f15,plain,(
% 1.88/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.88/1.00    inference(ennf_transformation,[],[f2])).
% 1.88/1.00  
% 1.88/1.00  fof(f35,plain,(
% 1.88/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.88/1.00    inference(nnf_transformation,[],[f15])).
% 1.88/1.00  
% 1.88/1.00  fof(f36,plain,(
% 1.88/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.88/1.00    inference(rectify,[],[f35])).
% 1.88/1.00  
% 1.88/1.00  fof(f37,plain,(
% 1.88/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.88/1.00    introduced(choice_axiom,[])).
% 1.88/1.00  
% 1.88/1.00  fof(f38,plain,(
% 1.88/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 1.88/1.00  
% 1.88/1.00  fof(f52,plain,(
% 1.88/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.88/1.00    inference(cnf_transformation,[],[f38])).
% 1.88/1.00  
% 1.88/1.00  fof(f82,plain,(
% 1.88/1.00    m1_subset_1(sK7,u1_struct_0(sK3))),
% 1.88/1.00    inference(cnf_transformation,[],[f49])).
% 1.88/1.00  
% 1.88/1.00  fof(f6,axiom,(
% 1.88/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.88/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.88/1.00  
% 1.88/1.00  fof(f39,plain,(
% 1.88/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.88/1.00    inference(nnf_transformation,[],[f6])).
% 1.88/1.00  
% 1.88/1.00  fof(f58,plain,(
% 1.88/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.88/1.00    inference(cnf_transformation,[],[f39])).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1189,plain,
% 1.88/1.00      ( k2_pre_topc(X0_58,X0_57) = k2_pre_topc(X0_58,X1_57)
% 1.88/1.00      | X0_57 != X1_57 ),
% 1.88/1.00      theory(equality) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1815,plain,
% 1.88/1.00      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,X0_57)
% 1.88/1.00      | k6_domain_1(u1_struct_0(sK3),sK7) != X0_57 ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1189]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_3414,plain,
% 1.88/1.00      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,k2_tarski(sK7,sK7))
% 1.88/1.00      | k6_domain_1(u1_struct_0(sK3),sK7) != k2_tarski(sK7,sK7) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1815]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1,plain,
% 1.88/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1176,plain,
% 1.88/1.00      ( ~ r2_hidden(X0_57,X1_57) | ~ v1_xboole_0(X1_57) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2266,plain,
% 1.88/1.00      ( ~ r2_hidden(sK7,X0_57) | ~ v1_xboole_0(X0_57) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1176]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_3242,plain,
% 1.88/1.00      ( ~ r2_hidden(sK7,u1_struct_0(sK3))
% 1.88/1.00      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_2266]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_20,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.88/1.00      inference(cnf_transformation,[],[f88]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1165,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1641,plain,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1165]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_6,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f57]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1171,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0_57,X1_57)
% 1.88/1.00      | r2_hidden(X0_57,X1_57)
% 1.88/1.00      | v1_xboole_0(X1_57) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1636,plain,
% 1.88/1.00      ( m1_subset_1(X0_57,X1_57) != iProver_top
% 1.88/1.00      | r2_hidden(X0_57,X1_57) = iProver_top
% 1.88/1.00      | v1_xboole_0(X1_57) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2346,plain,
% 1.88/1.00      ( r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_1641,c_1636]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_29,negated_conjecture,
% 1.88/1.00      ( l1_pre_topc(sK3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_36,plain,
% 1.88/1.00      ( l1_pre_topc(sK3) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_45,plain,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_11,plain,
% 1.88/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.88/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ l1_pre_topc(X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_26,negated_conjecture,
% 1.88/1.00      ( m1_pre_topc(sK4,sK3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_730,plain,
% 1.88/1.00      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ l1_pre_topc(X1)
% 1.88/1.00      | sK4 != X0
% 1.88/1.00      | sK3 != X1 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_731,plain,
% 1.88/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ l1_pre_topc(sK3) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_730]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_732,plain,
% 1.88/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 1.88/1.00      | l1_pre_topc(sK3) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_16,plain,
% 1.88/1.00      ( ~ v3_tex_2(X0,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ v2_pre_topc(X1)
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ l1_pre_topc(X1)
% 1.88/1.00      | ~ v1_xboole_0(X0) ),
% 1.88/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_31,negated_conjecture,
% 1.88/1.00      ( v2_pre_topc(sK3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_451,plain,
% 1.88/1.00      ( ~ v3_tex_2(X0,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ l1_pre_topc(X1)
% 1.88/1.00      | ~ v1_xboole_0(X0)
% 1.88/1.00      | sK3 != X1 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_452,plain,
% 1.88/1.00      ( ~ v3_tex_2(X0,sK3)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | v2_struct_0(sK3)
% 1.88/1.00      | ~ l1_pre_topc(sK3)
% 1.88/1.00      | ~ v1_xboole_0(X0) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_451]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_32,negated_conjecture,
% 1.88/1.00      ( ~ v2_struct_0(sK3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_456,plain,
% 1.88/1.00      ( ~ v3_tex_2(X0,sK3)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ v1_xboole_0(X0) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_452,c_32,c_29]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_15,plain,
% 1.88/1.00      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.88/1.00      | ~ v4_tex_2(X0,X1)
% 1.88/1.00      | ~ m1_pre_topc(X0,X1)
% 1.88/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ l1_pre_topc(X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f89]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_178,plain,
% 1.88/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.88/1.00      | ~ v4_tex_2(X0,X1)
% 1.88/1.00      | v3_tex_2(u1_struct_0(X0),X1)
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ l1_pre_topc(X1) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_15,c_11]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_179,plain,
% 1.88/1.00      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.88/1.00      | ~ v4_tex_2(X0,X1)
% 1.88/1.00      | ~ m1_pre_topc(X0,X1)
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ l1_pre_topc(X1) ),
% 1.88/1.00      inference(renaming,[status(thm)],[c_178]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_715,plain,
% 1.88/1.00      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.88/1.00      | ~ v4_tex_2(X0,X1)
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | ~ l1_pre_topc(X1)
% 1.88/1.00      | sK4 != X0
% 1.88/1.00      | sK3 != X1 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_179,c_26]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_716,plain,
% 1.88/1.00      ( v3_tex_2(u1_struct_0(sK4),sK3)
% 1.88/1.00      | ~ v4_tex_2(sK4,sK3)
% 1.88/1.00      | v2_struct_0(sK3)
% 1.88/1.00      | ~ l1_pre_topc(sK3) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_715]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_27,negated_conjecture,
% 1.88/1.00      ( v4_tex_2(sK4,sK3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_718,plain,
% 1.88/1.00      ( v3_tex_2(u1_struct_0(sK4),sK3) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_716,c_32,c_29,c_27]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_772,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ v1_xboole_0(X0)
% 1.88/1.00      | u1_struct_0(sK4) != X0
% 1.88/1.00      | sK3 != sK3 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_456,c_718]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_773,plain,
% 1.88/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_772]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_774,plain,
% 1.88/1.00      ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1763,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0_57,u1_struct_0(sK4))
% 1.88/1.00      | r2_hidden(X0_57,u1_struct_0(sK4))
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1171]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1980,plain,
% 1.88/1.00      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 1.88/1.00      | r2_hidden(sK7,u1_struct_0(sK4))
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1763]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1981,plain,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 1.88/1.00      | r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2682,plain,
% 1.88/1.00      ( r2_hidden(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_2346,c_36,c_45,c_732,c_774,c_1981]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_5,plain,
% 1.88/1.00      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
% 1.88/1.00      | ~ r2_hidden(X0,X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f85]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1172,plain,
% 1.88/1.00      ( m1_subset_1(k2_tarski(X0_57,X0_57),k1_zfmisc_1(X1_57))
% 1.88/1.00      | ~ r2_hidden(X0_57,X1_57) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1635,plain,
% 1.88/1.00      ( m1_subset_1(k2_tarski(X0_57,X0_57),k1_zfmisc_1(X1_57)) = iProver_top
% 1.88/1.00      | r2_hidden(X0_57,X1_57) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_9,plain,
% 1.88/1.00      ( ~ m1_pre_topc(X0,X1)
% 1.88/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.88/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ l1_pre_topc(X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_741,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/1.00      | ~ l1_pre_topc(X2)
% 1.88/1.00      | sK4 != X1
% 1.88/1.00      | sK3 != X2 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_742,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.88/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ l1_pre_topc(sK3) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_741]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_746,plain,
% 1.88/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_742,c_29]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_747,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.88/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.88/1.00      inference(renaming,[status(thm)],[c_746]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_17,plain,
% 1.88/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.88/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.88/1.00      | ~ v3_borsuk_1(X0,X1,X2)
% 1.88/1.00      | ~ v4_tex_2(X2,X1)
% 1.88/1.00      | ~ m1_pre_topc(X2,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/1.00      | ~ v3_tdlat_3(X1)
% 1.88/1.00      | ~ v1_funct_1(X0)
% 1.88/1.00      | ~ v2_pre_topc(X1)
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | v2_struct_0(X2)
% 1.88/1.00      | ~ l1_pre_topc(X1)
% 1.88/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f90]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_21,negated_conjecture,
% 1.88/1.00      ( v3_borsuk_1(sK5,sK3,sK4) ),
% 1.88/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_426,plain,
% 1.88/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.88/1.00      | ~ v5_pre_topc(X0,X1,X2)
% 1.88/1.00      | ~ v4_tex_2(X2,X1)
% 1.88/1.00      | ~ m1_pre_topc(X2,X1)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.88/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.88/1.00      | ~ v3_tdlat_3(X1)
% 1.88/1.00      | ~ v1_funct_1(X0)
% 1.88/1.00      | ~ v2_pre_topc(X1)
% 1.88/1.00      | v2_struct_0(X1)
% 1.88/1.00      | v2_struct_0(X2)
% 1.88/1.00      | ~ l1_pre_topc(X1)
% 1.88/1.00      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 1.88/1.00      | sK5 != X0
% 1.88/1.00      | sK4 != X2
% 1.88/1.00      | sK3 != X1 ),
% 1.88/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_427,plain,
% 1.88/1.00      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 1.88/1.00      | ~ v5_pre_topc(sK5,sK3,sK4)
% 1.88/1.00      | ~ v4_tex_2(sK4,sK3)
% 1.88/1.00      | ~ m1_pre_topc(sK4,sK3)
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 1.88/1.00      | ~ v3_tdlat_3(sK3)
% 1.88/1.00      | ~ v1_funct_1(sK5)
% 1.88/1.00      | ~ v2_pre_topc(sK3)
% 1.88/1.00      | v2_struct_0(sK4)
% 1.88/1.00      | v2_struct_0(sK3)
% 1.88/1.00      | ~ l1_pre_topc(sK3)
% 1.88/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.88/1.00      inference(unflattening,[status(thm)],[c_426]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_30,negated_conjecture,
% 1.88/1.00      ( v3_tdlat_3(sK3) ),
% 1.88/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_28,negated_conjecture,
% 1.88/1.00      ( ~ v2_struct_0(sK4) ),
% 1.88/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_25,negated_conjecture,
% 1.88/1.00      ( v1_funct_1(sK5) ),
% 1.88/1.00      inference(cnf_transformation,[],[f76]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_24,negated_conjecture,
% 1.88/1.00      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 1.88/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_23,negated_conjecture,
% 1.88/1.00      ( v5_pre_topc(sK5,sK3,sK4) ),
% 1.88/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_22,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 1.88/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_431,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.88/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_427,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23,
% 1.88/1.00                 c_22]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_432,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.88/1.00      inference(renaming,[status(thm)],[c_431]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_767,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.88/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.88/1.00      inference(backward_subsumption_resolution,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_747,c_432]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1161,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.88/1.00      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_57) = k2_pre_topc(sK3,X0_57) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_767]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1645,plain,
% 1.88/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0_57) = k2_pre_topc(sK3,X0_57)
% 1.88/1.00      | m1_subset_1(X0_57,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1161]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1944,plain,
% 1.88/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_tarski(X0_57,X0_57)) = k2_pre_topc(sK3,k2_tarski(X0_57,X0_57))
% 1.88/1.00      | r2_hidden(X0_57,u1_struct_0(sK4)) != iProver_top ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_1635,c_1645]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2688,plain,
% 1.88/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_tarski(sK7,sK7)) = k2_pre_topc(sK3,k2_tarski(sK7,sK7)) ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_2682,c_1944]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_10,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,X1)
% 1.88/1.00      | v1_xboole_0(X1)
% 1.88/1.00      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.88/1.00      inference(cnf_transformation,[],[f86]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1168,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0_57,X1_57)
% 1.88/1.00      | v1_xboole_0(X1_57)
% 1.88/1.00      | k6_domain_1(X1_57,X0_57) = k2_tarski(X0_57,X0_57) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1639,plain,
% 1.88/1.00      ( k6_domain_1(X0_57,X1_57) = k2_tarski(X1_57,X1_57)
% 1.88/1.00      | m1_subset_1(X1_57,X0_57) != iProver_top
% 1.88/1.00      | v1_xboole_0(X0_57) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1168]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2541,plain,
% 1.88/1.00      ( k6_domain_1(u1_struct_0(sK4),sK7) = k2_tarski(sK7,sK7)
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_1641,c_1639]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1774,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0_57,u1_struct_0(sK4))
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4))
% 1.88/1.00      | k6_domain_1(u1_struct_0(sK4),X0_57) = k2_tarski(X0_57,X0_57) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1168]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2005,plain,
% 1.88/1.00      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK4))
% 1.88/1.00      | k6_domain_1(u1_struct_0(sK4),sK7) = k2_tarski(sK7,sK7) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1774]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2739,plain,
% 1.88/1.00      ( k6_domain_1(u1_struct_0(sK4),sK7) = k2_tarski(sK7,sK7) ),
% 1.88/1.00      inference(global_propositional_subsumption,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_2541,c_29,c_20,c_731,c_773,c_2005]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_18,negated_conjecture,
% 1.88/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 1.88/1.00      inference(cnf_transformation,[],[f87]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1167,negated_conjecture,
% 1.88/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2742,plain,
% 1.88/1.00      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k2_tarski(sK7,sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 1.88/1.00      inference(demodulation,[status(thm)],[c_2739,c_1167]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2938,plain,
% 1.88/1.00      ( k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) != k2_pre_topc(sK3,k2_tarski(sK7,sK7)) ),
% 1.88/1.00      inference(demodulation,[status(thm)],[c_2688,c_2742]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_4,plain,
% 1.88/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1173,plain,
% 1.88/1.00      ( ~ r1_tarski(X0_57,X1_57)
% 1.88/1.00      | ~ r2_hidden(X2_57,X0_57)
% 1.88/1.00      | r2_hidden(X2_57,X1_57) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2042,plain,
% 1.88/1.00      ( ~ r1_tarski(u1_struct_0(sK4),X0_57)
% 1.88/1.00      | r2_hidden(sK7,X0_57)
% 1.88/1.00      | ~ r2_hidden(sK7,u1_struct_0(sK4)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1173]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2697,plain,
% 1.88/1.00      ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3))
% 1.88/1.00      | ~ r2_hidden(sK7,u1_struct_0(sK4))
% 1.88/1.00      | r2_hidden(sK7,u1_struct_0(sK3)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_2042]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_19,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.88/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1166,negated_conjecture,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1640,plain,
% 1.88/1.00      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1166]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2540,plain,
% 1.88/1.00      ( k6_domain_1(u1_struct_0(sK3),sK7) = k2_tarski(sK7,sK7)
% 1.88/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.88/1.00      inference(superposition,[status(thm)],[c_1640,c_1639]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2588,plain,
% 1.88/1.00      ( v1_xboole_0(u1_struct_0(sK3))
% 1.88/1.00      | k6_domain_1(u1_struct_0(sK3),sK7) = k2_tarski(sK7,sK7) ),
% 1.88/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2540]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_8,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.88/1.00      inference(cnf_transformation,[],[f58]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_1169,plain,
% 1.88/1.00      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 1.88/1.00      | r1_tarski(X0_57,X1_57) ),
% 1.88/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2014,plain,
% 1.88/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(X0_57))
% 1.88/1.00      | r1_tarski(u1_struct_0(sK4),X0_57) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_1169]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(c_2205,plain,
% 1.88/1.00      ( ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.88/1.00      | r1_tarski(u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 1.88/1.00      inference(instantiation,[status(thm)],[c_2014]) ).
% 1.88/1.00  
% 1.88/1.00  cnf(contradiction,plain,
% 1.88/1.00      ( $false ),
% 1.88/1.00      inference(minisat,
% 1.88/1.00                [status(thm)],
% 1.88/1.00                [c_3414,c_3242,c_2938,c_2697,c_2588,c_2205,c_1980,c_773,
% 1.88/1.00                 c_731,c_20,c_29]) ).
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/1.00  
% 1.88/1.00  ------                               Statistics
% 1.88/1.00  
% 1.88/1.00  ------ General
% 1.88/1.00  
% 1.88/1.00  abstr_ref_over_cycles:                  0
% 1.88/1.00  abstr_ref_under_cycles:                 0
% 1.88/1.00  gc_basic_clause_elim:                   0
% 1.88/1.00  forced_gc_time:                         0
% 1.88/1.00  parsing_time:                           0.012
% 1.88/1.00  unif_index_cands_time:                  0.
% 1.88/1.00  unif_index_add_time:                    0.
% 1.88/1.00  orderings_time:                         0.
% 1.88/1.00  out_proof_time:                         0.012
% 1.88/1.00  total_time:                             0.126
% 1.88/1.00  num_of_symbols:                         66
% 1.88/1.00  num_of_terms:                           2344
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing
% 1.88/1.00  
% 1.88/1.00  num_of_splits:                          0
% 1.88/1.00  num_of_split_atoms:                     0
% 1.88/1.00  num_of_reused_defs:                     0
% 1.88/1.00  num_eq_ax_congr_red:                    30
% 1.88/1.00  num_of_sem_filtered_clauses:            1
% 1.88/1.00  num_of_subtypes:                        3
% 1.88/1.00  monotx_restored_types:                  0
% 1.88/1.00  sat_num_of_epr_types:                   0
% 1.88/1.00  sat_num_of_non_cyclic_types:            0
% 1.88/1.00  sat_guarded_non_collapsed_types:        0
% 1.88/1.00  num_pure_diseq_elim:                    0
% 1.88/1.00  simp_replaced_by:                       0
% 1.88/1.00  res_preprocessed:                       112
% 1.88/1.00  prep_upred:                             0
% 1.88/1.00  prep_unflattend:                        31
% 1.88/1.00  smt_new_axioms:                         0
% 1.88/1.00  pred_elim_cands:                        4
% 1.88/1.00  pred_elim:                              11
% 1.88/1.00  pred_elim_cl:                           15
% 1.88/1.00  pred_elim_cycles:                       17
% 1.88/1.00  merged_defs:                            8
% 1.88/1.00  merged_defs_ncl:                        0
% 1.88/1.00  bin_hyper_res:                          8
% 1.88/1.00  prep_cycles:                            4
% 1.88/1.00  pred_elim_time:                         0.009
% 1.88/1.00  splitting_time:                         0.
% 1.88/1.00  sem_filter_time:                        0.
% 1.88/1.00  monotx_time:                            0.
% 1.88/1.00  subtype_inf_time:                       0.
% 1.88/1.00  
% 1.88/1.00  ------ Problem properties
% 1.88/1.00  
% 1.88/1.00  clauses:                                18
% 1.88/1.00  conjectures:                            4
% 1.88/1.00  epr:                                    3
% 1.88/1.00  horn:                                   14
% 1.88/1.00  ground:                                 6
% 1.88/1.00  unary:                                  6
% 1.88/1.00  binary:                                 9
% 1.88/1.00  lits:                                   33
% 1.88/1.00  lits_eq:                                3
% 1.88/1.00  fd_pure:                                0
% 1.88/1.00  fd_pseudo:                              0
% 1.88/1.00  fd_cond:                                0
% 1.88/1.00  fd_pseudo_cond:                         0
% 1.88/1.00  ac_symbols:                             0
% 1.88/1.00  
% 1.88/1.00  ------ Propositional Solver
% 1.88/1.00  
% 1.88/1.00  prop_solver_calls:                      29
% 1.88/1.00  prop_fast_solver_calls:                 730
% 1.88/1.00  smt_solver_calls:                       0
% 1.88/1.00  smt_fast_solver_calls:                  0
% 1.88/1.00  prop_num_of_clauses:                    908
% 1.88/1.00  prop_preprocess_simplified:             3685
% 1.88/1.00  prop_fo_subsumed:                       26
% 1.88/1.00  prop_solver_time:                       0.
% 1.88/1.00  smt_solver_time:                        0.
% 1.88/1.00  smt_fast_solver_time:                   0.
% 1.88/1.00  prop_fast_solver_time:                  0.
% 1.88/1.00  prop_unsat_core_time:                   0.
% 1.88/1.00  
% 1.88/1.00  ------ QBF
% 1.88/1.00  
% 1.88/1.00  qbf_q_res:                              0
% 1.88/1.00  qbf_num_tautologies:                    0
% 1.88/1.00  qbf_prep_cycles:                        0
% 1.88/1.00  
% 1.88/1.00  ------ BMC1
% 1.88/1.00  
% 1.88/1.00  bmc1_current_bound:                     -1
% 1.88/1.00  bmc1_last_solved_bound:                 -1
% 1.88/1.00  bmc1_unsat_core_size:                   -1
% 1.88/1.00  bmc1_unsat_core_parents_size:           -1
% 1.88/1.00  bmc1_merge_next_fun:                    0
% 1.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.88/1.00  
% 1.88/1.00  ------ Instantiation
% 1.88/1.00  
% 1.88/1.00  inst_num_of_clauses:                    230
% 1.88/1.00  inst_num_in_passive:                    23
% 1.88/1.00  inst_num_in_active:                     188
% 1.88/1.00  inst_num_in_unprocessed:                18
% 1.88/1.00  inst_num_of_loops:                      248
% 1.88/1.00  inst_num_of_learning_restarts:          0
% 1.88/1.00  inst_num_moves_active_passive:          54
% 1.88/1.00  inst_lit_activity:                      0
% 1.88/1.00  inst_lit_activity_moves:                0
% 1.88/1.00  inst_num_tautologies:                   0
% 1.88/1.00  inst_num_prop_implied:                  0
% 1.88/1.00  inst_num_existing_simplified:           0
% 1.88/1.00  inst_num_eq_res_simplified:             0
% 1.88/1.00  inst_num_child_elim:                    0
% 1.88/1.00  inst_num_of_dismatching_blockings:      104
% 1.88/1.00  inst_num_of_non_proper_insts:           323
% 1.88/1.00  inst_num_of_duplicates:                 0
% 1.88/1.00  inst_inst_num_from_inst_to_res:         0
% 1.88/1.00  inst_dismatching_checking_time:         0.
% 1.88/1.00  
% 1.88/1.00  ------ Resolution
% 1.88/1.00  
% 1.88/1.00  res_num_of_clauses:                     0
% 1.88/1.00  res_num_in_passive:                     0
% 1.88/1.00  res_num_in_active:                      0
% 1.88/1.00  res_num_of_loops:                       116
% 1.88/1.00  res_forward_subset_subsumed:            64
% 1.88/1.00  res_backward_subset_subsumed:           2
% 1.88/1.00  res_forward_subsumed:                   0
% 1.88/1.00  res_backward_subsumed:                  0
% 1.88/1.00  res_forward_subsumption_resolution:     0
% 1.88/1.00  res_backward_subsumption_resolution:    1
% 1.88/1.00  res_clause_to_clause_subsumption:       135
% 1.88/1.00  res_orphan_elimination:                 0
% 1.88/1.00  res_tautology_del:                      79
% 1.88/1.00  res_num_eq_res_simplified:              0
% 1.88/1.00  res_num_sel_changes:                    0
% 1.88/1.00  res_moves_from_active_to_pass:          0
% 1.88/1.00  
% 1.88/1.00  ------ Superposition
% 1.88/1.00  
% 1.88/1.00  sup_time_total:                         0.
% 1.88/1.00  sup_time_generating:                    0.
% 1.88/1.00  sup_time_sim_full:                      0.
% 1.88/1.00  sup_time_sim_immed:                     0.
% 1.88/1.00  
% 1.88/1.00  sup_num_of_clauses:                     65
% 1.88/1.00  sup_num_in_active:                      44
% 1.88/1.00  sup_num_in_passive:                     21
% 1.88/1.00  sup_num_of_loops:                       48
% 1.88/1.00  sup_fw_superposition:                   34
% 1.88/1.00  sup_bw_superposition:                   26
% 1.88/1.00  sup_immediate_simplified:               3
% 1.88/1.00  sup_given_eliminated:                   0
% 1.88/1.00  comparisons_done:                       0
% 1.88/1.00  comparisons_avoided:                    3
% 1.88/1.00  
% 1.88/1.00  ------ Simplifications
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  sim_fw_subset_subsumed:                 1
% 1.88/1.00  sim_bw_subset_subsumed:                 3
% 1.88/1.00  sim_fw_subsumed:                        2
% 1.88/1.00  sim_bw_subsumed:                        0
% 1.88/1.00  sim_fw_subsumption_res:                 0
% 1.88/1.00  sim_bw_subsumption_res:                 0
% 1.88/1.00  sim_tautology_del:                      7
% 1.88/1.00  sim_eq_tautology_del:                   0
% 1.88/1.00  sim_eq_res_simp:                        0
% 1.88/1.00  sim_fw_demodulated:                     0
% 1.88/1.00  sim_bw_demodulated:                     2
% 1.88/1.00  sim_light_normalised:                   0
% 1.88/1.00  sim_joinable_taut:                      0
% 1.88/1.00  sim_joinable_simp:                      0
% 1.88/1.00  sim_ac_normalised:                      0
% 1.88/1.00  sim_smt_subsumption:                    0
% 1.88/1.00  
%------------------------------------------------------------------------------
