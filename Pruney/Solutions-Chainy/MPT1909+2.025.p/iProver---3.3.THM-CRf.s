%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:58 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 977 expanded)
%              Number of clauses        :   76 ( 188 expanded)
%              Number of leaves         :   18 ( 394 expanded)
%              Depth                    :   21
%              Number of atoms          :  657 (11305 expanded)
%              Number of equality atoms :  116 (1999 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6))
        & sK6 = X3
        & m1_subset_1(sK6,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f27,f40,f39,f38,f37,f36])).

fof(f70,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK1(X0,X1),X0)
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f61,plain,(
    v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f67,plain,(
    v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f58,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f41])).

fof(f73,plain,(
    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(definition_unfolding,[],[f71,f70])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_576,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_784,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | v1_xboole_0(X1_55)
    | k2_tarski(X0_55,X0_55) = k6_domain_1(X1_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_782,plain,
    ( k2_tarski(X0_55,X0_55) = k6_domain_1(X1_55,X0_55)
    | m1_subset_1(X0_55,X1_55) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_1115,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK6) = k2_tarski(sK6,sK6)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_784,c_782])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_442,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_443,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_444,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_11,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_342,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_343,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_347,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_27,c_24])).

cnf(c_10,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_150,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_6])).

cnf(c_151,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_427,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_151,c_21])).

cnf(c_428,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2)
    | ~ v4_tex_2(sK3,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_22,negated_conjecture,
    ( v4_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_430,plain,
    ( v3_tex_2(u1_struct_0(sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_27,c_24,c_22])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_347,c_430])).

cnf(c_485,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_486,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_1280,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK6) = k2_tarski(sK6,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1115,c_31,c_444,c_486])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0_55,X1_55)
    | m1_subset_1(k6_domain_1(X1_55,X0_55),k1_zfmisc_1(X1_55))
    | v1_xboole_0(X1_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_781,plain,
    ( m1_subset_1(X0_55,X1_55) != iProver_top
    | m1_subset_1(k6_domain_1(X1_55,X0_55),k1_zfmisc_1(X1_55)) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(c_1284,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_781])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1366,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1284,c_31,c_40,c_444,c_486])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK3 != X1
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_458,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_24])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_16,negated_conjecture,
    ( v3_borsuk_1(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_317,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_318,plain,
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
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_25,negated_conjecture,
    ( v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,negated_conjecture,
    ( v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_459,c_323])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55) ),
    inference(subtyping,[status(esa)],[c_479])).

cnf(c_789,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55)
    | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1371,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6)) = k2_pre_topc(sK2,k2_tarski(sK6,sK6)) ),
    inference(superposition,[status(thm)],[c_1366,c_789])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_577,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_783,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_1114,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK6) = k2_tarski(sK6,sK6)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_783,c_782])).

cnf(c_1143,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK6) = k2_tarski(sK6,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1114])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ v1_xboole_0(X1_55)
    | v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_301])).

cnf(c_1055,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_55)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_1210,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_1232,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK6) = k2_tarski(sK6,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1114,c_24,c_443,c_485,c_1143,c_1210])).

cnf(c_13,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_578,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1235,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) ),
    inference(demodulation,[status(thm)],[c_1232,c_578])).

cnf(c_1283,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) ),
    inference(demodulation,[status(thm)],[c_1280,c_1235])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1371,c_1283])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.80/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.07  
% 1.80/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.80/1.07  
% 1.80/1.07  ------  iProver source info
% 1.80/1.07  
% 1.80/1.07  git: date: 2020-06-30 10:37:57 +0100
% 1.80/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.80/1.07  git: non_committed_changes: false
% 1.80/1.07  git: last_make_outside_of_git: false
% 1.80/1.07  
% 1.80/1.07  ------ 
% 1.80/1.07  
% 1.80/1.07  ------ Input Options
% 1.80/1.07  
% 1.80/1.07  --out_options                           all
% 1.80/1.07  --tptp_safe_out                         true
% 1.80/1.07  --problem_path                          ""
% 1.80/1.07  --include_path                          ""
% 1.80/1.07  --clausifier                            res/vclausify_rel
% 1.80/1.07  --clausifier_options                    --mode clausify
% 1.80/1.07  --stdin                                 false
% 1.80/1.07  --stats_out                             all
% 1.80/1.07  
% 1.80/1.07  ------ General Options
% 1.80/1.07  
% 1.80/1.07  --fof                                   false
% 1.80/1.07  --time_out_real                         305.
% 1.80/1.07  --time_out_virtual                      -1.
% 1.80/1.07  --symbol_type_check                     false
% 1.80/1.07  --clausify_out                          false
% 1.80/1.07  --sig_cnt_out                           false
% 1.80/1.07  --trig_cnt_out                          false
% 1.80/1.07  --trig_cnt_out_tolerance                1.
% 1.80/1.07  --trig_cnt_out_sk_spl                   false
% 1.80/1.07  --abstr_cl_out                          false
% 1.80/1.07  
% 1.80/1.07  ------ Global Options
% 1.80/1.07  
% 1.80/1.07  --schedule                              default
% 1.80/1.07  --add_important_lit                     false
% 1.80/1.07  --prop_solver_per_cl                    1000
% 1.80/1.07  --min_unsat_core                        false
% 1.80/1.07  --soft_assumptions                      false
% 1.80/1.07  --soft_lemma_size                       3
% 1.80/1.07  --prop_impl_unit_size                   0
% 1.80/1.07  --prop_impl_unit                        []
% 1.80/1.07  --share_sel_clauses                     true
% 1.80/1.07  --reset_solvers                         false
% 1.80/1.07  --bc_imp_inh                            [conj_cone]
% 1.80/1.07  --conj_cone_tolerance                   3.
% 1.80/1.07  --extra_neg_conj                        none
% 1.80/1.07  --large_theory_mode                     true
% 1.80/1.07  --prolific_symb_bound                   200
% 1.80/1.07  --lt_threshold                          2000
% 1.80/1.07  --clause_weak_htbl                      true
% 1.80/1.07  --gc_record_bc_elim                     false
% 1.80/1.07  
% 1.80/1.07  ------ Preprocessing Options
% 1.80/1.07  
% 1.80/1.07  --preprocessing_flag                    true
% 1.80/1.07  --time_out_prep_mult                    0.1
% 1.80/1.07  --splitting_mode                        input
% 1.80/1.07  --splitting_grd                         true
% 1.80/1.07  --splitting_cvd                         false
% 1.80/1.07  --splitting_cvd_svl                     false
% 1.80/1.07  --splitting_nvd                         32
% 1.80/1.07  --sub_typing                            true
% 1.80/1.07  --prep_gs_sim                           true
% 1.80/1.07  --prep_unflatten                        true
% 1.80/1.07  --prep_res_sim                          true
% 1.80/1.07  --prep_upred                            true
% 1.80/1.07  --prep_sem_filter                       exhaustive
% 1.80/1.07  --prep_sem_filter_out                   false
% 1.80/1.07  --pred_elim                             true
% 1.80/1.07  --res_sim_input                         true
% 1.80/1.07  --eq_ax_congr_red                       true
% 1.80/1.07  --pure_diseq_elim                       true
% 1.80/1.07  --brand_transform                       false
% 1.80/1.07  --non_eq_to_eq                          false
% 1.80/1.07  --prep_def_merge                        true
% 1.80/1.07  --prep_def_merge_prop_impl              false
% 1.80/1.07  --prep_def_merge_mbd                    true
% 1.80/1.07  --prep_def_merge_tr_red                 false
% 1.80/1.07  --prep_def_merge_tr_cl                  false
% 1.80/1.07  --smt_preprocessing                     true
% 1.80/1.07  --smt_ac_axioms                         fast
% 1.80/1.07  --preprocessed_out                      false
% 1.80/1.07  --preprocessed_stats                    false
% 1.80/1.07  
% 1.80/1.07  ------ Abstraction refinement Options
% 1.80/1.07  
% 1.80/1.07  --abstr_ref                             []
% 1.80/1.07  --abstr_ref_prep                        false
% 1.80/1.07  --abstr_ref_until_sat                   false
% 1.80/1.07  --abstr_ref_sig_restrict                funpre
% 1.80/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/1.07  --abstr_ref_under                       []
% 1.80/1.07  
% 1.80/1.07  ------ SAT Options
% 1.80/1.07  
% 1.80/1.07  --sat_mode                              false
% 1.80/1.07  --sat_fm_restart_options                ""
% 1.80/1.07  --sat_gr_def                            false
% 1.80/1.07  --sat_epr_types                         true
% 1.80/1.07  --sat_non_cyclic_types                  false
% 1.80/1.07  --sat_finite_models                     false
% 1.80/1.07  --sat_fm_lemmas                         false
% 1.80/1.07  --sat_fm_prep                           false
% 1.80/1.07  --sat_fm_uc_incr                        true
% 1.80/1.07  --sat_out_model                         small
% 1.80/1.07  --sat_out_clauses                       false
% 1.80/1.07  
% 1.80/1.07  ------ QBF Options
% 1.80/1.07  
% 1.80/1.07  --qbf_mode                              false
% 1.80/1.07  --qbf_elim_univ                         false
% 1.80/1.07  --qbf_dom_inst                          none
% 1.80/1.07  --qbf_dom_pre_inst                      false
% 1.80/1.07  --qbf_sk_in                             false
% 1.80/1.07  --qbf_pred_elim                         true
% 1.80/1.07  --qbf_split                             512
% 1.80/1.07  
% 1.80/1.07  ------ BMC1 Options
% 1.80/1.07  
% 1.80/1.07  --bmc1_incremental                      false
% 1.80/1.07  --bmc1_axioms                           reachable_all
% 1.80/1.07  --bmc1_min_bound                        0
% 1.80/1.07  --bmc1_max_bound                        -1
% 1.80/1.07  --bmc1_max_bound_default                -1
% 1.80/1.07  --bmc1_symbol_reachability              true
% 1.80/1.07  --bmc1_property_lemmas                  false
% 1.80/1.07  --bmc1_k_induction                      false
% 1.80/1.07  --bmc1_non_equiv_states                 false
% 1.80/1.07  --bmc1_deadlock                         false
% 1.80/1.07  --bmc1_ucm                              false
% 1.80/1.07  --bmc1_add_unsat_core                   none
% 1.80/1.07  --bmc1_unsat_core_children              false
% 1.80/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/1.07  --bmc1_out_stat                         full
% 1.80/1.07  --bmc1_ground_init                      false
% 1.80/1.07  --bmc1_pre_inst_next_state              false
% 1.80/1.07  --bmc1_pre_inst_state                   false
% 1.80/1.07  --bmc1_pre_inst_reach_state             false
% 1.80/1.07  --bmc1_out_unsat_core                   false
% 1.80/1.07  --bmc1_aig_witness_out                  false
% 1.80/1.07  --bmc1_verbose                          false
% 1.80/1.07  --bmc1_dump_clauses_tptp                false
% 1.80/1.07  --bmc1_dump_unsat_core_tptp             false
% 1.80/1.07  --bmc1_dump_file                        -
% 1.80/1.07  --bmc1_ucm_expand_uc_limit              128
% 1.80/1.07  --bmc1_ucm_n_expand_iterations          6
% 1.80/1.07  --bmc1_ucm_extend_mode                  1
% 1.80/1.07  --bmc1_ucm_init_mode                    2
% 1.80/1.07  --bmc1_ucm_cone_mode                    none
% 1.80/1.07  --bmc1_ucm_reduced_relation_type        0
% 1.80/1.07  --bmc1_ucm_relax_model                  4
% 1.80/1.07  --bmc1_ucm_full_tr_after_sat            true
% 1.80/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/1.07  --bmc1_ucm_layered_model                none
% 1.80/1.07  --bmc1_ucm_max_lemma_size               10
% 1.80/1.07  
% 1.80/1.07  ------ AIG Options
% 1.80/1.07  
% 1.80/1.07  --aig_mode                              false
% 1.80/1.07  
% 1.80/1.07  ------ Instantiation Options
% 1.80/1.07  
% 1.80/1.07  --instantiation_flag                    true
% 1.80/1.07  --inst_sos_flag                         false
% 1.80/1.07  --inst_sos_phase                        true
% 1.80/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/1.07  --inst_lit_sel_side                     num_symb
% 1.80/1.07  --inst_solver_per_active                1400
% 1.80/1.07  --inst_solver_calls_frac                1.
% 1.80/1.07  --inst_passive_queue_type               priority_queues
% 1.80/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/1.07  --inst_passive_queues_freq              [25;2]
% 1.80/1.07  --inst_dismatching                      true
% 1.80/1.07  --inst_eager_unprocessed_to_passive     true
% 1.80/1.07  --inst_prop_sim_given                   true
% 1.80/1.07  --inst_prop_sim_new                     false
% 1.80/1.07  --inst_subs_new                         false
% 1.80/1.07  --inst_eq_res_simp                      false
% 1.80/1.07  --inst_subs_given                       false
% 1.80/1.07  --inst_orphan_elimination               true
% 1.80/1.07  --inst_learning_loop_flag               true
% 1.80/1.07  --inst_learning_start                   3000
% 1.80/1.07  --inst_learning_factor                  2
% 1.80/1.07  --inst_start_prop_sim_after_learn       3
% 1.80/1.07  --inst_sel_renew                        solver
% 1.80/1.07  --inst_lit_activity_flag                true
% 1.80/1.07  --inst_restr_to_given                   false
% 1.80/1.07  --inst_activity_threshold               500
% 1.80/1.07  --inst_out_proof                        true
% 1.80/1.07  
% 1.80/1.07  ------ Resolution Options
% 1.80/1.07  
% 1.80/1.07  --resolution_flag                       true
% 1.80/1.07  --res_lit_sel                           adaptive
% 1.80/1.07  --res_lit_sel_side                      none
% 1.80/1.07  --res_ordering                          kbo
% 1.80/1.07  --res_to_prop_solver                    active
% 1.80/1.07  --res_prop_simpl_new                    false
% 1.80/1.07  --res_prop_simpl_given                  true
% 1.80/1.07  --res_passive_queue_type                priority_queues
% 1.80/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/1.07  --res_passive_queues_freq               [15;5]
% 1.80/1.07  --res_forward_subs                      full
% 1.80/1.07  --res_backward_subs                     full
% 1.80/1.07  --res_forward_subs_resolution           true
% 1.80/1.07  --res_backward_subs_resolution          true
% 1.80/1.07  --res_orphan_elimination                true
% 1.80/1.07  --res_time_limit                        2.
% 1.80/1.07  --res_out_proof                         true
% 1.80/1.07  
% 1.80/1.07  ------ Superposition Options
% 1.80/1.07  
% 1.80/1.07  --superposition_flag                    true
% 1.80/1.07  --sup_passive_queue_type                priority_queues
% 1.80/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/1.07  --sup_passive_queues_freq               [8;1;4]
% 1.80/1.07  --demod_completeness_check              fast
% 1.80/1.07  --demod_use_ground                      true
% 1.80/1.07  --sup_to_prop_solver                    passive
% 1.80/1.07  --sup_prop_simpl_new                    true
% 1.80/1.07  --sup_prop_simpl_given                  true
% 1.80/1.07  --sup_fun_splitting                     false
% 1.80/1.07  --sup_smt_interval                      50000
% 1.80/1.07  
% 1.80/1.07  ------ Superposition Simplification Setup
% 1.80/1.07  
% 1.80/1.07  --sup_indices_passive                   []
% 1.80/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.07  --sup_full_bw                           [BwDemod]
% 1.80/1.07  --sup_immed_triv                        [TrivRules]
% 1.80/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.07  --sup_immed_bw_main                     []
% 1.80/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.07  
% 1.80/1.07  ------ Combination Options
% 1.80/1.07  
% 1.80/1.07  --comb_res_mult                         3
% 1.80/1.07  --comb_sup_mult                         2
% 1.80/1.07  --comb_inst_mult                        10
% 1.80/1.07  
% 1.80/1.07  ------ Debug Options
% 1.80/1.07  
% 1.80/1.07  --dbg_backtrace                         false
% 1.80/1.07  --dbg_dump_prop_clauses                 false
% 1.80/1.07  --dbg_dump_prop_clauses_file            -
% 1.80/1.07  --dbg_out_stat                          false
% 1.80/1.07  ------ Parsing...
% 1.80/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.80/1.07  
% 1.80/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 13 0s  sf_e  pe_s  pe_e 
% 1.80/1.07  
% 1.80/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.80/1.07  
% 1.80/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.80/1.07  ------ Proving...
% 1.80/1.07  ------ Problem Properties 
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  clauses                                 11
% 1.80/1.07  conjectures                             4
% 1.80/1.07  EPR                                     0
% 1.80/1.07  Horn                                    9
% 1.80/1.07  unary                                   6
% 1.80/1.07  binary                                  2
% 1.80/1.07  lits                                    19
% 1.80/1.07  lits eq                                 3
% 1.80/1.07  fd_pure                                 0
% 1.80/1.07  fd_pseudo                               0
% 1.80/1.07  fd_cond                                 0
% 1.80/1.07  fd_pseudo_cond                          0
% 1.80/1.07  AC symbols                              0
% 1.80/1.07  
% 1.80/1.07  ------ Schedule dynamic 5 is on 
% 1.80/1.07  
% 1.80/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  ------ 
% 1.80/1.07  Current options:
% 1.80/1.07  ------ 
% 1.80/1.07  
% 1.80/1.07  ------ Input Options
% 1.80/1.07  
% 1.80/1.07  --out_options                           all
% 1.80/1.07  --tptp_safe_out                         true
% 1.80/1.07  --problem_path                          ""
% 1.80/1.07  --include_path                          ""
% 1.80/1.07  --clausifier                            res/vclausify_rel
% 1.80/1.07  --clausifier_options                    --mode clausify
% 1.80/1.07  --stdin                                 false
% 1.80/1.07  --stats_out                             all
% 1.80/1.07  
% 1.80/1.07  ------ General Options
% 1.80/1.07  
% 1.80/1.07  --fof                                   false
% 1.80/1.07  --time_out_real                         305.
% 1.80/1.07  --time_out_virtual                      -1.
% 1.80/1.07  --symbol_type_check                     false
% 1.80/1.07  --clausify_out                          false
% 1.80/1.07  --sig_cnt_out                           false
% 1.80/1.07  --trig_cnt_out                          false
% 1.80/1.07  --trig_cnt_out_tolerance                1.
% 1.80/1.07  --trig_cnt_out_sk_spl                   false
% 1.80/1.07  --abstr_cl_out                          false
% 1.80/1.07  
% 1.80/1.07  ------ Global Options
% 1.80/1.07  
% 1.80/1.07  --schedule                              default
% 1.80/1.07  --add_important_lit                     false
% 1.80/1.07  --prop_solver_per_cl                    1000
% 1.80/1.07  --min_unsat_core                        false
% 1.80/1.07  --soft_assumptions                      false
% 1.80/1.07  --soft_lemma_size                       3
% 1.80/1.07  --prop_impl_unit_size                   0
% 1.80/1.07  --prop_impl_unit                        []
% 1.80/1.07  --share_sel_clauses                     true
% 1.80/1.07  --reset_solvers                         false
% 1.80/1.07  --bc_imp_inh                            [conj_cone]
% 1.80/1.07  --conj_cone_tolerance                   3.
% 1.80/1.07  --extra_neg_conj                        none
% 1.80/1.07  --large_theory_mode                     true
% 1.80/1.07  --prolific_symb_bound                   200
% 1.80/1.07  --lt_threshold                          2000
% 1.80/1.07  --clause_weak_htbl                      true
% 1.80/1.07  --gc_record_bc_elim                     false
% 1.80/1.07  
% 1.80/1.07  ------ Preprocessing Options
% 1.80/1.07  
% 1.80/1.07  --preprocessing_flag                    true
% 1.80/1.07  --time_out_prep_mult                    0.1
% 1.80/1.07  --splitting_mode                        input
% 1.80/1.07  --splitting_grd                         true
% 1.80/1.07  --splitting_cvd                         false
% 1.80/1.07  --splitting_cvd_svl                     false
% 1.80/1.07  --splitting_nvd                         32
% 1.80/1.07  --sub_typing                            true
% 1.80/1.07  --prep_gs_sim                           true
% 1.80/1.07  --prep_unflatten                        true
% 1.80/1.07  --prep_res_sim                          true
% 1.80/1.07  --prep_upred                            true
% 1.80/1.07  --prep_sem_filter                       exhaustive
% 1.80/1.07  --prep_sem_filter_out                   false
% 1.80/1.07  --pred_elim                             true
% 1.80/1.07  --res_sim_input                         true
% 1.80/1.07  --eq_ax_congr_red                       true
% 1.80/1.07  --pure_diseq_elim                       true
% 1.80/1.07  --brand_transform                       false
% 1.80/1.07  --non_eq_to_eq                          false
% 1.80/1.07  --prep_def_merge                        true
% 1.80/1.07  --prep_def_merge_prop_impl              false
% 1.80/1.07  --prep_def_merge_mbd                    true
% 1.80/1.07  --prep_def_merge_tr_red                 false
% 1.80/1.07  --prep_def_merge_tr_cl                  false
% 1.80/1.07  --smt_preprocessing                     true
% 1.80/1.07  --smt_ac_axioms                         fast
% 1.80/1.07  --preprocessed_out                      false
% 1.80/1.07  --preprocessed_stats                    false
% 1.80/1.07  
% 1.80/1.07  ------ Abstraction refinement Options
% 1.80/1.07  
% 1.80/1.07  --abstr_ref                             []
% 1.80/1.07  --abstr_ref_prep                        false
% 1.80/1.07  --abstr_ref_until_sat                   false
% 1.80/1.07  --abstr_ref_sig_restrict                funpre
% 1.80/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 1.80/1.07  --abstr_ref_under                       []
% 1.80/1.07  
% 1.80/1.07  ------ SAT Options
% 1.80/1.07  
% 1.80/1.07  --sat_mode                              false
% 1.80/1.07  --sat_fm_restart_options                ""
% 1.80/1.07  --sat_gr_def                            false
% 1.80/1.07  --sat_epr_types                         true
% 1.80/1.07  --sat_non_cyclic_types                  false
% 1.80/1.07  --sat_finite_models                     false
% 1.80/1.07  --sat_fm_lemmas                         false
% 1.80/1.07  --sat_fm_prep                           false
% 1.80/1.07  --sat_fm_uc_incr                        true
% 1.80/1.07  --sat_out_model                         small
% 1.80/1.07  --sat_out_clauses                       false
% 1.80/1.07  
% 1.80/1.07  ------ QBF Options
% 1.80/1.07  
% 1.80/1.07  --qbf_mode                              false
% 1.80/1.07  --qbf_elim_univ                         false
% 1.80/1.07  --qbf_dom_inst                          none
% 1.80/1.07  --qbf_dom_pre_inst                      false
% 1.80/1.07  --qbf_sk_in                             false
% 1.80/1.07  --qbf_pred_elim                         true
% 1.80/1.07  --qbf_split                             512
% 1.80/1.07  
% 1.80/1.07  ------ BMC1 Options
% 1.80/1.07  
% 1.80/1.07  --bmc1_incremental                      false
% 1.80/1.07  --bmc1_axioms                           reachable_all
% 1.80/1.07  --bmc1_min_bound                        0
% 1.80/1.07  --bmc1_max_bound                        -1
% 1.80/1.07  --bmc1_max_bound_default                -1
% 1.80/1.07  --bmc1_symbol_reachability              true
% 1.80/1.07  --bmc1_property_lemmas                  false
% 1.80/1.07  --bmc1_k_induction                      false
% 1.80/1.07  --bmc1_non_equiv_states                 false
% 1.80/1.07  --bmc1_deadlock                         false
% 1.80/1.07  --bmc1_ucm                              false
% 1.80/1.07  --bmc1_add_unsat_core                   none
% 1.80/1.07  --bmc1_unsat_core_children              false
% 1.80/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 1.80/1.07  --bmc1_out_stat                         full
% 1.80/1.07  --bmc1_ground_init                      false
% 1.80/1.07  --bmc1_pre_inst_next_state              false
% 1.80/1.07  --bmc1_pre_inst_state                   false
% 1.80/1.07  --bmc1_pre_inst_reach_state             false
% 1.80/1.07  --bmc1_out_unsat_core                   false
% 1.80/1.07  --bmc1_aig_witness_out                  false
% 1.80/1.07  --bmc1_verbose                          false
% 1.80/1.07  --bmc1_dump_clauses_tptp                false
% 1.80/1.07  --bmc1_dump_unsat_core_tptp             false
% 1.80/1.07  --bmc1_dump_file                        -
% 1.80/1.07  --bmc1_ucm_expand_uc_limit              128
% 1.80/1.07  --bmc1_ucm_n_expand_iterations          6
% 1.80/1.07  --bmc1_ucm_extend_mode                  1
% 1.80/1.07  --bmc1_ucm_init_mode                    2
% 1.80/1.07  --bmc1_ucm_cone_mode                    none
% 1.80/1.07  --bmc1_ucm_reduced_relation_type        0
% 1.80/1.07  --bmc1_ucm_relax_model                  4
% 1.80/1.07  --bmc1_ucm_full_tr_after_sat            true
% 1.80/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 1.80/1.07  --bmc1_ucm_layered_model                none
% 1.80/1.07  --bmc1_ucm_max_lemma_size               10
% 1.80/1.07  
% 1.80/1.07  ------ AIG Options
% 1.80/1.07  
% 1.80/1.07  --aig_mode                              false
% 1.80/1.07  
% 1.80/1.07  ------ Instantiation Options
% 1.80/1.07  
% 1.80/1.07  --instantiation_flag                    true
% 1.80/1.07  --inst_sos_flag                         false
% 1.80/1.07  --inst_sos_phase                        true
% 1.80/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.80/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.80/1.07  --inst_lit_sel_side                     none
% 1.80/1.07  --inst_solver_per_active                1400
% 1.80/1.07  --inst_solver_calls_frac                1.
% 1.80/1.07  --inst_passive_queue_type               priority_queues
% 1.80/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.80/1.07  --inst_passive_queues_freq              [25;2]
% 1.80/1.07  --inst_dismatching                      true
% 1.80/1.07  --inst_eager_unprocessed_to_passive     true
% 1.80/1.07  --inst_prop_sim_given                   true
% 1.80/1.07  --inst_prop_sim_new                     false
% 1.80/1.07  --inst_subs_new                         false
% 1.80/1.07  --inst_eq_res_simp                      false
% 1.80/1.07  --inst_subs_given                       false
% 1.80/1.07  --inst_orphan_elimination               true
% 1.80/1.07  --inst_learning_loop_flag               true
% 1.80/1.07  --inst_learning_start                   3000
% 1.80/1.07  --inst_learning_factor                  2
% 1.80/1.07  --inst_start_prop_sim_after_learn       3
% 1.80/1.07  --inst_sel_renew                        solver
% 1.80/1.07  --inst_lit_activity_flag                true
% 1.80/1.07  --inst_restr_to_given                   false
% 1.80/1.07  --inst_activity_threshold               500
% 1.80/1.07  --inst_out_proof                        true
% 1.80/1.07  
% 1.80/1.07  ------ Resolution Options
% 1.80/1.07  
% 1.80/1.07  --resolution_flag                       false
% 1.80/1.07  --res_lit_sel                           adaptive
% 1.80/1.07  --res_lit_sel_side                      none
% 1.80/1.07  --res_ordering                          kbo
% 1.80/1.07  --res_to_prop_solver                    active
% 1.80/1.07  --res_prop_simpl_new                    false
% 1.80/1.07  --res_prop_simpl_given                  true
% 1.80/1.07  --res_passive_queue_type                priority_queues
% 1.80/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.80/1.07  --res_passive_queues_freq               [15;5]
% 1.80/1.07  --res_forward_subs                      full
% 1.80/1.07  --res_backward_subs                     full
% 1.80/1.07  --res_forward_subs_resolution           true
% 1.80/1.07  --res_backward_subs_resolution          true
% 1.80/1.07  --res_orphan_elimination                true
% 1.80/1.07  --res_time_limit                        2.
% 1.80/1.07  --res_out_proof                         true
% 1.80/1.07  
% 1.80/1.07  ------ Superposition Options
% 1.80/1.07  
% 1.80/1.07  --superposition_flag                    true
% 1.80/1.07  --sup_passive_queue_type                priority_queues
% 1.80/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.80/1.07  --sup_passive_queues_freq               [8;1;4]
% 1.80/1.07  --demod_completeness_check              fast
% 1.80/1.07  --demod_use_ground                      true
% 1.80/1.07  --sup_to_prop_solver                    passive
% 1.80/1.07  --sup_prop_simpl_new                    true
% 1.80/1.07  --sup_prop_simpl_given                  true
% 1.80/1.07  --sup_fun_splitting                     false
% 1.80/1.07  --sup_smt_interval                      50000
% 1.80/1.07  
% 1.80/1.07  ------ Superposition Simplification Setup
% 1.80/1.07  
% 1.80/1.07  --sup_indices_passive                   []
% 1.80/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.80/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.80/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.07  --sup_full_bw                           [BwDemod]
% 1.80/1.07  --sup_immed_triv                        [TrivRules]
% 1.80/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.80/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.07  --sup_immed_bw_main                     []
% 1.80/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.80/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.80/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.80/1.07  
% 1.80/1.07  ------ Combination Options
% 1.80/1.07  
% 1.80/1.07  --comb_res_mult                         3
% 1.80/1.07  --comb_sup_mult                         2
% 1.80/1.07  --comb_inst_mult                        10
% 1.80/1.07  
% 1.80/1.07  ------ Debug Options
% 1.80/1.07  
% 1.80/1.07  --dbg_backtrace                         false
% 1.80/1.07  --dbg_dump_prop_clauses                 false
% 1.80/1.07  --dbg_dump_prop_clauses_file            -
% 1.80/1.07  --dbg_out_stat                          false
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  ------ Proving...
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  % SZS status Theorem for theBenchmark.p
% 1.80/1.07  
% 1.80/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 1.80/1.07  
% 1.80/1.07  fof(f68,plain,(
% 1.80/1.07    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f11,conjecture,(
% 1.80/1.07    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f12,negated_conjecture,(
% 1.80/1.07    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.80/1.07    inference(negated_conjecture,[],[f11])).
% 1.80/1.07  
% 1.80/1.07  fof(f26,plain,(
% 1.80/1.07    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.80/1.07    inference(ennf_transformation,[],[f12])).
% 1.80/1.07  
% 1.80/1.07  fof(f27,plain,(
% 1.80/1.07    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.80/1.07    inference(flattening,[],[f26])).
% 1.80/1.07  
% 1.80/1.07  fof(f40,plain,(
% 1.80/1.07    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK6)) & sK6 = X3 & m1_subset_1(sK6,u1_struct_0(X0)))) )),
% 1.80/1.07    introduced(choice_axiom,[])).
% 1.80/1.07  
% 1.80/1.07  fof(f39,plain,(
% 1.80/1.07    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK5)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.80/1.07    introduced(choice_axiom,[])).
% 1.80/1.07  
% 1.80/1.07  fof(f38,plain,(
% 1.80/1.07    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK4,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK4,X0,X1) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 1.80/1.07    introduced(choice_axiom,[])).
% 1.80/1.07  
% 1.80/1.07  fof(f37,plain,(
% 1.80/1.07    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,k6_domain_1(u1_struct_0(sK3),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK3))) & v3_borsuk_1(X2,X0,sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v5_pre_topc(X2,X0,sK3) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & m1_pre_topc(sK3,X0) & v4_tex_2(sK3,X0) & ~v2_struct_0(sK3))) )),
% 1.80/1.07    introduced(choice_axiom,[])).
% 1.80/1.07  
% 1.80/1.07  fof(f36,plain,(
% 1.80/1.07    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK2) & v4_tex_2(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.80/1.07    introduced(choice_axiom,[])).
% 1.80/1.07  
% 1.80/1.07  fof(f41,plain,(
% 1.80/1.07    ((((k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & v3_borsuk_1(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK2) & v4_tex_2(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.80/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f27,f40,f39,f38,f37,f36])).
% 1.80/1.07  
% 1.80/1.07  fof(f70,plain,(
% 1.80/1.07    sK5 = sK6),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f74,plain,(
% 1.80/1.07    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.80/1.07    inference(definition_unfolding,[],[f68,f70])).
% 1.80/1.07  
% 1.80/1.07  fof(f6,axiom,(
% 1.80/1.07    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f17,plain,(
% 1.80/1.07    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.80/1.07    inference(ennf_transformation,[],[f6])).
% 1.80/1.07  
% 1.80/1.07  fof(f18,plain,(
% 1.80/1.07    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.80/1.07    inference(flattening,[],[f17])).
% 1.80/1.07  
% 1.80/1.07  fof(f48,plain,(
% 1.80/1.07    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f18])).
% 1.80/1.07  
% 1.80/1.07  fof(f2,axiom,(
% 1.80/1.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f44,plain,(
% 1.80/1.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f2])).
% 1.80/1.07  
% 1.80/1.07  fof(f72,plain,(
% 1.80/1.07    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.80/1.07    inference(definition_unfolding,[],[f48,f44])).
% 1.80/1.07  
% 1.80/1.07  fof(f59,plain,(
% 1.80/1.07    l1_pre_topc(sK2)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f7,axiom,(
% 1.80/1.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f19,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.80/1.07    inference(ennf_transformation,[],[f7])).
% 1.80/1.07  
% 1.80/1.07  fof(f49,plain,(
% 1.80/1.07    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f19])).
% 1.80/1.07  
% 1.80/1.07  fof(f62,plain,(
% 1.80/1.07    m1_pre_topc(sK3,sK2)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f9,axiom,(
% 1.80/1.07    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f22,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.80/1.07    inference(ennf_transformation,[],[f9])).
% 1.80/1.07  
% 1.80/1.07  fof(f23,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/1.07    inference(flattening,[],[f22])).
% 1.80/1.07  
% 1.80/1.07  fof(f54,plain,(
% 1.80/1.07    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f23])).
% 1.80/1.07  
% 1.80/1.07  fof(f57,plain,(
% 1.80/1.07    v2_pre_topc(sK2)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f56,plain,(
% 1.80/1.07    ~v2_struct_0(sK2)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f8,axiom,(
% 1.80/1.07    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f20,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.80/1.07    inference(ennf_transformation,[],[f8])).
% 1.80/1.07  
% 1.80/1.07  fof(f21,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/1.07    inference(flattening,[],[f20])).
% 1.80/1.07  
% 1.80/1.07  fof(f32,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/1.07    inference(nnf_transformation,[],[f21])).
% 1.80/1.07  
% 1.80/1.07  fof(f33,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/1.07    inference(rectify,[],[f32])).
% 1.80/1.07  
% 1.80/1.07  fof(f34,plain,(
% 1.80/1.07    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.80/1.07    introduced(choice_axiom,[])).
% 1.80/1.07  
% 1.80/1.07  fof(f35,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK1(X0,X1),X0) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 1.80/1.07  
% 1.80/1.07  fof(f50,plain,(
% 1.80/1.07    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f35])).
% 1.80/1.07  
% 1.80/1.07  fof(f75,plain,(
% 1.80/1.07    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/1.07    inference(equality_resolution,[],[f50])).
% 1.80/1.07  
% 1.80/1.07  fof(f61,plain,(
% 1.80/1.07    v4_tex_2(sK3,sK2)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f5,axiom,(
% 1.80/1.07    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f15,plain,(
% 1.80/1.07    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.80/1.07    inference(ennf_transformation,[],[f5])).
% 1.80/1.07  
% 1.80/1.07  fof(f16,plain,(
% 1.80/1.07    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.80/1.07    inference(flattening,[],[f15])).
% 1.80/1.07  
% 1.80/1.07  fof(f47,plain,(
% 1.80/1.07    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f16])).
% 1.80/1.07  
% 1.80/1.07  fof(f4,axiom,(
% 1.80/1.07    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f14,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.80/1.07    inference(ennf_transformation,[],[f4])).
% 1.80/1.07  
% 1.80/1.07  fof(f46,plain,(
% 1.80/1.07    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f14])).
% 1.80/1.07  
% 1.80/1.07  fof(f10,axiom,(
% 1.80/1.07    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f24,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.80/1.07    inference(ennf_transformation,[],[f10])).
% 1.80/1.07  
% 1.80/1.07  fof(f25,plain,(
% 1.80/1.07    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.80/1.07    inference(flattening,[],[f24])).
% 1.80/1.07  
% 1.80/1.07  fof(f55,plain,(
% 1.80/1.07    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f25])).
% 1.80/1.07  
% 1.80/1.07  fof(f76,plain,(
% 1.80/1.07    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.80/1.07    inference(equality_resolution,[],[f55])).
% 1.80/1.07  
% 1.80/1.07  fof(f67,plain,(
% 1.80/1.07    v3_borsuk_1(sK4,sK2,sK3)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f58,plain,(
% 1.80/1.07    v3_tdlat_3(sK2)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f60,plain,(
% 1.80/1.07    ~v2_struct_0(sK3)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f63,plain,(
% 1.80/1.07    v1_funct_1(sK4)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f64,plain,(
% 1.80/1.07    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f65,plain,(
% 1.80/1.07    v5_pre_topc(sK4,sK2,sK3)),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f66,plain,(
% 1.80/1.07    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f69,plain,(
% 1.80/1.07    m1_subset_1(sK6,u1_struct_0(sK2))),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f1,axiom,(
% 1.80/1.07    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f28,plain,(
% 1.80/1.07    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.80/1.07    inference(nnf_transformation,[],[f1])).
% 1.80/1.07  
% 1.80/1.07  fof(f29,plain,(
% 1.80/1.07    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.80/1.07    inference(rectify,[],[f28])).
% 1.80/1.07  
% 1.80/1.07  fof(f30,plain,(
% 1.80/1.07    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.80/1.07    introduced(choice_axiom,[])).
% 1.80/1.07  
% 1.80/1.07  fof(f31,plain,(
% 1.80/1.07    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.80/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.80/1.07  
% 1.80/1.07  fof(f43,plain,(
% 1.80/1.07    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f31])).
% 1.80/1.07  
% 1.80/1.07  fof(f3,axiom,(
% 1.80/1.07    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.80/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.80/1.07  
% 1.80/1.07  fof(f13,plain,(
% 1.80/1.07    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.80/1.07    inference(ennf_transformation,[],[f3])).
% 1.80/1.07  
% 1.80/1.07  fof(f45,plain,(
% 1.80/1.07    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.80/1.07    inference(cnf_transformation,[],[f13])).
% 1.80/1.07  
% 1.80/1.07  fof(f71,plain,(
% 1.80/1.07    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK5)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 1.80/1.07    inference(cnf_transformation,[],[f41])).
% 1.80/1.07  
% 1.80/1.07  fof(f73,plain,(
% 1.80/1.07    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6))),
% 1.80/1.07    inference(definition_unfolding,[],[f71,f70])).
% 1.80/1.07  
% 1.80/1.07  cnf(c_15,negated_conjecture,
% 1.80/1.07      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.80/1.07      inference(cnf_transformation,[],[f74]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_576,negated_conjecture,
% 1.80/1.07      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 1.80/1.07      inference(subtyping,[status(esa)],[c_15]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_784,plain,
% 1.80/1.07      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_5,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,X1)
% 1.80/1.07      | v1_xboole_0(X1)
% 1.80/1.07      | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
% 1.80/1.07      inference(cnf_transformation,[],[f72]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_579,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0_55,X1_55)
% 1.80/1.07      | v1_xboole_0(X1_55)
% 1.80/1.07      | k2_tarski(X0_55,X0_55) = k6_domain_1(X1_55,X0_55) ),
% 1.80/1.07      inference(subtyping,[status(esa)],[c_5]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_782,plain,
% 1.80/1.07      ( k2_tarski(X0_55,X0_55) = k6_domain_1(X1_55,X0_55)
% 1.80/1.07      | m1_subset_1(X0_55,X1_55) != iProver_top
% 1.80/1.07      | v1_xboole_0(X1_55) = iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1115,plain,
% 1.80/1.07      ( k6_domain_1(u1_struct_0(sK3),sK6) = k2_tarski(sK6,sK6)
% 1.80/1.07      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.80/1.07      inference(superposition,[status(thm)],[c_784,c_782]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_24,negated_conjecture,
% 1.80/1.07      ( l1_pre_topc(sK2) ),
% 1.80/1.07      inference(cnf_transformation,[],[f59]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_31,plain,
% 1.80/1.07      ( l1_pre_topc(sK2) = iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_6,plain,
% 1.80/1.07      ( ~ m1_pre_topc(X0,X1)
% 1.80/1.07      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | ~ l1_pre_topc(X1) ),
% 1.80/1.07      inference(cnf_transformation,[],[f49]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_21,negated_conjecture,
% 1.80/1.07      ( m1_pre_topc(sK3,sK2) ),
% 1.80/1.07      inference(cnf_transformation,[],[f62]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_442,plain,
% 1.80/1.07      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | ~ l1_pre_topc(X1)
% 1.80/1.07      | sK3 != X0
% 1.80/1.07      | sK2 != X1 ),
% 1.80/1.07      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_443,plain,
% 1.80/1.07      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ l1_pre_topc(sK2) ),
% 1.80/1.07      inference(unflattening,[status(thm)],[c_442]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_444,plain,
% 1.80/1.07      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.80/1.07      | l1_pre_topc(sK2) != iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_11,plain,
% 1.80/1.07      ( ~ v3_tex_2(X0,X1)
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | ~ v2_pre_topc(X1)
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | ~ l1_pre_topc(X1)
% 1.80/1.07      | ~ v1_xboole_0(X0) ),
% 1.80/1.07      inference(cnf_transformation,[],[f54]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_26,negated_conjecture,
% 1.80/1.07      ( v2_pre_topc(sK2) ),
% 1.80/1.07      inference(cnf_transformation,[],[f57]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_342,plain,
% 1.80/1.07      ( ~ v3_tex_2(X0,X1)
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | ~ l1_pre_topc(X1)
% 1.80/1.07      | ~ v1_xboole_0(X0)
% 1.80/1.07      | sK2 != X1 ),
% 1.80/1.07      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_343,plain,
% 1.80/1.07      ( ~ v3_tex_2(X0,sK2)
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | v2_struct_0(sK2)
% 1.80/1.07      | ~ l1_pre_topc(sK2)
% 1.80/1.07      | ~ v1_xboole_0(X0) ),
% 1.80/1.07      inference(unflattening,[status(thm)],[c_342]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_27,negated_conjecture,
% 1.80/1.07      ( ~ v2_struct_0(sK2) ),
% 1.80/1.07      inference(cnf_transformation,[],[f56]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_347,plain,
% 1.80/1.07      ( ~ v3_tex_2(X0,sK2)
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ v1_xboole_0(X0) ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_343,c_27,c_24]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_10,plain,
% 1.80/1.07      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.80/1.07      | ~ v4_tex_2(X0,X1)
% 1.80/1.07      | ~ m1_pre_topc(X0,X1)
% 1.80/1.07      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | ~ l1_pre_topc(X1) ),
% 1.80/1.07      inference(cnf_transformation,[],[f75]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_150,plain,
% 1.80/1.07      ( ~ m1_pre_topc(X0,X1)
% 1.80/1.07      | ~ v4_tex_2(X0,X1)
% 1.80/1.07      | v3_tex_2(u1_struct_0(X0),X1)
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | ~ l1_pre_topc(X1) ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_10,c_6]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_151,plain,
% 1.80/1.07      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.80/1.07      | ~ v4_tex_2(X0,X1)
% 1.80/1.07      | ~ m1_pre_topc(X0,X1)
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | ~ l1_pre_topc(X1) ),
% 1.80/1.07      inference(renaming,[status(thm)],[c_150]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_427,plain,
% 1.80/1.07      ( v3_tex_2(u1_struct_0(X0),X1)
% 1.80/1.07      | ~ v4_tex_2(X0,X1)
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | ~ l1_pre_topc(X1)
% 1.80/1.07      | sK3 != X0
% 1.80/1.07      | sK2 != X1 ),
% 1.80/1.07      inference(resolution_lifted,[status(thm)],[c_151,c_21]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_428,plain,
% 1.80/1.07      ( v3_tex_2(u1_struct_0(sK3),sK2)
% 1.80/1.07      | ~ v4_tex_2(sK3,sK2)
% 1.80/1.07      | v2_struct_0(sK2)
% 1.80/1.07      | ~ l1_pre_topc(sK2) ),
% 1.80/1.07      inference(unflattening,[status(thm)],[c_427]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_22,negated_conjecture,
% 1.80/1.07      ( v4_tex_2(sK3,sK2) ),
% 1.80/1.07      inference(cnf_transformation,[],[f61]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_430,plain,
% 1.80/1.07      ( v3_tex_2(u1_struct_0(sK3),sK2) ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_428,c_27,c_24,c_22]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_484,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ v1_xboole_0(X0)
% 1.80/1.07      | u1_struct_0(sK3) != X0
% 1.80/1.07      | sK2 != sK2 ),
% 1.80/1.07      inference(resolution_lifted,[status(thm)],[c_347,c_430]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_485,plain,
% 1.80/1.07      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.80/1.07      inference(unflattening,[status(thm)],[c_484]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_486,plain,
% 1.80/1.07      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.80/1.07      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1280,plain,
% 1.80/1.07      ( k6_domain_1(u1_struct_0(sK3),sK6) = k2_tarski(sK6,sK6) ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_1115,c_31,c_444,c_486]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_4,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,X1)
% 1.80/1.07      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.80/1.07      | v1_xboole_0(X1) ),
% 1.80/1.07      inference(cnf_transformation,[],[f47]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_580,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0_55,X1_55)
% 1.80/1.07      | m1_subset_1(k6_domain_1(X1_55,X0_55),k1_zfmisc_1(X1_55))
% 1.80/1.07      | v1_xboole_0(X1_55) ),
% 1.80/1.07      inference(subtyping,[status(esa)],[c_4]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_781,plain,
% 1.80/1.07      ( m1_subset_1(X0_55,X1_55) != iProver_top
% 1.80/1.07      | m1_subset_1(k6_domain_1(X1_55,X0_55),k1_zfmisc_1(X1_55)) = iProver_top
% 1.80/1.07      | v1_xboole_0(X1_55) = iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1284,plain,
% 1.80/1.07      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 1.80/1.07      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
% 1.80/1.07      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.80/1.07      inference(superposition,[status(thm)],[c_1280,c_781]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_40,plain,
% 1.80/1.07      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1366,plain,
% 1.80/1.07      ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_1284,c_31,c_40,c_444,c_486]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_3,plain,
% 1.80/1.07      ( ~ m1_pre_topc(X0,X1)
% 1.80/1.07      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.80/1.07      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | ~ l1_pre_topc(X1) ),
% 1.80/1.07      inference(cnf_transformation,[],[f46]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_453,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.80/1.07      | ~ l1_pre_topc(X2)
% 1.80/1.07      | sK3 != X1
% 1.80/1.07      | sK2 != X2 ),
% 1.80/1.07      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_454,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.80/1.07      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ l1_pre_topc(sK2) ),
% 1.80/1.07      inference(unflattening,[status(thm)],[c_453]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_458,plain,
% 1.80/1.07      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_454,c_24]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_459,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.80/1.07      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.80/1.07      inference(renaming,[status(thm)],[c_458]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_12,plain,
% 1.80/1.07      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.80/1.07      | ~ v5_pre_topc(X0,X1,X2)
% 1.80/1.07      | ~ v3_borsuk_1(X0,X1,X2)
% 1.80/1.07      | ~ v4_tex_2(X2,X1)
% 1.80/1.07      | ~ m1_pre_topc(X2,X1)
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.80/1.07      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.80/1.07      | ~ v3_tdlat_3(X1)
% 1.80/1.07      | ~ v1_funct_1(X0)
% 1.80/1.07      | ~ v2_pre_topc(X1)
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | v2_struct_0(X2)
% 1.80/1.07      | ~ l1_pre_topc(X1)
% 1.80/1.07      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 1.80/1.07      inference(cnf_transformation,[],[f76]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_16,negated_conjecture,
% 1.80/1.07      ( v3_borsuk_1(sK4,sK2,sK3) ),
% 1.80/1.07      inference(cnf_transformation,[],[f67]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_317,plain,
% 1.80/1.07      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.80/1.07      | ~ v5_pre_topc(X0,X1,X2)
% 1.80/1.07      | ~ v4_tex_2(X2,X1)
% 1.80/1.07      | ~ m1_pre_topc(X2,X1)
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.80/1.07      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.80/1.07      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.80/1.07      | ~ v3_tdlat_3(X1)
% 1.80/1.07      | ~ v1_funct_1(X0)
% 1.80/1.07      | ~ v2_pre_topc(X1)
% 1.80/1.07      | v2_struct_0(X1)
% 1.80/1.07      | v2_struct_0(X2)
% 1.80/1.07      | ~ l1_pre_topc(X1)
% 1.80/1.07      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 1.80/1.07      | sK4 != X0
% 1.80/1.07      | sK3 != X2
% 1.80/1.07      | sK2 != X1 ),
% 1.80/1.07      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_318,plain,
% 1.80/1.07      ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
% 1.80/1.07      | ~ v5_pre_topc(sK4,sK2,sK3)
% 1.80/1.07      | ~ v4_tex_2(sK3,sK2)
% 1.80/1.07      | ~ m1_pre_topc(sK3,sK2)
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 1.80/1.07      | ~ v3_tdlat_3(sK2)
% 1.80/1.07      | ~ v1_funct_1(sK4)
% 1.80/1.07      | ~ v2_pre_topc(sK2)
% 1.80/1.07      | v2_struct_0(sK3)
% 1.80/1.07      | v2_struct_0(sK2)
% 1.80/1.07      | ~ l1_pre_topc(sK2)
% 1.80/1.07      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.80/1.07      inference(unflattening,[status(thm)],[c_317]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_25,negated_conjecture,
% 1.80/1.07      ( v3_tdlat_3(sK2) ),
% 1.80/1.07      inference(cnf_transformation,[],[f58]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_23,negated_conjecture,
% 1.80/1.07      ( ~ v2_struct_0(sK3) ),
% 1.80/1.07      inference(cnf_transformation,[],[f60]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_20,negated_conjecture,
% 1.80/1.07      ( v1_funct_1(sK4) ),
% 1.80/1.07      inference(cnf_transformation,[],[f63]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_19,negated_conjecture,
% 1.80/1.07      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 1.80/1.07      inference(cnf_transformation,[],[f64]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_18,negated_conjecture,
% 1.80/1.07      ( v5_pre_topc(sK4,sK2,sK3) ),
% 1.80/1.07      inference(cnf_transformation,[],[f65]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_17,negated_conjecture,
% 1.80/1.07      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 1.80/1.07      inference(cnf_transformation,[],[f66]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_322,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.80/1.07      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_318,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,
% 1.80/1.07                 c_17]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_323,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.80/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.80/1.07      inference(renaming,[status(thm)],[c_322]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_479,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.80/1.07      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k2_pre_topc(sK2,X0) ),
% 1.80/1.07      inference(backward_subsumption_resolution,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_459,c_323]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_571,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.80/1.07      | k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55) ),
% 1.80/1.07      inference(subtyping,[status(esa)],[c_479]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_789,plain,
% 1.80/1.07      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0_55) = k2_pre_topc(sK2,X0_55)
% 1.80/1.07      | m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1371,plain,
% 1.80/1.07      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6)) = k2_pre_topc(sK2,k2_tarski(sK6,sK6)) ),
% 1.80/1.07      inference(superposition,[status(thm)],[c_1366,c_789]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_14,negated_conjecture,
% 1.80/1.07      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 1.80/1.07      inference(cnf_transformation,[],[f69]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_577,negated_conjecture,
% 1.80/1.07      ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
% 1.80/1.07      inference(subtyping,[status(esa)],[c_14]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_783,plain,
% 1.80/1.07      ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
% 1.80/1.07      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1114,plain,
% 1.80/1.07      ( k6_domain_1(u1_struct_0(sK2),sK6) = k2_tarski(sK6,sK6)
% 1.80/1.07      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.80/1.07      inference(superposition,[status(thm)],[c_783,c_782]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1143,plain,
% 1.80/1.07      ( v1_xboole_0(u1_struct_0(sK2))
% 1.80/1.07      | k6_domain_1(u1_struct_0(sK2),sK6) = k2_tarski(sK6,sK6) ),
% 1.80/1.07      inference(predicate_to_equality_rev,[status(thm)],[c_1114]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_0,plain,
% 1.80/1.07      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.80/1.07      inference(cnf_transformation,[],[f43]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_2,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.80/1.07      | ~ r2_hidden(X2,X0)
% 1.80/1.07      | ~ v1_xboole_0(X1) ),
% 1.80/1.07      inference(cnf_transformation,[],[f45]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_300,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.80/1.07      | ~ v1_xboole_0(X1)
% 1.80/1.07      | v1_xboole_0(X2)
% 1.80/1.07      | X0 != X2
% 1.80/1.07      | sK0(X2) != X3 ),
% 1.80/1.07      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_301,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.80/1.07      | ~ v1_xboole_0(X1)
% 1.80/1.07      | v1_xboole_0(X0) ),
% 1.80/1.07      inference(unflattening,[status(thm)],[c_300]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_574,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 1.80/1.07      | ~ v1_xboole_0(X1_55)
% 1.80/1.07      | v1_xboole_0(X0_55) ),
% 1.80/1.07      inference(subtyping,[status(esa)],[c_301]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1055,plain,
% 1.80/1.07      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | v1_xboole_0(X0_55)
% 1.80/1.07      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.80/1.07      inference(instantiation,[status(thm)],[c_574]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1210,plain,
% 1.80/1.07      ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.80/1.07      | v1_xboole_0(u1_struct_0(sK3))
% 1.80/1.07      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.80/1.07      inference(instantiation,[status(thm)],[c_1055]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1232,plain,
% 1.80/1.07      ( k6_domain_1(u1_struct_0(sK2),sK6) = k2_tarski(sK6,sK6) ),
% 1.80/1.07      inference(global_propositional_subsumption,
% 1.80/1.07                [status(thm)],
% 1.80/1.07                [c_1114,c_24,c_443,c_485,c_1143,c_1210]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_13,negated_conjecture,
% 1.80/1.07      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
% 1.80/1.07      inference(cnf_transformation,[],[f73]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_578,negated_conjecture,
% 1.80/1.07      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK6)) ),
% 1.80/1.07      inference(subtyping,[status(esa)],[c_13]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1235,plain,
% 1.80/1.07      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k6_domain_1(u1_struct_0(sK3),sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) ),
% 1.80/1.07      inference(demodulation,[status(thm)],[c_1232,c_578]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(c_1283,plain,
% 1.80/1.07      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tarski(sK6,sK6)) != k2_pre_topc(sK2,k2_tarski(sK6,sK6)) ),
% 1.80/1.07      inference(demodulation,[status(thm)],[c_1280,c_1235]) ).
% 1.80/1.07  
% 1.80/1.07  cnf(contradiction,plain,
% 1.80/1.07      ( $false ),
% 1.80/1.07      inference(minisat,[status(thm)],[c_1371,c_1283]) ).
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 1.80/1.07  
% 1.80/1.07  ------                               Statistics
% 1.80/1.07  
% 1.80/1.07  ------ General
% 1.80/1.07  
% 1.80/1.07  abstr_ref_over_cycles:                  0
% 1.80/1.07  abstr_ref_under_cycles:                 0
% 1.80/1.07  gc_basic_clause_elim:                   0
% 1.80/1.07  forced_gc_time:                         0
% 1.80/1.07  parsing_time:                           0.013
% 1.80/1.07  unif_index_cands_time:                  0.
% 1.80/1.07  unif_index_add_time:                    0.
% 1.80/1.07  orderings_time:                         0.
% 1.80/1.07  out_proof_time:                         0.014
% 1.80/1.07  total_time:                             0.113
% 1.80/1.07  num_of_symbols:                         64
% 1.80/1.07  num_of_terms:                           1513
% 1.80/1.07  
% 1.80/1.07  ------ Preprocessing
% 1.80/1.07  
% 1.80/1.07  num_of_splits:                          0
% 1.80/1.07  num_of_split_atoms:                     0
% 1.80/1.07  num_of_reused_defs:                     0
% 1.80/1.07  num_eq_ax_congr_red:                    14
% 1.80/1.07  num_of_sem_filtered_clauses:            1
% 1.80/1.07  num_of_subtypes:                        3
% 1.80/1.07  monotx_restored_types:                  0
% 1.80/1.07  sat_num_of_epr_types:                   0
% 1.80/1.07  sat_num_of_non_cyclic_types:            0
% 1.80/1.07  sat_guarded_non_collapsed_types:        0
% 1.80/1.07  num_pure_diseq_elim:                    0
% 1.80/1.07  simp_replaced_by:                       0
% 1.80/1.07  res_preprocessed:                       84
% 1.80/1.07  prep_upred:                             0
% 1.80/1.07  prep_unflattend:                        24
% 1.80/1.07  smt_new_axioms:                         0
% 1.80/1.07  pred_elim_cands:                        2
% 1.80/1.07  pred_elim:                              12
% 1.80/1.07  pred_elim_cl:                           17
% 1.80/1.07  pred_elim_cycles:                       15
% 1.80/1.07  merged_defs:                            0
% 1.80/1.07  merged_defs_ncl:                        0
% 1.80/1.07  bin_hyper_res:                          0
% 1.80/1.07  prep_cycles:                            4
% 1.80/1.07  pred_elim_time:                         0.004
% 1.80/1.07  splitting_time:                         0.
% 1.80/1.07  sem_filter_time:                        0.
% 1.80/1.07  monotx_time:                            0.
% 1.80/1.07  subtype_inf_time:                       0.
% 1.80/1.07  
% 1.80/1.07  ------ Problem properties
% 1.80/1.07  
% 1.80/1.07  clauses:                                11
% 1.80/1.07  conjectures:                            4
% 1.80/1.07  epr:                                    0
% 1.80/1.07  horn:                                   9
% 1.80/1.07  ground:                                 6
% 1.80/1.07  unary:                                  6
% 1.80/1.07  binary:                                 2
% 1.80/1.07  lits:                                   19
% 1.80/1.07  lits_eq:                                3
% 1.80/1.07  fd_pure:                                0
% 1.80/1.07  fd_pseudo:                              0
% 1.80/1.07  fd_cond:                                0
% 1.80/1.07  fd_pseudo_cond:                         0
% 1.80/1.07  ac_symbols:                             0
% 1.80/1.07  
% 1.80/1.07  ------ Propositional Solver
% 1.80/1.07  
% 1.80/1.07  prop_solver_calls:                      26
% 1.80/1.07  prop_fast_solver_calls:                 491
% 1.80/1.07  smt_solver_calls:                       0
% 1.80/1.07  smt_fast_solver_calls:                  0
% 1.80/1.07  prop_num_of_clauses:                    442
% 1.80/1.07  prop_preprocess_simplified:             2123
% 1.80/1.07  prop_fo_subsumed:                       28
% 1.80/1.07  prop_solver_time:                       0.
% 1.80/1.07  smt_solver_time:                        0.
% 1.80/1.07  smt_fast_solver_time:                   0.
% 1.80/1.07  prop_fast_solver_time:                  0.
% 1.80/1.07  prop_unsat_core_time:                   0.
% 1.80/1.07  
% 1.80/1.07  ------ QBF
% 1.80/1.07  
% 1.80/1.07  qbf_q_res:                              0
% 1.80/1.07  qbf_num_tautologies:                    0
% 1.80/1.07  qbf_prep_cycles:                        0
% 1.80/1.07  
% 1.80/1.07  ------ BMC1
% 1.80/1.07  
% 1.80/1.07  bmc1_current_bound:                     -1
% 1.80/1.07  bmc1_last_solved_bound:                 -1
% 1.80/1.07  bmc1_unsat_core_size:                   -1
% 1.80/1.07  bmc1_unsat_core_parents_size:           -1
% 1.80/1.07  bmc1_merge_next_fun:                    0
% 1.80/1.07  bmc1_unsat_core_clauses_time:           0.
% 1.80/1.07  
% 1.80/1.07  ------ Instantiation
% 1.80/1.07  
% 1.80/1.07  inst_num_of_clauses:                    116
% 1.80/1.07  inst_num_in_passive:                    14
% 1.80/1.07  inst_num_in_active:                     84
% 1.80/1.07  inst_num_in_unprocessed:                18
% 1.80/1.07  inst_num_of_loops:                      90
% 1.80/1.07  inst_num_of_learning_restarts:          0
% 1.80/1.07  inst_num_moves_active_passive:          4
% 1.80/1.07  inst_lit_activity:                      0
% 1.80/1.07  inst_lit_activity_moves:                0
% 1.80/1.07  inst_num_tautologies:                   0
% 1.80/1.07  inst_num_prop_implied:                  0
% 1.80/1.07  inst_num_existing_simplified:           0
% 1.80/1.07  inst_num_eq_res_simplified:             0
% 1.80/1.07  inst_num_child_elim:                    0
% 1.80/1.07  inst_num_of_dismatching_blockings:      4
% 1.80/1.07  inst_num_of_non_proper_insts:           86
% 1.80/1.07  inst_num_of_duplicates:                 0
% 1.80/1.07  inst_inst_num_from_inst_to_res:         0
% 1.80/1.07  inst_dismatching_checking_time:         0.
% 1.80/1.07  
% 1.80/1.07  ------ Resolution
% 1.80/1.07  
% 1.80/1.07  res_num_of_clauses:                     0
% 1.80/1.07  res_num_in_passive:                     0
% 1.80/1.07  res_num_in_active:                      0
% 1.80/1.07  res_num_of_loops:                       88
% 1.80/1.07  res_forward_subset_subsumed:            16
% 1.80/1.07  res_backward_subset_subsumed:           2
% 1.80/1.07  res_forward_subsumed:                   0
% 1.80/1.07  res_backward_subsumed:                  0
% 1.80/1.07  res_forward_subsumption_resolution:     0
% 1.80/1.07  res_backward_subsumption_resolution:    1
% 1.80/1.07  res_clause_to_clause_subsumption:       29
% 1.80/1.07  res_orphan_elimination:                 0
% 1.80/1.07  res_tautology_del:                      12
% 1.80/1.07  res_num_eq_res_simplified:              0
% 1.80/1.07  res_num_sel_changes:                    0
% 1.80/1.07  res_moves_from_active_to_pass:          0
% 1.80/1.07  
% 1.80/1.07  ------ Superposition
% 1.80/1.07  
% 1.80/1.07  sup_time_total:                         0.
% 1.80/1.07  sup_time_generating:                    0.
% 1.80/1.07  sup_time_sim_full:                      0.
% 1.80/1.07  sup_time_sim_immed:                     0.
% 1.80/1.07  
% 1.80/1.07  sup_num_of_clauses:                     22
% 1.80/1.07  sup_num_in_active:                      16
% 1.80/1.07  sup_num_in_passive:                     6
% 1.80/1.07  sup_num_of_loops:                       17
% 1.80/1.07  sup_fw_superposition:                   5
% 1.80/1.07  sup_bw_superposition:                   8
% 1.80/1.07  sup_immediate_simplified:               0
% 1.80/1.07  sup_given_eliminated:                   0
% 1.80/1.07  comparisons_done:                       0
% 1.80/1.07  comparisons_avoided:                    0
% 1.80/1.07  
% 1.80/1.07  ------ Simplifications
% 1.80/1.07  
% 1.80/1.07  
% 1.80/1.07  sim_fw_subset_subsumed:                 0
% 1.80/1.07  sim_bw_subset_subsumed:                 0
% 1.80/1.07  sim_fw_subsumed:                        0
% 1.80/1.07  sim_bw_subsumed:                        0
% 1.80/1.07  sim_fw_subsumption_res:                 0
% 1.80/1.07  sim_bw_subsumption_res:                 0
% 1.80/1.07  sim_tautology_del:                      0
% 1.80/1.07  sim_eq_tautology_del:                   0
% 1.80/1.07  sim_eq_res_simp:                        0
% 1.80/1.07  sim_fw_demodulated:                     0
% 1.80/1.07  sim_bw_demodulated:                     2
% 1.80/1.07  sim_light_normalised:                   0
% 1.80/1.07  sim_joinable_taut:                      0
% 1.80/1.07  sim_joinable_simp:                      0
% 1.80/1.07  sim_ac_normalised:                      0
% 1.80/1.07  sim_smt_subsumption:                    0
% 1.80/1.07  
%------------------------------------------------------------------------------
