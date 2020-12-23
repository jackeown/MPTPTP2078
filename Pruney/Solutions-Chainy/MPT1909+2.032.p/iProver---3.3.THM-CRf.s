%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:00 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 902 expanded)
%              Number of clauses        :   94 ( 184 expanded)
%              Number of leaves         :   18 ( 359 expanded)
%              Depth                    :   18
%              Number of atoms          :  750 (10318 expanded)
%              Number of equality atoms :  153 (1868 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))
        & sK4 = X3
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ? [X4] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
            & sK3 = X4
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        & v3_borsuk_1(sK2,X0,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(sK2,X0,X1)
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                & m1_subset_1(X3,u1_struct_0(sK1)) )
            & v3_borsuk_1(X2,X0,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v5_pre_topc(X2,X0,sK1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & m1_pre_topc(sK1,X0)
        & v4_tex_2(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v5_pre_topc(X2,sK0,X1)
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,sK0)
          & v4_tex_2(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & v3_borsuk_1(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v5_pre_topc(sK2,sK0,sK1)
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & m1_pre_topc(sK1,sK0)
    & v4_tex_2(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f41,f40,f39,f38,f37])).

fof(f74,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f72,f74])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f71,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(definition_unfolding,[],[f75,f74])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_836,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1261,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_12,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_164,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_165,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_170,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_165,c_14,c_13])).

cnf(c_171,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_830,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55)
    | k6_domain_1(u1_struct_0(X0_55),X0_56) = u1_struct_0(k1_tex_2(X0_55,X0_56)) ),
    inference(subtyping,[status(esa)],[c_171])).

cnf(c_1267,plain,
    ( k6_domain_1(u1_struct_0(X0_55),X0_56) = u1_struct_0(k1_tex_2(X0_55,X0_56))
    | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_2575,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1267])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_843,plain,
    ( ~ m1_subset_1(X0_56,X1_56)
    | v1_xboole_0(X1_56)
    | k6_domain_1(X1_56,X0_56) = k2_tarski(X0_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1255,plain,
    ( k6_domain_1(X0_56,X1_56) = k2_tarski(X1_56,X1_56)
    | m1_subset_1(X1_56,X0_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_1585,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1255])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_401,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_829,plain,
    ( v2_struct_0(X0_55)
    | ~ v1_xboole_0(u1_struct_0(X0_55))
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_401])).

cnf(c_1268,plain,
    ( v2_struct_0(X0_55) = iProver_top
    | v1_xboole_0(u1_struct_0(X0_55)) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_2133,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_1268])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_37,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_845,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ l1_pre_topc(X1_55)
    | l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1525,plain,
    ( ~ m1_pre_topc(sK1,X0_55)
    | ~ l1_pre_topc(X0_55)
    | l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_1526,plain,
    ( m1_pre_topc(sK1,X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_1528,plain,
    ( m1_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1526])).

cnf(c_2420,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2133,c_34,c_35,c_37,c_1528])).

cnf(c_2579,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK4)) = k2_tarski(sK4,sK4)
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2575,c_2420])).

cnf(c_2808,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK4)) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2579,c_34,c_35,c_37,c_1528])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_550,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_551,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_513,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X0)
    | m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_514,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(X0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_555,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_27,c_514])).

cnf(c_556,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_602,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | u1_struct_0(X1) != X3
    | u1_struct_0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_222,c_556])).

cnf(c_603,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(unflattening,[status(thm)],[c_602])).

cnf(c_825,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X1_55,sK0)
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55))) ),
    inference(subtyping,[status(esa)],[c_603])).

cnf(c_1272,plain,
    ( m1_pre_topc(X0_55,X1_55) != iProver_top
    | m1_pre_topc(X1_55,sK0) != iProver_top
    | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_2815,plain,
    ( m1_pre_topc(X0_55,sK0) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK4),X0_55) != iProver_top
    | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2808,c_1272])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_19,negated_conjecture,
    ( v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_488,plain,
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
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
    | sK2 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_489,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v4_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v3_tdlat_3(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21,negated_conjecture,
    ( v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k2_pre_topc(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k2_pre_topc(sK0,X0) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_828,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0)))
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56) ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1269,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_909,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_844,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X1_55)))
    | ~ l1_pre_topc(X1_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1490,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_1491,plain,
    ( m1_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_1882,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1269,c_34,c_37,c_909,c_1491])).

cnf(c_1883,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56)
    | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1882])).

cnf(c_3246,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4))
    | m1_pre_topc(k1_tex_2(sK1,sK4),sK1) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2815,c_1883])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_837,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1260,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_1584,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1255])).

cnf(c_73,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_77,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1477,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1971,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1584,c_30,c_27,c_17,c_73,c_77,c_1477])).

cnf(c_16,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_838,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1974,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_1971,c_838])).

cnf(c_2423,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
    inference(demodulation,[status(thm)],[c_2420,c_1974])).

cnf(c_841,plain,
    ( m1_pre_topc(k1_tex_2(X0_55,X0_56),X0_55)
    | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
    | v2_struct_0(X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1474,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK4),sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1475,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK4),sK1) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3246,c_2423,c_1528,c_1475,c_43,c_37,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.43/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.00  
% 2.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/1.00  
% 2.43/1.00  ------  iProver source info
% 2.43/1.00  
% 2.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/1.00  git: non_committed_changes: false
% 2.43/1.00  git: last_make_outside_of_git: false
% 2.43/1.00  
% 2.43/1.00  ------ 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options
% 2.43/1.00  
% 2.43/1.00  --out_options                           all
% 2.43/1.00  --tptp_safe_out                         true
% 2.43/1.00  --problem_path                          ""
% 2.43/1.00  --include_path                          ""
% 2.43/1.00  --clausifier                            res/vclausify_rel
% 2.43/1.00  --clausifier_options                    --mode clausify
% 2.43/1.00  --stdin                                 false
% 2.43/1.00  --stats_out                             all
% 2.43/1.00  
% 2.43/1.00  ------ General Options
% 2.43/1.00  
% 2.43/1.00  --fof                                   false
% 2.43/1.00  --time_out_real                         305.
% 2.43/1.00  --time_out_virtual                      -1.
% 2.43/1.00  --symbol_type_check                     false
% 2.43/1.00  --clausify_out                          false
% 2.43/1.00  --sig_cnt_out                           false
% 2.43/1.00  --trig_cnt_out                          false
% 2.43/1.00  --trig_cnt_out_tolerance                1.
% 2.43/1.00  --trig_cnt_out_sk_spl                   false
% 2.43/1.00  --abstr_cl_out                          false
% 2.43/1.00  
% 2.43/1.00  ------ Global Options
% 2.43/1.00  
% 2.43/1.00  --schedule                              default
% 2.43/1.00  --add_important_lit                     false
% 2.43/1.00  --prop_solver_per_cl                    1000
% 2.43/1.00  --min_unsat_core                        false
% 2.43/1.00  --soft_assumptions                      false
% 2.43/1.00  --soft_lemma_size                       3
% 2.43/1.00  --prop_impl_unit_size                   0
% 2.43/1.00  --prop_impl_unit                        []
% 2.43/1.00  --share_sel_clauses                     true
% 2.43/1.00  --reset_solvers                         false
% 2.43/1.00  --bc_imp_inh                            [conj_cone]
% 2.43/1.00  --conj_cone_tolerance                   3.
% 2.43/1.00  --extra_neg_conj                        none
% 2.43/1.00  --large_theory_mode                     true
% 2.43/1.00  --prolific_symb_bound                   200
% 2.43/1.00  --lt_threshold                          2000
% 2.43/1.00  --clause_weak_htbl                      true
% 2.43/1.00  --gc_record_bc_elim                     false
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing Options
% 2.43/1.00  
% 2.43/1.00  --preprocessing_flag                    true
% 2.43/1.00  --time_out_prep_mult                    0.1
% 2.43/1.00  --splitting_mode                        input
% 2.43/1.00  --splitting_grd                         true
% 2.43/1.00  --splitting_cvd                         false
% 2.43/1.00  --splitting_cvd_svl                     false
% 2.43/1.00  --splitting_nvd                         32
% 2.43/1.00  --sub_typing                            true
% 2.43/1.00  --prep_gs_sim                           true
% 2.43/1.00  --prep_unflatten                        true
% 2.43/1.00  --prep_res_sim                          true
% 2.43/1.00  --prep_upred                            true
% 2.43/1.00  --prep_sem_filter                       exhaustive
% 2.43/1.00  --prep_sem_filter_out                   false
% 2.43/1.00  --pred_elim                             true
% 2.43/1.00  --res_sim_input                         true
% 2.43/1.00  --eq_ax_congr_red                       true
% 2.43/1.00  --pure_diseq_elim                       true
% 2.43/1.00  --brand_transform                       false
% 2.43/1.00  --non_eq_to_eq                          false
% 2.43/1.00  --prep_def_merge                        true
% 2.43/1.00  --prep_def_merge_prop_impl              false
% 2.43/1.00  --prep_def_merge_mbd                    true
% 2.43/1.00  --prep_def_merge_tr_red                 false
% 2.43/1.00  --prep_def_merge_tr_cl                  false
% 2.43/1.00  --smt_preprocessing                     true
% 2.43/1.00  --smt_ac_axioms                         fast
% 2.43/1.00  --preprocessed_out                      false
% 2.43/1.00  --preprocessed_stats                    false
% 2.43/1.00  
% 2.43/1.00  ------ Abstraction refinement Options
% 2.43/1.00  
% 2.43/1.00  --abstr_ref                             []
% 2.43/1.00  --abstr_ref_prep                        false
% 2.43/1.00  --abstr_ref_until_sat                   false
% 2.43/1.00  --abstr_ref_sig_restrict                funpre
% 2.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.00  --abstr_ref_under                       []
% 2.43/1.00  
% 2.43/1.00  ------ SAT Options
% 2.43/1.00  
% 2.43/1.00  --sat_mode                              false
% 2.43/1.00  --sat_fm_restart_options                ""
% 2.43/1.00  --sat_gr_def                            false
% 2.43/1.00  --sat_epr_types                         true
% 2.43/1.00  --sat_non_cyclic_types                  false
% 2.43/1.00  --sat_finite_models                     false
% 2.43/1.00  --sat_fm_lemmas                         false
% 2.43/1.00  --sat_fm_prep                           false
% 2.43/1.00  --sat_fm_uc_incr                        true
% 2.43/1.00  --sat_out_model                         small
% 2.43/1.00  --sat_out_clauses                       false
% 2.43/1.00  
% 2.43/1.00  ------ QBF Options
% 2.43/1.00  
% 2.43/1.00  --qbf_mode                              false
% 2.43/1.00  --qbf_elim_univ                         false
% 2.43/1.00  --qbf_dom_inst                          none
% 2.43/1.00  --qbf_dom_pre_inst                      false
% 2.43/1.00  --qbf_sk_in                             false
% 2.43/1.00  --qbf_pred_elim                         true
% 2.43/1.00  --qbf_split                             512
% 2.43/1.00  
% 2.43/1.00  ------ BMC1 Options
% 2.43/1.00  
% 2.43/1.00  --bmc1_incremental                      false
% 2.43/1.00  --bmc1_axioms                           reachable_all
% 2.43/1.00  --bmc1_min_bound                        0
% 2.43/1.00  --bmc1_max_bound                        -1
% 2.43/1.00  --bmc1_max_bound_default                -1
% 2.43/1.00  --bmc1_symbol_reachability              true
% 2.43/1.00  --bmc1_property_lemmas                  false
% 2.43/1.00  --bmc1_k_induction                      false
% 2.43/1.00  --bmc1_non_equiv_states                 false
% 2.43/1.00  --bmc1_deadlock                         false
% 2.43/1.00  --bmc1_ucm                              false
% 2.43/1.00  --bmc1_add_unsat_core                   none
% 2.43/1.00  --bmc1_unsat_core_children              false
% 2.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.00  --bmc1_out_stat                         full
% 2.43/1.00  --bmc1_ground_init                      false
% 2.43/1.00  --bmc1_pre_inst_next_state              false
% 2.43/1.00  --bmc1_pre_inst_state                   false
% 2.43/1.00  --bmc1_pre_inst_reach_state             false
% 2.43/1.00  --bmc1_out_unsat_core                   false
% 2.43/1.00  --bmc1_aig_witness_out                  false
% 2.43/1.00  --bmc1_verbose                          false
% 2.43/1.00  --bmc1_dump_clauses_tptp                false
% 2.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.00  --bmc1_dump_file                        -
% 2.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.00  --bmc1_ucm_extend_mode                  1
% 2.43/1.00  --bmc1_ucm_init_mode                    2
% 2.43/1.00  --bmc1_ucm_cone_mode                    none
% 2.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.00  --bmc1_ucm_relax_model                  4
% 2.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.00  --bmc1_ucm_layered_model                none
% 2.43/1.00  --bmc1_ucm_max_lemma_size               10
% 2.43/1.00  
% 2.43/1.00  ------ AIG Options
% 2.43/1.00  
% 2.43/1.00  --aig_mode                              false
% 2.43/1.00  
% 2.43/1.00  ------ Instantiation Options
% 2.43/1.00  
% 2.43/1.00  --instantiation_flag                    true
% 2.43/1.00  --inst_sos_flag                         false
% 2.43/1.00  --inst_sos_phase                        true
% 2.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel_side                     num_symb
% 2.43/1.00  --inst_solver_per_active                1400
% 2.43/1.00  --inst_solver_calls_frac                1.
% 2.43/1.00  --inst_passive_queue_type               priority_queues
% 2.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.00  --inst_passive_queues_freq              [25;2]
% 2.43/1.00  --inst_dismatching                      true
% 2.43/1.00  --inst_eager_unprocessed_to_passive     true
% 2.43/1.00  --inst_prop_sim_given                   true
% 2.43/1.00  --inst_prop_sim_new                     false
% 2.43/1.00  --inst_subs_new                         false
% 2.43/1.00  --inst_eq_res_simp                      false
% 2.43/1.00  --inst_subs_given                       false
% 2.43/1.00  --inst_orphan_elimination               true
% 2.43/1.00  --inst_learning_loop_flag               true
% 2.43/1.00  --inst_learning_start                   3000
% 2.43/1.00  --inst_learning_factor                  2
% 2.43/1.00  --inst_start_prop_sim_after_learn       3
% 2.43/1.00  --inst_sel_renew                        solver
% 2.43/1.00  --inst_lit_activity_flag                true
% 2.43/1.00  --inst_restr_to_given                   false
% 2.43/1.00  --inst_activity_threshold               500
% 2.43/1.00  --inst_out_proof                        true
% 2.43/1.00  
% 2.43/1.00  ------ Resolution Options
% 2.43/1.00  
% 2.43/1.00  --resolution_flag                       true
% 2.43/1.00  --res_lit_sel                           adaptive
% 2.43/1.00  --res_lit_sel_side                      none
% 2.43/1.00  --res_ordering                          kbo
% 2.43/1.00  --res_to_prop_solver                    active
% 2.43/1.00  --res_prop_simpl_new                    false
% 2.43/1.00  --res_prop_simpl_given                  true
% 2.43/1.00  --res_passive_queue_type                priority_queues
% 2.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.00  --res_passive_queues_freq               [15;5]
% 2.43/1.00  --res_forward_subs                      full
% 2.43/1.00  --res_backward_subs                     full
% 2.43/1.00  --res_forward_subs_resolution           true
% 2.43/1.00  --res_backward_subs_resolution          true
% 2.43/1.00  --res_orphan_elimination                true
% 2.43/1.00  --res_time_limit                        2.
% 2.43/1.00  --res_out_proof                         true
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Options
% 2.43/1.00  
% 2.43/1.00  --superposition_flag                    true
% 2.43/1.00  --sup_passive_queue_type                priority_queues
% 2.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.00  --demod_completeness_check              fast
% 2.43/1.00  --demod_use_ground                      true
% 2.43/1.00  --sup_to_prop_solver                    passive
% 2.43/1.00  --sup_prop_simpl_new                    true
% 2.43/1.00  --sup_prop_simpl_given                  true
% 2.43/1.00  --sup_fun_splitting                     false
% 2.43/1.00  --sup_smt_interval                      50000
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Simplification Setup
% 2.43/1.00  
% 2.43/1.00  --sup_indices_passive                   []
% 2.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_full_bw                           [BwDemod]
% 2.43/1.00  --sup_immed_triv                        [TrivRules]
% 2.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_immed_bw_main                     []
% 2.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  
% 2.43/1.00  ------ Combination Options
% 2.43/1.00  
% 2.43/1.00  --comb_res_mult                         3
% 2.43/1.00  --comb_sup_mult                         2
% 2.43/1.00  --comb_inst_mult                        10
% 2.43/1.00  
% 2.43/1.00  ------ Debug Options
% 2.43/1.00  
% 2.43/1.00  --dbg_backtrace                         false
% 2.43/1.00  --dbg_dump_prop_clauses                 false
% 2.43/1.00  --dbg_dump_prop_clauses_file            -
% 2.43/1.00  --dbg_out_stat                          false
% 2.43/1.00  ------ Parsing...
% 2.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/1.00  ------ Proving...
% 2.43/1.00  ------ Problem Properties 
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  clauses                                 21
% 2.43/1.00  conjectures                             8
% 2.43/1.00  EPR                                     6
% 2.43/1.00  Horn                                    16
% 2.43/1.00  unary                                   8
% 2.43/1.00  binary                                  0
% 2.43/1.00  lits                                    58
% 2.43/1.00  lits eq                                 6
% 2.43/1.00  fd_pure                                 0
% 2.43/1.00  fd_pseudo                               0
% 2.43/1.00  fd_cond                                 0
% 2.43/1.00  fd_pseudo_cond                          1
% 2.43/1.00  AC symbols                              0
% 2.43/1.00  
% 2.43/1.00  ------ Schedule dynamic 5 is on 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  ------ 
% 2.43/1.00  Current options:
% 2.43/1.00  ------ 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options
% 2.43/1.00  
% 2.43/1.00  --out_options                           all
% 2.43/1.00  --tptp_safe_out                         true
% 2.43/1.00  --problem_path                          ""
% 2.43/1.00  --include_path                          ""
% 2.43/1.00  --clausifier                            res/vclausify_rel
% 2.43/1.00  --clausifier_options                    --mode clausify
% 2.43/1.00  --stdin                                 false
% 2.43/1.00  --stats_out                             all
% 2.43/1.00  
% 2.43/1.00  ------ General Options
% 2.43/1.00  
% 2.43/1.00  --fof                                   false
% 2.43/1.00  --time_out_real                         305.
% 2.43/1.00  --time_out_virtual                      -1.
% 2.43/1.00  --symbol_type_check                     false
% 2.43/1.00  --clausify_out                          false
% 2.43/1.00  --sig_cnt_out                           false
% 2.43/1.00  --trig_cnt_out                          false
% 2.43/1.00  --trig_cnt_out_tolerance                1.
% 2.43/1.00  --trig_cnt_out_sk_spl                   false
% 2.43/1.00  --abstr_cl_out                          false
% 2.43/1.00  
% 2.43/1.00  ------ Global Options
% 2.43/1.00  
% 2.43/1.00  --schedule                              default
% 2.43/1.00  --add_important_lit                     false
% 2.43/1.00  --prop_solver_per_cl                    1000
% 2.43/1.00  --min_unsat_core                        false
% 2.43/1.00  --soft_assumptions                      false
% 2.43/1.00  --soft_lemma_size                       3
% 2.43/1.00  --prop_impl_unit_size                   0
% 2.43/1.00  --prop_impl_unit                        []
% 2.43/1.00  --share_sel_clauses                     true
% 2.43/1.00  --reset_solvers                         false
% 2.43/1.00  --bc_imp_inh                            [conj_cone]
% 2.43/1.00  --conj_cone_tolerance                   3.
% 2.43/1.00  --extra_neg_conj                        none
% 2.43/1.00  --large_theory_mode                     true
% 2.43/1.00  --prolific_symb_bound                   200
% 2.43/1.00  --lt_threshold                          2000
% 2.43/1.00  --clause_weak_htbl                      true
% 2.43/1.00  --gc_record_bc_elim                     false
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing Options
% 2.43/1.00  
% 2.43/1.00  --preprocessing_flag                    true
% 2.43/1.00  --time_out_prep_mult                    0.1
% 2.43/1.00  --splitting_mode                        input
% 2.43/1.00  --splitting_grd                         true
% 2.43/1.00  --splitting_cvd                         false
% 2.43/1.00  --splitting_cvd_svl                     false
% 2.43/1.00  --splitting_nvd                         32
% 2.43/1.00  --sub_typing                            true
% 2.43/1.00  --prep_gs_sim                           true
% 2.43/1.00  --prep_unflatten                        true
% 2.43/1.00  --prep_res_sim                          true
% 2.43/1.00  --prep_upred                            true
% 2.43/1.00  --prep_sem_filter                       exhaustive
% 2.43/1.00  --prep_sem_filter_out                   false
% 2.43/1.00  --pred_elim                             true
% 2.43/1.00  --res_sim_input                         true
% 2.43/1.00  --eq_ax_congr_red                       true
% 2.43/1.00  --pure_diseq_elim                       true
% 2.43/1.00  --brand_transform                       false
% 2.43/1.00  --non_eq_to_eq                          false
% 2.43/1.00  --prep_def_merge                        true
% 2.43/1.00  --prep_def_merge_prop_impl              false
% 2.43/1.00  --prep_def_merge_mbd                    true
% 2.43/1.00  --prep_def_merge_tr_red                 false
% 2.43/1.00  --prep_def_merge_tr_cl                  false
% 2.43/1.00  --smt_preprocessing                     true
% 2.43/1.00  --smt_ac_axioms                         fast
% 2.43/1.00  --preprocessed_out                      false
% 2.43/1.00  --preprocessed_stats                    false
% 2.43/1.00  
% 2.43/1.00  ------ Abstraction refinement Options
% 2.43/1.00  
% 2.43/1.00  --abstr_ref                             []
% 2.43/1.00  --abstr_ref_prep                        false
% 2.43/1.00  --abstr_ref_until_sat                   false
% 2.43/1.00  --abstr_ref_sig_restrict                funpre
% 2.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.00  --abstr_ref_under                       []
% 2.43/1.00  
% 2.43/1.00  ------ SAT Options
% 2.43/1.00  
% 2.43/1.00  --sat_mode                              false
% 2.43/1.00  --sat_fm_restart_options                ""
% 2.43/1.00  --sat_gr_def                            false
% 2.43/1.00  --sat_epr_types                         true
% 2.43/1.00  --sat_non_cyclic_types                  false
% 2.43/1.00  --sat_finite_models                     false
% 2.43/1.00  --sat_fm_lemmas                         false
% 2.43/1.00  --sat_fm_prep                           false
% 2.43/1.00  --sat_fm_uc_incr                        true
% 2.43/1.00  --sat_out_model                         small
% 2.43/1.00  --sat_out_clauses                       false
% 2.43/1.00  
% 2.43/1.00  ------ QBF Options
% 2.43/1.00  
% 2.43/1.00  --qbf_mode                              false
% 2.43/1.00  --qbf_elim_univ                         false
% 2.43/1.00  --qbf_dom_inst                          none
% 2.43/1.00  --qbf_dom_pre_inst                      false
% 2.43/1.00  --qbf_sk_in                             false
% 2.43/1.00  --qbf_pred_elim                         true
% 2.43/1.00  --qbf_split                             512
% 2.43/1.00  
% 2.43/1.00  ------ BMC1 Options
% 2.43/1.00  
% 2.43/1.00  --bmc1_incremental                      false
% 2.43/1.00  --bmc1_axioms                           reachable_all
% 2.43/1.00  --bmc1_min_bound                        0
% 2.43/1.00  --bmc1_max_bound                        -1
% 2.43/1.00  --bmc1_max_bound_default                -1
% 2.43/1.00  --bmc1_symbol_reachability              true
% 2.43/1.00  --bmc1_property_lemmas                  false
% 2.43/1.00  --bmc1_k_induction                      false
% 2.43/1.00  --bmc1_non_equiv_states                 false
% 2.43/1.00  --bmc1_deadlock                         false
% 2.43/1.00  --bmc1_ucm                              false
% 2.43/1.00  --bmc1_add_unsat_core                   none
% 2.43/1.00  --bmc1_unsat_core_children              false
% 2.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.00  --bmc1_out_stat                         full
% 2.43/1.00  --bmc1_ground_init                      false
% 2.43/1.00  --bmc1_pre_inst_next_state              false
% 2.43/1.00  --bmc1_pre_inst_state                   false
% 2.43/1.00  --bmc1_pre_inst_reach_state             false
% 2.43/1.00  --bmc1_out_unsat_core                   false
% 2.43/1.00  --bmc1_aig_witness_out                  false
% 2.43/1.00  --bmc1_verbose                          false
% 2.43/1.00  --bmc1_dump_clauses_tptp                false
% 2.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.00  --bmc1_dump_file                        -
% 2.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.00  --bmc1_ucm_extend_mode                  1
% 2.43/1.00  --bmc1_ucm_init_mode                    2
% 2.43/1.00  --bmc1_ucm_cone_mode                    none
% 2.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.00  --bmc1_ucm_relax_model                  4
% 2.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.00  --bmc1_ucm_layered_model                none
% 2.43/1.00  --bmc1_ucm_max_lemma_size               10
% 2.43/1.00  
% 2.43/1.00  ------ AIG Options
% 2.43/1.00  
% 2.43/1.00  --aig_mode                              false
% 2.43/1.00  
% 2.43/1.00  ------ Instantiation Options
% 2.43/1.00  
% 2.43/1.00  --instantiation_flag                    true
% 2.43/1.00  --inst_sos_flag                         false
% 2.43/1.00  --inst_sos_phase                        true
% 2.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel_side                     none
% 2.43/1.00  --inst_solver_per_active                1400
% 2.43/1.00  --inst_solver_calls_frac                1.
% 2.43/1.00  --inst_passive_queue_type               priority_queues
% 2.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.00  --inst_passive_queues_freq              [25;2]
% 2.43/1.00  --inst_dismatching                      true
% 2.43/1.00  --inst_eager_unprocessed_to_passive     true
% 2.43/1.00  --inst_prop_sim_given                   true
% 2.43/1.00  --inst_prop_sim_new                     false
% 2.43/1.00  --inst_subs_new                         false
% 2.43/1.00  --inst_eq_res_simp                      false
% 2.43/1.00  --inst_subs_given                       false
% 2.43/1.00  --inst_orphan_elimination               true
% 2.43/1.00  --inst_learning_loop_flag               true
% 2.43/1.00  --inst_learning_start                   3000
% 2.43/1.00  --inst_learning_factor                  2
% 2.43/1.00  --inst_start_prop_sim_after_learn       3
% 2.43/1.00  --inst_sel_renew                        solver
% 2.43/1.00  --inst_lit_activity_flag                true
% 2.43/1.00  --inst_restr_to_given                   false
% 2.43/1.00  --inst_activity_threshold               500
% 2.43/1.00  --inst_out_proof                        true
% 2.43/1.00  
% 2.43/1.00  ------ Resolution Options
% 2.43/1.00  
% 2.43/1.00  --resolution_flag                       false
% 2.43/1.00  --res_lit_sel                           adaptive
% 2.43/1.00  --res_lit_sel_side                      none
% 2.43/1.00  --res_ordering                          kbo
% 2.43/1.00  --res_to_prop_solver                    active
% 2.43/1.00  --res_prop_simpl_new                    false
% 2.43/1.00  --res_prop_simpl_given                  true
% 2.43/1.00  --res_passive_queue_type                priority_queues
% 2.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.00  --res_passive_queues_freq               [15;5]
% 2.43/1.00  --res_forward_subs                      full
% 2.43/1.00  --res_backward_subs                     full
% 2.43/1.00  --res_forward_subs_resolution           true
% 2.43/1.00  --res_backward_subs_resolution          true
% 2.43/1.00  --res_orphan_elimination                true
% 2.43/1.00  --res_time_limit                        2.
% 2.43/1.00  --res_out_proof                         true
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Options
% 2.43/1.00  
% 2.43/1.00  --superposition_flag                    true
% 2.43/1.00  --sup_passive_queue_type                priority_queues
% 2.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.00  --demod_completeness_check              fast
% 2.43/1.00  --demod_use_ground                      true
% 2.43/1.00  --sup_to_prop_solver                    passive
% 2.43/1.00  --sup_prop_simpl_new                    true
% 2.43/1.00  --sup_prop_simpl_given                  true
% 2.43/1.00  --sup_fun_splitting                     false
% 2.43/1.00  --sup_smt_interval                      50000
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Simplification Setup
% 2.43/1.00  
% 2.43/1.00  --sup_indices_passive                   []
% 2.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_full_bw                           [BwDemod]
% 2.43/1.00  --sup_immed_triv                        [TrivRules]
% 2.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_immed_bw_main                     []
% 2.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  
% 2.43/1.00  ------ Combination Options
% 2.43/1.00  
% 2.43/1.00  --comb_res_mult                         3
% 2.43/1.00  --comb_sup_mult                         2
% 2.43/1.00  --comb_inst_mult                        10
% 2.43/1.00  
% 2.43/1.00  ------ Debug Options
% 2.43/1.00  
% 2.43/1.00  --dbg_backtrace                         false
% 2.43/1.00  --dbg_dump_prop_clauses                 false
% 2.43/1.00  --dbg_dump_prop_clauses_file            -
% 2.43/1.00  --dbg_out_stat                          false
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  ------ Proving...
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  % SZS status Theorem for theBenchmark.p
% 2.43/1.00  
% 2.43/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/1.00  
% 2.43/1.00  fof(f72,plain,(
% 2.43/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.43/1.00    inference(cnf_transformation,[],[f42])).
% 2.43/1.00  
% 2.43/1.00  fof(f13,conjecture,(
% 2.43/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.43/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.00  
% 2.43/1.00  fof(f14,negated_conjecture,(
% 2.43/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.43/1.00    inference(negated_conjecture,[],[f13])).
% 2.43/1.00  
% 2.43/1.00  fof(f32,plain,(
% 2.43/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.43/1.00    inference(ennf_transformation,[],[f14])).
% 2.43/1.00  
% 2.43/1.00  fof(f33,plain,(
% 2.43/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.43/1.00    inference(flattening,[],[f32])).
% 2.43/1.00  
% 2.43/1.00  fof(f41,plain,(
% 2.43/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)) & sK4 = X3 & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.43/1.00    introduced(choice_axiom,[])).
% 2.43/1.00  
% 2.43/1.00  fof(f40,plain,(
% 2.43/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3,u1_struct_0(X1)))) )),
% 2.43/1.00    introduced(choice_axiom,[])).
% 2.43/1.00  
% 2.43/1.00  fof(f39,plain,(
% 2.43/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK2,X0,X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK2,X0,X1) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f38,plain,(
% 2.43/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,k6_domain_1(u1_struct_0(sK1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK1))) & v3_borsuk_1(X2,X0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v5_pre_topc(X2,X0,sK1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & m1_pre_topc(sK1,X0) & v4_tex_2(sK1,X0) & ~v2_struct_0(sK1))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f37,plain,(
% 2.43/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v5_pre_topc(X2,sK0,X1) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK0) & v4_tex_2(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f42,plain,(
% 2.43/1.01    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) & sK3 = sK4 & m1_subset_1(sK4,u1_struct_0(sK0))) & m1_subset_1(sK3,u1_struct_0(sK1))) & v3_borsuk_1(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v5_pre_topc(sK2,sK0,sK1) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & m1_pre_topc(sK1,sK0) & v4_tex_2(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f41,f40,f39,f38,f37])).
% 2.43/1.01  
% 2.43/1.01  fof(f74,plain,(
% 2.43/1.01    sK3 = sK4),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f78,plain,(
% 2.43/1.01    m1_subset_1(sK4,u1_struct_0(sK1))),
% 2.43/1.01    inference(definition_unfolding,[],[f72,f74])).
% 2.43/1.01  
% 2.43/1.01  fof(f10,axiom,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f26,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f10])).
% 2.43/1.01  
% 2.43/1.01  fof(f27,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(flattening,[],[f26])).
% 2.43/1.01  
% 2.43/1.01  fof(f36,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(nnf_transformation,[],[f27])).
% 2.43/1.01  
% 2.43/1.01  fof(f54,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f36])).
% 2.43/1.01  
% 2.43/1.01  fof(f79,plain,(
% 2.43/1.01    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(equality_resolution,[],[f54])).
% 2.43/1.01  
% 2.43/1.01  fof(f11,axiom,(
% 2.43/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f28,plain,(
% 2.43/1.01    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f11])).
% 2.43/1.01  
% 2.43/1.01  fof(f29,plain,(
% 2.43/1.01    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(flattening,[],[f28])).
% 2.43/1.01  
% 2.43/1.01  fof(f58,plain,(
% 2.43/1.01    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f29])).
% 2.43/1.01  
% 2.43/1.01  fof(f56,plain,(
% 2.43/1.01    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f29])).
% 2.43/1.01  
% 2.43/1.01  fof(f57,plain,(
% 2.43/1.01    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f29])).
% 2.43/1.01  
% 2.43/1.01  fof(f7,axiom,(
% 2.43/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f20,plain,(
% 2.43/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f7])).
% 2.43/1.01  
% 2.43/1.01  fof(f21,plain,(
% 2.43/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.43/1.01    inference(flattening,[],[f20])).
% 2.43/1.01  
% 2.43/1.01  fof(f50,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f21])).
% 2.43/1.01  
% 2.43/1.01  fof(f1,axiom,(
% 2.43/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f43,plain,(
% 2.43/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f1])).
% 2.43/1.01  
% 2.43/1.01  fof(f76,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.43/1.01    inference(definition_unfolding,[],[f50,f43])).
% 2.43/1.01  
% 2.43/1.01  fof(f3,axiom,(
% 2.43/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f15,plain,(
% 2.43/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f3])).
% 2.43/1.01  
% 2.43/1.01  fof(f46,plain,(
% 2.43/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f15])).
% 2.43/1.01  
% 2.43/1.01  fof(f5,axiom,(
% 2.43/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f17,plain,(
% 2.43/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f5])).
% 2.43/1.01  
% 2.43/1.01  fof(f18,plain,(
% 2.43/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(flattening,[],[f17])).
% 2.43/1.01  
% 2.43/1.01  fof(f48,plain,(
% 2.43/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f18])).
% 2.43/1.01  
% 2.43/1.01  fof(f63,plain,(
% 2.43/1.01    l1_pre_topc(sK0)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f64,plain,(
% 2.43/1.01    ~v2_struct_0(sK1)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f66,plain,(
% 2.43/1.01    m1_pre_topc(sK1,sK0)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f4,axiom,(
% 2.43/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f16,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f4])).
% 2.43/1.01  
% 2.43/1.01  fof(f47,plain,(
% 2.43/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f16])).
% 2.43/1.01  
% 2.43/1.01  fof(f2,axiom,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f34,plain,(
% 2.43/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.43/1.01    inference(nnf_transformation,[],[f2])).
% 2.43/1.01  
% 2.43/1.01  fof(f45,plain,(
% 2.43/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f34])).
% 2.43/1.01  
% 2.43/1.01  fof(f8,axiom,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f22,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f8])).
% 2.43/1.01  
% 2.43/1.01  fof(f23,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.43/1.01    inference(flattening,[],[f22])).
% 2.43/1.01  
% 2.43/1.01  fof(f35,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.43/1.01    inference(nnf_transformation,[],[f23])).
% 2.43/1.01  
% 2.43/1.01  fof(f52,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f35])).
% 2.43/1.01  
% 2.43/1.01  fof(f61,plain,(
% 2.43/1.01    v2_pre_topc(sK0)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f9,axiom,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f24,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f9])).
% 2.43/1.01  
% 2.43/1.01  fof(f25,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.43/1.01    inference(flattening,[],[f24])).
% 2.43/1.01  
% 2.43/1.01  fof(f53,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f25])).
% 2.43/1.01  
% 2.43/1.01  fof(f12,axiom,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f30,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f12])).
% 2.43/1.01  
% 2.43/1.01  fof(f31,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(flattening,[],[f30])).
% 2.43/1.01  
% 2.43/1.01  fof(f59,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f31])).
% 2.43/1.01  
% 2.43/1.01  fof(f80,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(equality_resolution,[],[f59])).
% 2.43/1.01  
% 2.43/1.01  fof(f71,plain,(
% 2.43/1.01    v3_borsuk_1(sK2,sK0,sK1)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f60,plain,(
% 2.43/1.01    ~v2_struct_0(sK0)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f62,plain,(
% 2.43/1.01    v3_tdlat_3(sK0)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f65,plain,(
% 2.43/1.01    v4_tex_2(sK1,sK0)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f67,plain,(
% 2.43/1.01    v1_funct_1(sK2)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f68,plain,(
% 2.43/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f69,plain,(
% 2.43/1.01    v5_pre_topc(sK2,sK0,sK1)),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f70,plain,(
% 2.43/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f6,axiom,(
% 2.43/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f19,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f6])).
% 2.43/1.01  
% 2.43/1.01  fof(f49,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f19])).
% 2.43/1.01  
% 2.43/1.01  fof(f73,plain,(
% 2.43/1.01    m1_subset_1(sK4,u1_struct_0(sK0))),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f75,plain,(
% 2.43/1.01    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 2.43/1.01    inference(cnf_transformation,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f77,plain,(
% 2.43/1.01    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 2.43/1.01    inference(definition_unfolding,[],[f75,f74])).
% 2.43/1.01  
% 2.43/1.01  cnf(c_18,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_836,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1261,plain,
% 2.43/1.01      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_11,plain,
% 2.43/1.01      ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.43/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/1.01      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 2.43/1.01      | v2_struct_0(X0)
% 2.43/1.01      | v2_struct_0(k1_tex_2(X0,X1))
% 2.43/1.01      | ~ l1_pre_topc(X0)
% 2.43/1.01      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_12,plain,
% 2.43/1.01      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.43/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/1.01      | v2_struct_0(X0)
% 2.43/1.01      | ~ l1_pre_topc(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_164,plain,
% 2.43/1.01      ( ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/1.01      | ~ v1_pre_topc(k1_tex_2(X0,X1))
% 2.43/1.01      | v2_struct_0(X0)
% 2.43/1.01      | v2_struct_0(k1_tex_2(X0,X1))
% 2.43/1.01      | ~ l1_pre_topc(X0)
% 2.43/1.01      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_11,c_12]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_165,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/1.01      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 2.43/1.01      | v2_struct_0(X1)
% 2.43/1.01      | v2_struct_0(k1_tex_2(X1,X0))
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_164]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_14,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/1.01      | v2_struct_0(X1)
% 2.43/1.01      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.43/1.01      | ~ l1_pre_topc(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_13,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/1.01      | v1_pre_topc(k1_tex_2(X1,X0))
% 2.43/1.01      | v2_struct_0(X1)
% 2.43/1.01      | ~ l1_pre_topc(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_170,plain,
% 2.43/1.01      ( v2_struct_0(X1)
% 2.43/1.01      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_165,c_14,c_13]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_171,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.43/1.01      | v2_struct_0(X1)
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_170]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_830,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 2.43/1.01      | v2_struct_0(X0_55)
% 2.43/1.01      | ~ l1_pre_topc(X0_55)
% 2.43/1.01      | k6_domain_1(u1_struct_0(X0_55),X0_56) = u1_struct_0(k1_tex_2(X0_55,X0_56)) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_171]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1267,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(X0_55),X0_56) = u1_struct_0(k1_tex_2(X0_55,X0_56))
% 2.43/1.01      | m1_subset_1(X0_56,u1_struct_0(X0_55)) != iProver_top
% 2.43/1.01      | v2_struct_0(X0_55) = iProver_top
% 2.43/1.01      | l1_pre_topc(X0_55) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2575,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK1),sK4) = u1_struct_0(k1_tex_2(sK1,sK4))
% 2.43/1.01      | v2_struct_0(sK1) = iProver_top
% 2.43/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1261,c_1267]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_6,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,X1)
% 2.43/1.01      | v1_xboole_0(X1)
% 2.43/1.01      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_843,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0_56,X1_56)
% 2.43/1.01      | v1_xboole_0(X1_56)
% 2.43/1.01      | k6_domain_1(X1_56,X0_56) = k2_tarski(X0_56,X0_56) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1255,plain,
% 2.43/1.01      ( k6_domain_1(X0_56,X1_56) = k2_tarski(X1_56,X1_56)
% 2.43/1.01      | m1_subset_1(X1_56,X0_56) != iProver_top
% 2.43/1.01      | v1_xboole_0(X0_56) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1585,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
% 2.43/1.01      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1261,c_1255]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2,plain,
% 2.43/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4,plain,
% 2.43/1.01      ( v2_struct_0(X0)
% 2.43/1.01      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.43/1.01      | ~ l1_struct_0(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_401,plain,
% 2.43/1.01      ( v2_struct_0(X0)
% 2.43/1.01      | ~ v1_xboole_0(u1_struct_0(X0))
% 2.43/1.01      | ~ l1_pre_topc(X0) ),
% 2.43/1.01      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_829,plain,
% 2.43/1.01      ( v2_struct_0(X0_55)
% 2.43/1.01      | ~ v1_xboole_0(u1_struct_0(X0_55))
% 2.43/1.01      | ~ l1_pre_topc(X0_55) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_401]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1268,plain,
% 2.43/1.01      ( v2_struct_0(X0_55) = iProver_top
% 2.43/1.01      | v1_xboole_0(u1_struct_0(X0_55)) != iProver_top
% 2.43/1.01      | l1_pre_topc(X0_55) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2133,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4)
% 2.43/1.01      | v2_struct_0(sK1) = iProver_top
% 2.43/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1585,c_1268]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_27,negated_conjecture,
% 2.43/1.01      ( l1_pre_topc(sK0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_34,plain,
% 2.43/1.01      ( l1_pre_topc(sK0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_26,negated_conjecture,
% 2.43/1.01      ( ~ v2_struct_0(sK1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_35,plain,
% 2.43/1.01      ( v2_struct_0(sK1) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_24,negated_conjecture,
% 2.43/1.01      ( m1_pre_topc(sK1,sK0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_37,plain,
% 2.43/1.01      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_845,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.43/1.01      | ~ l1_pre_topc(X1_55)
% 2.43/1.01      | l1_pre_topc(X0_55) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1525,plain,
% 2.43/1.01      ( ~ m1_pre_topc(sK1,X0_55)
% 2.43/1.01      | ~ l1_pre_topc(X0_55)
% 2.43/1.01      | l1_pre_topc(sK1) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_845]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1526,plain,
% 2.43/1.01      ( m1_pre_topc(sK1,X0_55) != iProver_top
% 2.43/1.01      | l1_pre_topc(X0_55) != iProver_top
% 2.43/1.01      | l1_pre_topc(sK1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1528,plain,
% 2.43/1.01      ( m1_pre_topc(sK1,sK0) != iProver_top
% 2.43/1.01      | l1_pre_topc(sK1) = iProver_top
% 2.43/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1526]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2420,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK1),sK4) = k2_tarski(sK4,sK4) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_2133,c_34,c_35,c_37,c_1528]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2579,plain,
% 2.43/1.01      ( u1_struct_0(k1_tex_2(sK1,sK4)) = k2_tarski(sK4,sK4)
% 2.43/1.01      | v2_struct_0(sK1) = iProver_top
% 2.43/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.43/1.01      inference(light_normalisation,[status(thm)],[c_2575,c_2420]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2808,plain,
% 2.43/1.01      ( u1_struct_0(k1_tex_2(sK1,sK4)) = k2_tarski(sK4,sK4) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_2579,c_34,c_35,c_37,c_1528]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_0,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_222,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.43/1.01      inference(prop_impl,[status(thm)],[c_0]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_7,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X0,X2)
% 2.43/1.01      | ~ m1_pre_topc(X2,X1)
% 2.43/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.43/1.01      | ~ v2_pre_topc(X1)
% 2.43/1.01      | ~ l1_pre_topc(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_29,negated_conjecture,
% 2.43/1.01      ( v2_pre_topc(sK0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_550,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X0,X2)
% 2.43/1.01      | ~ m1_pre_topc(X2,X1)
% 2.43/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | sK0 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_551,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X0,sK0)
% 2.43/1.01      | ~ m1_pre_topc(X1,sK0)
% 2.43/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.43/1.01      | ~ l1_pre_topc(sK0) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_550]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_9,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X2,X0)
% 2.43/1.01      | m1_pre_topc(X2,X1)
% 2.43/1.01      | ~ v2_pre_topc(X1)
% 2.43/1.01      | ~ l1_pre_topc(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_513,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X2,X0)
% 2.43/1.01      | m1_pre_topc(X2,X1)
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | sK0 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_514,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X1,sK0)
% 2.43/1.01      | m1_pre_topc(X0,sK0)
% 2.43/1.01      | ~ l1_pre_topc(sK0) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_513]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_555,plain,
% 2.43/1.01      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 2.43/1.01      | ~ m1_pre_topc(X1,sK0)
% 2.43/1.01      | ~ m1_pre_topc(X0,X1) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_551,c_27,c_514]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_556,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X1,sK0)
% 2.43/1.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_555]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_602,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X1,sK0)
% 2.43/1.01      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.43/1.01      | u1_struct_0(X1) != X3
% 2.43/1.01      | u1_struct_0(X0) != X2 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_222,c_556]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_603,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_pre_topc(X1,sK0)
% 2.43/1.01      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_602]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_825,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.43/1.01      | ~ m1_pre_topc(X1_55,sK0)
% 2.43/1.01      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55))) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_603]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1272,plain,
% 2.43/1.01      ( m1_pre_topc(X0_55,X1_55) != iProver_top
% 2.43/1.01      | m1_pre_topc(X1_55,sK0) != iProver_top
% 2.43/1.01      | m1_subset_1(u1_struct_0(X0_55),k1_zfmisc_1(u1_struct_0(X1_55))) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2815,plain,
% 2.43/1.01      ( m1_pre_topc(X0_55,sK0) != iProver_top
% 2.43/1.01      | m1_pre_topc(k1_tex_2(sK1,sK4),X0_55) != iProver_top
% 2.43/1.01      | m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(X0_55))) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2808,c_1272]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_15,plain,
% 2.43/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.43/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 2.43/1.01      | ~ v3_borsuk_1(X0,X1,X2)
% 2.43/1.01      | ~ v4_tex_2(X2,X1)
% 2.43/1.01      | ~ m1_pre_topc(X2,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.43/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.43/1.01      | ~ v3_tdlat_3(X1)
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | ~ v2_pre_topc(X1)
% 2.43/1.01      | v2_struct_0(X1)
% 2.43/1.01      | v2_struct_0(X2)
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 2.43/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_19,negated_conjecture,
% 2.43/1.01      ( v3_borsuk_1(sK2,sK0,sK1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_488,plain,
% 2.43/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.43/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 2.43/1.01      | ~ v4_tex_2(X2,X1)
% 2.43/1.01      | ~ m1_pre_topc(X2,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.43/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.43/1.01      | ~ v3_tdlat_3(X1)
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | ~ v2_pre_topc(X1)
% 2.43/1.01      | v2_struct_0(X2)
% 2.43/1.01      | v2_struct_0(X1)
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 2.43/1.01      | sK2 != X0
% 2.43/1.01      | sK1 != X2
% 2.43/1.01      | sK0 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_489,plain,
% 2.43/1.01      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.43/1.01      | ~ v5_pre_topc(sK2,sK0,sK1)
% 2.43/1.01      | ~ v4_tex_2(sK1,sK0)
% 2.43/1.01      | ~ m1_pre_topc(sK1,sK0)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.43/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.43/1.01      | ~ v3_tdlat_3(sK0)
% 2.43/1.01      | ~ v1_funct_1(sK2)
% 2.43/1.01      | ~ v2_pre_topc(sK0)
% 2.43/1.01      | v2_struct_0(sK1)
% 2.43/1.01      | v2_struct_0(sK0)
% 2.43/1.01      | ~ l1_pre_topc(sK0)
% 2.43/1.01      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k2_pre_topc(sK0,X0) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_488]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_30,negated_conjecture,
% 2.43/1.01      ( ~ v2_struct_0(sK0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_28,negated_conjecture,
% 2.43/1.01      ( v3_tdlat_3(sK0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_25,negated_conjecture,
% 2.43/1.01      ( v4_tex_2(sK1,sK0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_23,negated_conjecture,
% 2.43/1.01      ( v1_funct_1(sK2) ),
% 2.43/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_22,negated_conjecture,
% 2.43/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_21,negated_conjecture,
% 2.43/1.01      ( v5_pre_topc(sK2,sK0,sK1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_20,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.43/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_493,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.43/1.01      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k2_pre_topc(sK0,X0) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_489,c_30,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,
% 2.43/1.01                 c_20]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_494,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.43/1.01      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k2_pre_topc(sK0,X0) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_493]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_828,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.43/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.43/1.01      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_494]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1269,plain,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56)
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_909,plain,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56)
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.43/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ l1_pre_topc(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_844,plain,
% 2.43/1.01      ( ~ m1_pre_topc(X0_55,X1_55)
% 2.43/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X0_55)))
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(X1_55)))
% 2.43/1.01      | ~ l1_pre_topc(X1_55) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1490,plain,
% 2.43/1.01      ( ~ m1_pre_topc(sK1,sK0)
% 2.43/1.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.43/1.01      | ~ l1_pre_topc(sK0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_844]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1491,plain,
% 2.43/1.01      ( m1_pre_topc(sK1,sK0) != iProver_top
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.43/1.01      | l1_pre_topc(sK0) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1882,plain,
% 2.43/1.01      ( m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.43/1.01      | k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_1269,c_34,c_37,c_909,c_1491]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1883,plain,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0_56) = k2_pre_topc(sK0,X0_56)
% 2.43/1.01      | m1_subset_1(X0_56,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_1882]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3246,plain,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) = k2_pre_topc(sK0,k2_tarski(sK4,sK4))
% 2.43/1.01      | m1_pre_topc(k1_tex_2(sK1,sK4),sK1) != iProver_top
% 2.43/1.01      | m1_pre_topc(sK1,sK0) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2815,c_1883]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_17,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_837,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK4,u1_struct_0(sK0)) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1260,plain,
% 2.43/1.01      ( m1_subset_1(sK4,u1_struct_0(sK0)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1584,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4)
% 2.43/1.01      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1260,c_1255]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_73,plain,
% 2.43/1.01      ( v2_struct_0(sK0)
% 2.43/1.01      | ~ v1_xboole_0(u1_struct_0(sK0))
% 2.43/1.01      | ~ l1_struct_0(sK0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_77,plain,
% 2.43/1.01      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1477,plain,
% 2.43/1.01      ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
% 2.43/1.01      | v1_xboole_0(u1_struct_0(sK0))
% 2.43/1.01      | k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_843]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1971,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK0),sK4) = k2_tarski(sK4,sK4) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_1584,c_30,c_27,c_17,c_73,c_77,c_1477]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_16,negated_conjecture,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_838,negated_conjecture,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1974,plain,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_1971,c_838]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2423,plain,
% 2.43/1.01      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_tarski(sK4,sK4)) != k2_pre_topc(sK0,k2_tarski(sK4,sK4)) ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_2420,c_1974]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_841,plain,
% 2.43/1.01      ( m1_pre_topc(k1_tex_2(X0_55,X0_56),X0_55)
% 2.43/1.01      | ~ m1_subset_1(X0_56,u1_struct_0(X0_55))
% 2.43/1.01      | v2_struct_0(X0_55)
% 2.43/1.01      | ~ l1_pre_topc(X0_55) ),
% 2.43/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1474,plain,
% 2.43/1.01      ( m1_pre_topc(k1_tex_2(sK1,sK4),sK1)
% 2.43/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK1))
% 2.43/1.01      | v2_struct_0(sK1)
% 2.43/1.01      | ~ l1_pre_topc(sK1) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_841]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1475,plain,
% 2.43/1.01      ( m1_pre_topc(k1_tex_2(sK1,sK4),sK1) = iProver_top
% 2.43/1.01      | m1_subset_1(sK4,u1_struct_0(sK1)) != iProver_top
% 2.43/1.01      | v2_struct_0(sK1) = iProver_top
% 2.43/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_43,plain,
% 2.43/1.01      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(contradiction,plain,
% 2.43/1.01      ( $false ),
% 2.43/1.01      inference(minisat,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_3246,c_2423,c_1528,c_1475,c_43,c_37,c_35,c_34]) ).
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  ------                               Statistics
% 2.43/1.01  
% 2.43/1.01  ------ General
% 2.43/1.01  
% 2.43/1.01  abstr_ref_over_cycles:                  0
% 2.43/1.01  abstr_ref_under_cycles:                 0
% 2.43/1.01  gc_basic_clause_elim:                   0
% 2.43/1.01  forced_gc_time:                         0
% 2.43/1.01  parsing_time:                           0.015
% 2.43/1.01  unif_index_cands_time:                  0.
% 2.43/1.01  unif_index_add_time:                    0.
% 2.43/1.01  orderings_time:                         0.
% 2.43/1.01  out_proof_time:                         0.014
% 2.43/1.01  total_time:                             0.145
% 2.43/1.01  num_of_symbols:                         61
% 2.43/1.01  num_of_terms:                           2489
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing
% 2.43/1.01  
% 2.43/1.01  num_of_splits:                          0
% 2.43/1.01  num_of_split_atoms:                     0
% 2.43/1.01  num_of_reused_defs:                     0
% 2.43/1.01  num_eq_ax_congr_red:                    13
% 2.43/1.01  num_of_sem_filtered_clauses:            1
% 2.43/1.01  num_of_subtypes:                        3
% 2.43/1.01  monotx_restored_types:                  0
% 2.43/1.01  sat_num_of_epr_types:                   0
% 2.43/1.01  sat_num_of_non_cyclic_types:            0
% 2.43/1.01  sat_guarded_non_collapsed_types:        1
% 2.43/1.01  num_pure_diseq_elim:                    0
% 2.43/1.01  simp_replaced_by:                       0
% 2.43/1.01  res_preprocessed:                       131
% 2.43/1.01  prep_upred:                             0
% 2.43/1.01  prep_unflattend:                        14
% 2.43/1.01  smt_new_axioms:                         0
% 2.43/1.01  pred_elim_cands:                        6
% 2.43/1.01  pred_elim:                              9
% 2.43/1.01  pred_elim_cl:                           10
% 2.43/1.01  pred_elim_cycles:                       14
% 2.43/1.01  merged_defs:                            2
% 2.43/1.01  merged_defs_ncl:                        0
% 2.43/1.01  bin_hyper_res:                          2
% 2.43/1.01  prep_cycles:                            4
% 2.43/1.01  pred_elim_time:                         0.006
% 2.43/1.01  splitting_time:                         0.
% 2.43/1.01  sem_filter_time:                        0.
% 2.43/1.01  monotx_time:                            0.
% 2.43/1.01  subtype_inf_time:                       0.013
% 2.43/1.01  
% 2.43/1.01  ------ Problem properties
% 2.43/1.01  
% 2.43/1.01  clauses:                                21
% 2.43/1.01  conjectures:                            8
% 2.43/1.01  epr:                                    6
% 2.43/1.01  horn:                                   16
% 2.43/1.01  ground:                                 8
% 2.43/1.01  unary:                                  8
% 2.43/1.01  binary:                                 0
% 2.43/1.01  lits:                                   58
% 2.43/1.01  lits_eq:                                6
% 2.43/1.01  fd_pure:                                0
% 2.43/1.01  fd_pseudo:                              0
% 2.43/1.01  fd_cond:                                0
% 2.43/1.01  fd_pseudo_cond:                         1
% 2.43/1.01  ac_symbols:                             0
% 2.43/1.01  
% 2.43/1.01  ------ Propositional Solver
% 2.43/1.01  
% 2.43/1.01  prop_solver_calls:                      27
% 2.43/1.01  prop_fast_solver_calls:                 984
% 2.43/1.01  smt_solver_calls:                       0
% 2.43/1.01  smt_fast_solver_calls:                  0
% 2.43/1.01  prop_num_of_clauses:                    978
% 2.43/1.01  prop_preprocess_simplified:             4172
% 2.43/1.01  prop_fo_subsumed:                       48
% 2.43/1.01  prop_solver_time:                       0.
% 2.43/1.01  smt_solver_time:                        0.
% 2.43/1.01  smt_fast_solver_time:                   0.
% 2.43/1.01  prop_fast_solver_time:                  0.
% 2.43/1.01  prop_unsat_core_time:                   0.
% 2.43/1.01  
% 2.43/1.01  ------ QBF
% 2.43/1.01  
% 2.43/1.01  qbf_q_res:                              0
% 2.43/1.01  qbf_num_tautologies:                    0
% 2.43/1.01  qbf_prep_cycles:                        0
% 2.43/1.01  
% 2.43/1.01  ------ BMC1
% 2.43/1.01  
% 2.43/1.01  bmc1_current_bound:                     -1
% 2.43/1.01  bmc1_last_solved_bound:                 -1
% 2.43/1.01  bmc1_unsat_core_size:                   -1
% 2.43/1.01  bmc1_unsat_core_parents_size:           -1
% 2.43/1.01  bmc1_merge_next_fun:                    0
% 2.43/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation
% 2.43/1.01  
% 2.43/1.01  inst_num_of_clauses:                    313
% 2.43/1.01  inst_num_in_passive:                    44
% 2.43/1.01  inst_num_in_active:                     209
% 2.43/1.01  inst_num_in_unprocessed:                60
% 2.43/1.01  inst_num_of_loops:                      220
% 2.43/1.01  inst_num_of_learning_restarts:          0
% 2.43/1.01  inst_num_moves_active_passive:          8
% 2.43/1.01  inst_lit_activity:                      0
% 2.43/1.01  inst_lit_activity_moves:                0
% 2.43/1.01  inst_num_tautologies:                   0
% 2.43/1.01  inst_num_prop_implied:                  0
% 2.43/1.01  inst_num_existing_simplified:           0
% 2.43/1.01  inst_num_eq_res_simplified:             0
% 2.43/1.01  inst_num_child_elim:                    0
% 2.43/1.01  inst_num_of_dismatching_blockings:      26
% 2.43/1.01  inst_num_of_non_proper_insts:           238
% 2.43/1.01  inst_num_of_duplicates:                 0
% 2.43/1.01  inst_inst_num_from_inst_to_res:         0
% 2.43/1.01  inst_dismatching_checking_time:         0.
% 2.43/1.01  
% 2.43/1.01  ------ Resolution
% 2.43/1.01  
% 2.43/1.01  res_num_of_clauses:                     0
% 2.43/1.01  res_num_in_passive:                     0
% 2.43/1.01  res_num_in_active:                      0
% 2.43/1.01  res_num_of_loops:                       135
% 2.43/1.01  res_forward_subset_subsumed:            51
% 2.43/1.01  res_backward_subset_subsumed:           2
% 2.43/1.01  res_forward_subsumed:                   0
% 2.43/1.01  res_backward_subsumed:                  0
% 2.43/1.01  res_forward_subsumption_resolution:     1
% 2.43/1.01  res_backward_subsumption_resolution:    0
% 2.43/1.01  res_clause_to_clause_subsumption:       133
% 2.43/1.01  res_orphan_elimination:                 0
% 2.43/1.01  res_tautology_del:                      44
% 2.43/1.01  res_num_eq_res_simplified:              0
% 2.43/1.01  res_num_sel_changes:                    0
% 2.43/1.01  res_moves_from_active_to_pass:          0
% 2.43/1.01  
% 2.43/1.01  ------ Superposition
% 2.43/1.01  
% 2.43/1.01  sup_time_total:                         0.
% 2.43/1.01  sup_time_generating:                    0.
% 2.43/1.01  sup_time_sim_full:                      0.
% 2.43/1.01  sup_time_sim_immed:                     0.
% 2.43/1.01  
% 2.43/1.01  sup_num_of_clauses:                     70
% 2.43/1.01  sup_num_in_active:                      41
% 2.43/1.01  sup_num_in_passive:                     29
% 2.43/1.01  sup_num_of_loops:                       43
% 2.43/1.01  sup_fw_superposition:                   23
% 2.43/1.01  sup_bw_superposition:                   34
% 2.43/1.01  sup_immediate_simplified:               9
% 2.43/1.01  sup_given_eliminated:                   0
% 2.43/1.01  comparisons_done:                       0
% 2.43/1.01  comparisons_avoided:                    0
% 2.43/1.01  
% 2.43/1.01  ------ Simplifications
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  sim_fw_subset_subsumed:                 2
% 2.43/1.01  sim_bw_subset_subsumed:                 1
% 2.43/1.01  sim_fw_subsumed:                        1
% 2.43/1.01  sim_bw_subsumed:                        0
% 2.43/1.01  sim_fw_subsumption_res:                 0
% 2.43/1.01  sim_bw_subsumption_res:                 0
% 2.43/1.01  sim_tautology_del:                      0
% 2.43/1.01  sim_eq_tautology_del:                   1
% 2.43/1.01  sim_eq_res_simp:                        0
% 2.43/1.01  sim_fw_demodulated:                     0
% 2.43/1.01  sim_bw_demodulated:                     2
% 2.43/1.01  sim_light_normalised:                   6
% 2.43/1.01  sim_joinable_taut:                      0
% 2.43/1.01  sim_joinable_simp:                      0
% 2.43/1.01  sim_ac_normalised:                      0
% 2.43/1.01  sim_smt_subsumption:                    0
% 2.43/1.01  
%------------------------------------------------------------------------------
