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
% DateTime   : Thu Dec  3 12:27:56 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  174 (1513 expanded)
%              Number of clauses        :   88 ( 284 expanded)
%              Number of leaves         :   23 ( 587 expanded)
%              Depth                    :   22
%              Number of atoms          :  723 (15555 expanded)
%              Number of equality atoms :  166 (2910 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))
        & sK5 = X3
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f33,f42,f41,f40,f39,f38])).

fof(f76,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f82])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f83])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f84])).

fof(f66,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK0(X0,X1),X0)
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v3_tex_2(X3,X0)
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f68,plain,(
    v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(definition_unfolding,[],[f75,f77])).

fof(f78,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(definition_unfolding,[],[f78,f77])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f62,plain,(
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

fof(f89,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f74,plain,(
    v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_546,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_770,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_548,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | v1_xboole_0(X1_54)
    | k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_769,plain,
    ( k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54)
    | m1_subset_1(X0_54,X1_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_1250,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_770,c_769])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_406,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_407,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_408,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_10,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_306,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_307,plain,
    ( ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_311,plain,
    ( ~ v3_tex_2(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_26,c_23])).

cnf(c_9,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_140,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_tex_2(X0,X1)
    | v3_tex_2(u1_struct_0(X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5])).

cnf(c_141,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_391,plain,
    ( v3_tex_2(u1_struct_0(X0),X1)
    | ~ v4_tex_2(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_20])).

cnf(c_392,plain,
    ( v3_tex_2(u1_struct_0(sK2),sK1)
    | ~ v4_tex_2(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_21,negated_conjecture,
    ( v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_394,plain,
    ( v3_tex_2(u1_struct_0(sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_26,c_23,c_21])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(X0)
    | u1_struct_0(sK2) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_311,c_394])).

cnf(c_449,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_450,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_880,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_881,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
    | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_880])).

cnf(c_409,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_23])).

cnf(c_543,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_773,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_768,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_xboole_0(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_549])).

cnf(c_1209,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_773,c_768])).

cnf(c_1456,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1250,c_30,c_40,c_408,c_450,c_881,c_1209])).

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
    inference(cnf_transformation,[],[f52])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0_54,X1_54)
    | ~ m1_subset_1(X2_54,X1_54)
    | ~ m1_subset_1(X3_54,X1_54)
    | ~ m1_subset_1(X4_54,X1_54)
    | ~ m1_subset_1(X5_54,X1_54)
    | ~ m1_subset_1(X6_54,X1_54)
    | ~ m1_subset_1(X7_54,X1_54)
    | ~ m1_subset_1(X8_54,X1_54)
    | m1_subset_1(k6_enumset1(X8_54,X7_54,X6_54,X5_54,X4_54,X3_54,X2_54,X0_54),k1_zfmisc_1(X1_54))
    | k1_xboole_0 = X1_54 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_767,plain,
    ( k1_xboole_0 = X0_54
    | m1_subset_1(X1_54,X0_54) != iProver_top
    | m1_subset_1(X2_54,X0_54) != iProver_top
    | m1_subset_1(X3_54,X0_54) != iProver_top
    | m1_subset_1(X4_54,X0_54) != iProver_top
    | m1_subset_1(X5_54,X0_54) != iProver_top
    | m1_subset_1(X6_54,X0_54) != iProver_top
    | m1_subset_1(X7_54,X0_54) != iProver_top
    | m1_subset_1(X8_54,X0_54) != iProver_top
    | m1_subset_1(k6_enumset1(X8_54,X7_54,X6_54,X5_54,X4_54,X3_54,X2_54,X1_54),k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_1459,plain,
    ( k1_xboole_0 = X0_54
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK5),k1_zfmisc_1(X0_54)) = iProver_top
    | m1_subset_1(sK5,X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_767])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_417,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_23])).

cnf(c_423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_422])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_423])).

cnf(c_774,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_1559,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK5),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_774])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_545,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_771,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_1251,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_769])).

cnf(c_883,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_1464,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1251,c_23,c_14,c_407,c_449,c_883])).

cnf(c_1466,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
    inference(light_normalisation,[status(thm)],[c_1464,c_1456])).

cnf(c_12,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_547,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1468,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(demodulation,[status(thm)],[c_1466,c_547])).

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
    inference(cnf_transformation,[],[f89])).

cnf(c_15,negated_conjecture,
    ( v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_281,plain,
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

cnf(c_282,plain,
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
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_24,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(renaming,[status(thm)],[c_286])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_423,c_287])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54) ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_775,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_1558,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
    | u1_struct_0(sK2) = k1_xboole_0
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_775])).

cnf(c_1599,plain,
    ( u1_struct_0(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1559,c_39,c_1468,c_1558])).

cnf(c_451,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_23,c_407])).

cnf(c_540,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_776,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_1607,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1599,c_776])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_70,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1607,c_70])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:12:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.22/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/0.97  
% 2.22/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/0.97  
% 2.22/0.97  ------  iProver source info
% 2.22/0.97  
% 2.22/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.22/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/0.97  git: non_committed_changes: false
% 2.22/0.97  git: last_make_outside_of_git: false
% 2.22/0.97  
% 2.22/0.97  ------ 
% 2.22/0.97  
% 2.22/0.97  ------ Input Options
% 2.22/0.97  
% 2.22/0.97  --out_options                           all
% 2.22/0.97  --tptp_safe_out                         true
% 2.22/0.97  --problem_path                          ""
% 2.22/0.97  --include_path                          ""
% 2.22/0.97  --clausifier                            res/vclausify_rel
% 2.22/0.97  --clausifier_options                    --mode clausify
% 2.22/0.97  --stdin                                 false
% 2.22/0.97  --stats_out                             all
% 2.22/0.97  
% 2.22/0.97  ------ General Options
% 2.22/0.97  
% 2.22/0.97  --fof                                   false
% 2.22/0.97  --time_out_real                         305.
% 2.22/0.97  --time_out_virtual                      -1.
% 2.22/0.97  --symbol_type_check                     false
% 2.22/0.97  --clausify_out                          false
% 2.22/0.97  --sig_cnt_out                           false
% 2.22/0.97  --trig_cnt_out                          false
% 2.22/0.97  --trig_cnt_out_tolerance                1.
% 2.22/0.97  --trig_cnt_out_sk_spl                   false
% 2.22/0.97  --abstr_cl_out                          false
% 2.22/0.97  
% 2.22/0.97  ------ Global Options
% 2.22/0.97  
% 2.22/0.97  --schedule                              default
% 2.22/0.97  --add_important_lit                     false
% 2.22/0.97  --prop_solver_per_cl                    1000
% 2.22/0.97  --min_unsat_core                        false
% 2.22/0.97  --soft_assumptions                      false
% 2.22/0.97  --soft_lemma_size                       3
% 2.22/0.97  --prop_impl_unit_size                   0
% 2.22/0.97  --prop_impl_unit                        []
% 2.22/0.97  --share_sel_clauses                     true
% 2.22/0.97  --reset_solvers                         false
% 2.22/0.97  --bc_imp_inh                            [conj_cone]
% 2.22/0.97  --conj_cone_tolerance                   3.
% 2.22/0.97  --extra_neg_conj                        none
% 2.22/0.97  --large_theory_mode                     true
% 2.22/0.97  --prolific_symb_bound                   200
% 2.22/0.97  --lt_threshold                          2000
% 2.22/0.97  --clause_weak_htbl                      true
% 2.22/0.97  --gc_record_bc_elim                     false
% 2.22/0.97  
% 2.22/0.97  ------ Preprocessing Options
% 2.22/0.97  
% 2.22/0.97  --preprocessing_flag                    true
% 2.22/0.97  --time_out_prep_mult                    0.1
% 2.22/0.97  --splitting_mode                        input
% 2.22/0.97  --splitting_grd                         true
% 2.22/0.97  --splitting_cvd                         false
% 2.22/0.97  --splitting_cvd_svl                     false
% 2.22/0.97  --splitting_nvd                         32
% 2.22/0.97  --sub_typing                            true
% 2.22/0.97  --prep_gs_sim                           true
% 2.22/0.97  --prep_unflatten                        true
% 2.22/0.97  --prep_res_sim                          true
% 2.22/0.97  --prep_upred                            true
% 2.22/0.97  --prep_sem_filter                       exhaustive
% 2.22/0.97  --prep_sem_filter_out                   false
% 2.22/0.97  --pred_elim                             true
% 2.22/0.97  --res_sim_input                         true
% 2.22/0.97  --eq_ax_congr_red                       true
% 2.22/0.97  --pure_diseq_elim                       true
% 2.22/0.97  --brand_transform                       false
% 2.22/0.97  --non_eq_to_eq                          false
% 2.22/0.97  --prep_def_merge                        true
% 2.22/0.97  --prep_def_merge_prop_impl              false
% 2.22/0.97  --prep_def_merge_mbd                    true
% 2.22/0.97  --prep_def_merge_tr_red                 false
% 2.22/0.97  --prep_def_merge_tr_cl                  false
% 2.22/0.97  --smt_preprocessing                     true
% 2.22/0.97  --smt_ac_axioms                         fast
% 2.22/0.97  --preprocessed_out                      false
% 2.22/0.97  --preprocessed_stats                    false
% 2.22/0.97  
% 2.22/0.97  ------ Abstraction refinement Options
% 2.22/0.97  
% 2.22/0.97  --abstr_ref                             []
% 2.22/0.97  --abstr_ref_prep                        false
% 2.22/0.97  --abstr_ref_until_sat                   false
% 2.22/0.97  --abstr_ref_sig_restrict                funpre
% 2.22/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.97  --abstr_ref_under                       []
% 2.22/0.97  
% 2.22/0.97  ------ SAT Options
% 2.22/0.97  
% 2.22/0.97  --sat_mode                              false
% 2.22/0.97  --sat_fm_restart_options                ""
% 2.22/0.97  --sat_gr_def                            false
% 2.22/0.97  --sat_epr_types                         true
% 2.22/0.97  --sat_non_cyclic_types                  false
% 2.22/0.97  --sat_finite_models                     false
% 2.22/0.97  --sat_fm_lemmas                         false
% 2.22/0.97  --sat_fm_prep                           false
% 2.22/0.97  --sat_fm_uc_incr                        true
% 2.22/0.97  --sat_out_model                         small
% 2.22/0.97  --sat_out_clauses                       false
% 2.22/0.97  
% 2.22/0.97  ------ QBF Options
% 2.22/0.97  
% 2.22/0.97  --qbf_mode                              false
% 2.22/0.97  --qbf_elim_univ                         false
% 2.22/0.97  --qbf_dom_inst                          none
% 2.22/0.97  --qbf_dom_pre_inst                      false
% 2.22/0.97  --qbf_sk_in                             false
% 2.22/0.97  --qbf_pred_elim                         true
% 2.22/0.97  --qbf_split                             512
% 2.22/0.97  
% 2.22/0.97  ------ BMC1 Options
% 2.22/0.97  
% 2.22/0.97  --bmc1_incremental                      false
% 2.22/0.97  --bmc1_axioms                           reachable_all
% 2.22/0.97  --bmc1_min_bound                        0
% 2.22/0.97  --bmc1_max_bound                        -1
% 2.22/0.97  --bmc1_max_bound_default                -1
% 2.22/0.97  --bmc1_symbol_reachability              true
% 2.22/0.97  --bmc1_property_lemmas                  false
% 2.22/0.97  --bmc1_k_induction                      false
% 2.22/0.97  --bmc1_non_equiv_states                 false
% 2.22/0.97  --bmc1_deadlock                         false
% 2.22/0.97  --bmc1_ucm                              false
% 2.22/0.97  --bmc1_add_unsat_core                   none
% 2.22/0.97  --bmc1_unsat_core_children              false
% 2.22/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.97  --bmc1_out_stat                         full
% 2.22/0.97  --bmc1_ground_init                      false
% 2.22/0.97  --bmc1_pre_inst_next_state              false
% 2.22/0.97  --bmc1_pre_inst_state                   false
% 2.22/0.97  --bmc1_pre_inst_reach_state             false
% 2.22/0.97  --bmc1_out_unsat_core                   false
% 2.22/0.97  --bmc1_aig_witness_out                  false
% 2.22/0.97  --bmc1_verbose                          false
% 2.22/0.97  --bmc1_dump_clauses_tptp                false
% 2.22/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.97  --bmc1_dump_file                        -
% 2.22/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.97  --bmc1_ucm_extend_mode                  1
% 2.22/0.97  --bmc1_ucm_init_mode                    2
% 2.22/0.97  --bmc1_ucm_cone_mode                    none
% 2.22/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.97  --bmc1_ucm_relax_model                  4
% 2.22/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.97  --bmc1_ucm_layered_model                none
% 2.22/0.97  --bmc1_ucm_max_lemma_size               10
% 2.22/0.97  
% 2.22/0.97  ------ AIG Options
% 2.22/0.97  
% 2.22/0.97  --aig_mode                              false
% 2.22/0.97  
% 2.22/0.97  ------ Instantiation Options
% 2.22/0.97  
% 2.22/0.97  --instantiation_flag                    true
% 2.22/0.97  --inst_sos_flag                         false
% 2.22/0.97  --inst_sos_phase                        true
% 2.22/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.97  --inst_lit_sel_side                     num_symb
% 2.22/0.97  --inst_solver_per_active                1400
% 2.22/0.97  --inst_solver_calls_frac                1.
% 2.22/0.97  --inst_passive_queue_type               priority_queues
% 2.22/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.97  --inst_passive_queues_freq              [25;2]
% 2.22/0.97  --inst_dismatching                      true
% 2.22/0.97  --inst_eager_unprocessed_to_passive     true
% 2.22/0.97  --inst_prop_sim_given                   true
% 2.22/0.97  --inst_prop_sim_new                     false
% 2.22/0.97  --inst_subs_new                         false
% 2.22/0.97  --inst_eq_res_simp                      false
% 2.22/0.97  --inst_subs_given                       false
% 2.22/0.97  --inst_orphan_elimination               true
% 2.22/0.97  --inst_learning_loop_flag               true
% 2.22/0.97  --inst_learning_start                   3000
% 2.22/0.97  --inst_learning_factor                  2
% 2.22/0.97  --inst_start_prop_sim_after_learn       3
% 2.22/0.97  --inst_sel_renew                        solver
% 2.22/0.97  --inst_lit_activity_flag                true
% 2.22/0.97  --inst_restr_to_given                   false
% 2.22/0.97  --inst_activity_threshold               500
% 2.22/0.97  --inst_out_proof                        true
% 2.22/0.97  
% 2.22/0.97  ------ Resolution Options
% 2.22/0.97  
% 2.22/0.97  --resolution_flag                       true
% 2.22/0.97  --res_lit_sel                           adaptive
% 2.22/0.97  --res_lit_sel_side                      none
% 2.22/0.97  --res_ordering                          kbo
% 2.22/0.97  --res_to_prop_solver                    active
% 2.22/0.97  --res_prop_simpl_new                    false
% 2.22/0.97  --res_prop_simpl_given                  true
% 2.22/0.97  --res_passive_queue_type                priority_queues
% 2.22/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.97  --res_passive_queues_freq               [15;5]
% 2.22/0.97  --res_forward_subs                      full
% 2.22/0.97  --res_backward_subs                     full
% 2.22/0.97  --res_forward_subs_resolution           true
% 2.22/0.97  --res_backward_subs_resolution          true
% 2.22/0.97  --res_orphan_elimination                true
% 2.22/0.97  --res_time_limit                        2.
% 2.22/0.97  --res_out_proof                         true
% 2.22/0.97  
% 2.22/0.97  ------ Superposition Options
% 2.22/0.97  
% 2.22/0.97  --superposition_flag                    true
% 2.22/0.97  --sup_passive_queue_type                priority_queues
% 2.22/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.97  --demod_completeness_check              fast
% 2.22/0.97  --demod_use_ground                      true
% 2.22/0.97  --sup_to_prop_solver                    passive
% 2.22/0.97  --sup_prop_simpl_new                    true
% 2.22/0.97  --sup_prop_simpl_given                  true
% 2.22/0.97  --sup_fun_splitting                     false
% 2.22/0.97  --sup_smt_interval                      50000
% 2.22/0.97  
% 2.22/0.97  ------ Superposition Simplification Setup
% 2.22/0.97  
% 2.22/0.97  --sup_indices_passive                   []
% 2.22/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.97  --sup_full_bw                           [BwDemod]
% 2.22/0.97  --sup_immed_triv                        [TrivRules]
% 2.22/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.97  --sup_immed_bw_main                     []
% 2.22/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.97  
% 2.22/0.97  ------ Combination Options
% 2.22/0.97  
% 2.22/0.97  --comb_res_mult                         3
% 2.22/0.97  --comb_sup_mult                         2
% 2.22/0.97  --comb_inst_mult                        10
% 2.22/0.97  
% 2.22/0.97  ------ Debug Options
% 2.22/0.97  
% 2.22/0.97  --dbg_backtrace                         false
% 2.22/0.97  --dbg_dump_prop_clauses                 false
% 2.22/0.97  --dbg_dump_prop_clauses_file            -
% 2.22/0.97  --dbg_out_stat                          false
% 2.22/0.97  ------ Parsing...
% 2.22/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/0.97  
% 2.22/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 2.22/0.97  
% 2.22/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/0.97  
% 2.22/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/0.97  ------ Proving...
% 2.22/0.97  ------ Problem Properties 
% 2.22/0.97  
% 2.22/0.97  
% 2.22/0.97  clauses                                 12
% 2.22/0.97  conjectures                             4
% 2.22/0.97  EPR                                     1
% 2.22/0.97  Horn                                    10
% 2.22/0.97  unary                                   7
% 2.22/0.97  binary                                  2
% 2.22/0.97  lits                                    27
% 2.22/0.97  lits eq                                 4
% 2.22/0.97  fd_pure                                 0
% 2.22/0.97  fd_pseudo                               0
% 2.22/0.97  fd_cond                                 1
% 2.22/0.97  fd_pseudo_cond                          0
% 2.22/0.97  AC symbols                              0
% 2.22/0.97  
% 2.22/0.97  ------ Schedule dynamic 5 is on 
% 2.22/0.97  
% 2.22/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/0.97  
% 2.22/0.97  
% 2.22/0.97  ------ 
% 2.22/0.97  Current options:
% 2.22/0.97  ------ 
% 2.22/0.97  
% 2.22/0.97  ------ Input Options
% 2.22/0.97  
% 2.22/0.97  --out_options                           all
% 2.22/0.97  --tptp_safe_out                         true
% 2.22/0.97  --problem_path                          ""
% 2.22/0.97  --include_path                          ""
% 2.22/0.97  --clausifier                            res/vclausify_rel
% 2.22/0.97  --clausifier_options                    --mode clausify
% 2.22/0.97  --stdin                                 false
% 2.22/0.97  --stats_out                             all
% 2.22/0.97  
% 2.22/0.97  ------ General Options
% 2.22/0.97  
% 2.22/0.97  --fof                                   false
% 2.22/0.97  --time_out_real                         305.
% 2.22/0.97  --time_out_virtual                      -1.
% 2.22/0.97  --symbol_type_check                     false
% 2.22/0.97  --clausify_out                          false
% 2.22/0.97  --sig_cnt_out                           false
% 2.22/0.97  --trig_cnt_out                          false
% 2.22/0.97  --trig_cnt_out_tolerance                1.
% 2.22/0.97  --trig_cnt_out_sk_spl                   false
% 2.22/0.97  --abstr_cl_out                          false
% 2.22/0.97  
% 2.22/0.97  ------ Global Options
% 2.22/0.97  
% 2.22/0.97  --schedule                              default
% 2.22/0.97  --add_important_lit                     false
% 2.22/0.97  --prop_solver_per_cl                    1000
% 2.22/0.97  --min_unsat_core                        false
% 2.22/0.97  --soft_assumptions                      false
% 2.22/0.97  --soft_lemma_size                       3
% 2.22/0.97  --prop_impl_unit_size                   0
% 2.22/0.97  --prop_impl_unit                        []
% 2.22/0.97  --share_sel_clauses                     true
% 2.22/0.97  --reset_solvers                         false
% 2.22/0.97  --bc_imp_inh                            [conj_cone]
% 2.22/0.97  --conj_cone_tolerance                   3.
% 2.22/0.97  --extra_neg_conj                        none
% 2.22/0.97  --large_theory_mode                     true
% 2.22/0.97  --prolific_symb_bound                   200
% 2.22/0.97  --lt_threshold                          2000
% 2.22/0.97  --clause_weak_htbl                      true
% 2.22/0.97  --gc_record_bc_elim                     false
% 2.22/0.97  
% 2.22/0.97  ------ Preprocessing Options
% 2.22/0.97  
% 2.22/0.97  --preprocessing_flag                    true
% 2.22/0.97  --time_out_prep_mult                    0.1
% 2.22/0.97  --splitting_mode                        input
% 2.22/0.97  --splitting_grd                         true
% 2.22/0.97  --splitting_cvd                         false
% 2.22/0.97  --splitting_cvd_svl                     false
% 2.22/0.97  --splitting_nvd                         32
% 2.22/0.97  --sub_typing                            true
% 2.22/0.97  --prep_gs_sim                           true
% 2.22/0.97  --prep_unflatten                        true
% 2.22/0.97  --prep_res_sim                          true
% 2.22/0.97  --prep_upred                            true
% 2.22/0.97  --prep_sem_filter                       exhaustive
% 2.22/0.97  --prep_sem_filter_out                   false
% 2.22/0.97  --pred_elim                             true
% 2.22/0.97  --res_sim_input                         true
% 2.22/0.97  --eq_ax_congr_red                       true
% 2.22/0.97  --pure_diseq_elim                       true
% 2.22/0.97  --brand_transform                       false
% 2.22/0.97  --non_eq_to_eq                          false
% 2.22/0.97  --prep_def_merge                        true
% 2.22/0.97  --prep_def_merge_prop_impl              false
% 2.22/0.97  --prep_def_merge_mbd                    true
% 2.22/0.97  --prep_def_merge_tr_red                 false
% 2.22/0.97  --prep_def_merge_tr_cl                  false
% 2.22/0.97  --smt_preprocessing                     true
% 2.22/0.97  --smt_ac_axioms                         fast
% 2.22/0.97  --preprocessed_out                      false
% 2.22/0.97  --preprocessed_stats                    false
% 2.22/0.97  
% 2.22/0.97  ------ Abstraction refinement Options
% 2.22/0.97  
% 2.22/0.97  --abstr_ref                             []
% 2.22/0.97  --abstr_ref_prep                        false
% 2.22/0.97  --abstr_ref_until_sat                   false
% 2.22/0.97  --abstr_ref_sig_restrict                funpre
% 2.22/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.97  --abstr_ref_under                       []
% 2.22/0.97  
% 2.22/0.97  ------ SAT Options
% 2.22/0.97  
% 2.22/0.97  --sat_mode                              false
% 2.22/0.97  --sat_fm_restart_options                ""
% 2.22/0.97  --sat_gr_def                            false
% 2.22/0.97  --sat_epr_types                         true
% 2.22/0.97  --sat_non_cyclic_types                  false
% 2.22/0.97  --sat_finite_models                     false
% 2.22/0.97  --sat_fm_lemmas                         false
% 2.22/0.97  --sat_fm_prep                           false
% 2.22/0.97  --sat_fm_uc_incr                        true
% 2.22/0.97  --sat_out_model                         small
% 2.22/0.97  --sat_out_clauses                       false
% 2.22/0.97  
% 2.22/0.97  ------ QBF Options
% 2.22/0.97  
% 2.22/0.97  --qbf_mode                              false
% 2.22/0.97  --qbf_elim_univ                         false
% 2.22/0.97  --qbf_dom_inst                          none
% 2.22/0.97  --qbf_dom_pre_inst                      false
% 2.22/0.97  --qbf_sk_in                             false
% 2.22/0.97  --qbf_pred_elim                         true
% 2.22/0.97  --qbf_split                             512
% 2.22/0.97  
% 2.22/0.97  ------ BMC1 Options
% 2.22/0.97  
% 2.22/0.97  --bmc1_incremental                      false
% 2.22/0.97  --bmc1_axioms                           reachable_all
% 2.22/0.97  --bmc1_min_bound                        0
% 2.22/0.97  --bmc1_max_bound                        -1
% 2.22/0.97  --bmc1_max_bound_default                -1
% 2.22/0.97  --bmc1_symbol_reachability              true
% 2.22/0.97  --bmc1_property_lemmas                  false
% 2.22/0.97  --bmc1_k_induction                      false
% 2.22/0.97  --bmc1_non_equiv_states                 false
% 2.22/0.97  --bmc1_deadlock                         false
% 2.22/0.97  --bmc1_ucm                              false
% 2.22/0.97  --bmc1_add_unsat_core                   none
% 2.22/0.97  --bmc1_unsat_core_children              false
% 2.22/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.97  --bmc1_out_stat                         full
% 2.22/0.97  --bmc1_ground_init                      false
% 2.22/0.97  --bmc1_pre_inst_next_state              false
% 2.22/0.97  --bmc1_pre_inst_state                   false
% 2.22/0.97  --bmc1_pre_inst_reach_state             false
% 2.22/0.97  --bmc1_out_unsat_core                   false
% 2.22/0.97  --bmc1_aig_witness_out                  false
% 2.22/0.97  --bmc1_verbose                          false
% 2.22/0.97  --bmc1_dump_clauses_tptp                false
% 2.22/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.97  --bmc1_dump_file                        -
% 2.22/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.97  --bmc1_ucm_extend_mode                  1
% 2.22/0.97  --bmc1_ucm_init_mode                    2
% 2.22/0.97  --bmc1_ucm_cone_mode                    none
% 2.22/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.97  --bmc1_ucm_relax_model                  4
% 2.22/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.97  --bmc1_ucm_layered_model                none
% 2.22/0.97  --bmc1_ucm_max_lemma_size               10
% 2.22/0.97  
% 2.22/0.97  ------ AIG Options
% 2.22/0.97  
% 2.22/0.97  --aig_mode                              false
% 2.22/0.97  
% 2.22/0.97  ------ Instantiation Options
% 2.22/0.97  
% 2.22/0.97  --instantiation_flag                    true
% 2.22/0.97  --inst_sos_flag                         false
% 2.22/0.97  --inst_sos_phase                        true
% 2.22/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.97  --inst_lit_sel_side                     none
% 2.22/0.97  --inst_solver_per_active                1400
% 2.22/0.97  --inst_solver_calls_frac                1.
% 2.22/0.97  --inst_passive_queue_type               priority_queues
% 2.22/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.97  --inst_passive_queues_freq              [25;2]
% 2.22/0.97  --inst_dismatching                      true
% 2.22/0.97  --inst_eager_unprocessed_to_passive     true
% 2.22/0.97  --inst_prop_sim_given                   true
% 2.22/0.97  --inst_prop_sim_new                     false
% 2.22/0.97  --inst_subs_new                         false
% 2.22/0.97  --inst_eq_res_simp                      false
% 2.22/0.97  --inst_subs_given                       false
% 2.22/0.97  --inst_orphan_elimination               true
% 2.22/0.97  --inst_learning_loop_flag               true
% 2.22/0.97  --inst_learning_start                   3000
% 2.22/0.97  --inst_learning_factor                  2
% 2.22/0.97  --inst_start_prop_sim_after_learn       3
% 2.22/0.97  --inst_sel_renew                        solver
% 2.22/0.97  --inst_lit_activity_flag                true
% 2.22/0.97  --inst_restr_to_given                   false
% 2.22/0.97  --inst_activity_threshold               500
% 2.22/0.97  --inst_out_proof                        true
% 2.22/0.97  
% 2.22/0.97  ------ Resolution Options
% 2.22/0.97  
% 2.22/0.97  --resolution_flag                       false
% 2.22/0.97  --res_lit_sel                           adaptive
% 2.22/0.97  --res_lit_sel_side                      none
% 2.22/0.97  --res_ordering                          kbo
% 2.22/0.97  --res_to_prop_solver                    active
% 2.22/0.97  --res_prop_simpl_new                    false
% 2.22/0.97  --res_prop_simpl_given                  true
% 2.22/0.97  --res_passive_queue_type                priority_queues
% 2.22/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.97  --res_passive_queues_freq               [15;5]
% 2.22/0.97  --res_forward_subs                      full
% 2.22/0.97  --res_backward_subs                     full
% 2.22/0.97  --res_forward_subs_resolution           true
% 2.22/0.97  --res_backward_subs_resolution          true
% 2.22/0.97  --res_orphan_elimination                true
% 2.22/0.97  --res_time_limit                        2.
% 2.22/0.97  --res_out_proof                         true
% 2.22/0.97  
% 2.22/0.97  ------ Superposition Options
% 2.22/0.97  
% 2.22/0.97  --superposition_flag                    true
% 2.22/0.97  --sup_passive_queue_type                priority_queues
% 2.22/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.97  --demod_completeness_check              fast
% 2.22/0.97  --demod_use_ground                      true
% 2.22/0.97  --sup_to_prop_solver                    passive
% 2.22/0.97  --sup_prop_simpl_new                    true
% 2.22/0.97  --sup_prop_simpl_given                  true
% 2.22/0.97  --sup_fun_splitting                     false
% 2.22/0.97  --sup_smt_interval                      50000
% 2.22/0.97  
% 2.22/0.97  ------ Superposition Simplification Setup
% 2.22/0.97  
% 2.22/0.97  --sup_indices_passive                   []
% 2.22/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.97  --sup_full_bw                           [BwDemod]
% 2.22/0.97  --sup_immed_triv                        [TrivRules]
% 2.22/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.97  --sup_immed_bw_main                     []
% 2.22/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.97  
% 2.22/0.97  ------ Combination Options
% 2.22/0.97  
% 2.22/0.97  --comb_res_mult                         3
% 2.22/0.97  --comb_sup_mult                         2
% 2.22/0.97  --comb_inst_mult                        10
% 2.22/0.97  
% 2.22/0.97  ------ Debug Options
% 2.22/0.97  
% 2.22/0.97  --dbg_backtrace                         false
% 2.22/0.97  --dbg_dump_prop_clauses                 false
% 2.22/0.97  --dbg_dump_prop_clauses_file            -
% 2.22/0.97  --dbg_out_stat                          false
% 2.22/0.97  
% 2.22/0.97  
% 2.22/0.97  
% 2.22/0.97  
% 2.22/0.97  ------ Proving...
% 2.22/0.97  
% 2.22/0.97  
% 2.22/0.97  % SZS status Theorem for theBenchmark.p
% 2.22/0.97  
% 2.22/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/0.97  
% 2.22/0.97  fof(f17,conjecture,(
% 2.22/0.97    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f18,negated_conjecture,(
% 2.22/0.97    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 2.22/0.97    inference(negated_conjecture,[],[f17])).
% 2.22/0.97  
% 2.22/0.97  fof(f32,plain,(
% 2.22/0.97    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.22/0.97    inference(ennf_transformation,[],[f18])).
% 2.22/0.97  
% 2.22/0.97  fof(f33,plain,(
% 2.22/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.97    inference(flattening,[],[f32])).
% 2.22/0.97  
% 2.22/0.97  fof(f42,plain,(
% 2.22/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) & sK5 = X3 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.22/0.97    introduced(choice_axiom,[])).
% 2.22/0.97  
% 2.22/0.97  fof(f41,plain,(
% 2.22/0.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK4 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 2.22/0.97    introduced(choice_axiom,[])).
% 2.22/0.97  
% 2.22/0.97  fof(f40,plain,(
% 2.22/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK3,X0,X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK3,X0,X1) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 2.22/0.97    introduced(choice_axiom,[])).
% 2.22/0.97  
% 2.22/0.97  fof(f39,plain,(
% 2.22/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(X2,X0,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v5_pre_topc(X2,X0,sK2) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & v4_tex_2(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.22/0.97    introduced(choice_axiom,[])).
% 2.22/0.97  
% 2.22/0.97  fof(f38,plain,(
% 2.22/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X2,sK1,X1) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & v4_tex_2(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.22/0.97    introduced(choice_axiom,[])).
% 2.22/0.97  
% 2.22/0.97  fof(f43,plain,(
% 2.22/0.97    ((((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2))) & v3_borsuk_1(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & v4_tex_2(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.22/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f33,f42,f41,f40,f39,f38])).
% 2.22/0.97  
% 2.22/0.97  fof(f76,plain,(
% 2.22/0.97    m1_subset_1(sK5,u1_struct_0(sK1))),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f12,axiom,(
% 2.22/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f23,plain,(
% 2.22/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.22/0.97    inference(ennf_transformation,[],[f12])).
% 2.22/0.97  
% 2.22/0.97  fof(f24,plain,(
% 2.22/0.97    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.22/0.97    inference(flattening,[],[f23])).
% 2.22/0.97  
% 2.22/0.97  fof(f55,plain,(
% 2.22/0.97    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f24])).
% 2.22/0.97  
% 2.22/0.97  fof(f2,axiom,(
% 2.22/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f45,plain,(
% 2.22/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f2])).
% 2.22/0.97  
% 2.22/0.97  fof(f3,axiom,(
% 2.22/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f46,plain,(
% 2.22/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f3])).
% 2.22/0.97  
% 2.22/0.97  fof(f4,axiom,(
% 2.22/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f47,plain,(
% 2.22/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f4])).
% 2.22/0.97  
% 2.22/0.97  fof(f5,axiom,(
% 2.22/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f48,plain,(
% 2.22/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f5])).
% 2.22/0.97  
% 2.22/0.97  fof(f6,axiom,(
% 2.22/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f49,plain,(
% 2.22/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f6])).
% 2.22/0.97  
% 2.22/0.97  fof(f7,axiom,(
% 2.22/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f50,plain,(
% 2.22/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f7])).
% 2.22/0.97  
% 2.22/0.97  fof(f8,axiom,(
% 2.22/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f51,plain,(
% 2.22/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f8])).
% 2.22/0.97  
% 2.22/0.97  fof(f79,plain,(
% 2.22/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.22/0.97    inference(definition_unfolding,[],[f50,f51])).
% 2.22/0.97  
% 2.22/0.97  fof(f80,plain,(
% 2.22/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.22/0.97    inference(definition_unfolding,[],[f49,f79])).
% 2.22/0.97  
% 2.22/0.97  fof(f81,plain,(
% 2.22/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.22/0.97    inference(definition_unfolding,[],[f48,f80])).
% 2.22/0.97  
% 2.22/0.97  fof(f82,plain,(
% 2.22/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.22/0.97    inference(definition_unfolding,[],[f47,f81])).
% 2.22/0.97  
% 2.22/0.97  fof(f83,plain,(
% 2.22/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.22/0.97    inference(definition_unfolding,[],[f46,f82])).
% 2.22/0.97  
% 2.22/0.97  fof(f84,plain,(
% 2.22/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.22/0.97    inference(definition_unfolding,[],[f45,f83])).
% 2.22/0.97  
% 2.22/0.97  fof(f85,plain,(
% 2.22/0.97    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.22/0.97    inference(definition_unfolding,[],[f55,f84])).
% 2.22/0.97  
% 2.22/0.97  fof(f66,plain,(
% 2.22/0.97    l1_pre_topc(sK1)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f13,axiom,(
% 2.22/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f25,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/0.97    inference(ennf_transformation,[],[f13])).
% 2.22/0.97  
% 2.22/0.97  fof(f56,plain,(
% 2.22/0.97    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f25])).
% 2.22/0.97  
% 2.22/0.97  fof(f69,plain,(
% 2.22/0.97    m1_pre_topc(sK2,sK1)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f15,axiom,(
% 2.22/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f28,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.97    inference(ennf_transformation,[],[f15])).
% 2.22/0.97  
% 2.22/0.97  fof(f29,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.97    inference(flattening,[],[f28])).
% 2.22/0.97  
% 2.22/0.97  fof(f61,plain,(
% 2.22/0.97    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f29])).
% 2.22/0.97  
% 2.22/0.97  fof(f64,plain,(
% 2.22/0.97    v2_pre_topc(sK1)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f63,plain,(
% 2.22/0.97    ~v2_struct_0(sK1)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f14,axiom,(
% 2.22/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f26,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.97    inference(ennf_transformation,[],[f14])).
% 2.22/0.97  
% 2.22/0.97  fof(f27,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.97    inference(flattening,[],[f26])).
% 2.22/0.97  
% 2.22/0.97  fof(f34,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.97    inference(nnf_transformation,[],[f27])).
% 2.22/0.97  
% 2.22/0.97  fof(f35,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.97    inference(rectify,[],[f34])).
% 2.22/0.97  
% 2.22/0.97  fof(f36,plain,(
% 2.22/0.97    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/0.97    introduced(choice_axiom,[])).
% 2.22/0.97  
% 2.22/0.97  fof(f37,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.22/0.97  
% 2.22/0.97  fof(f57,plain,(
% 2.22/0.97    ( ! [X0,X3,X1] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f37])).
% 2.22/0.97  
% 2.22/0.97  fof(f88,plain,(
% 2.22/0.97    ( ! [X0,X1] : (v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.97    inference(equality_resolution,[],[f57])).
% 2.22/0.97  
% 2.22/0.97  fof(f68,plain,(
% 2.22/0.97    v4_tex_2(sK2,sK1)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f10,axiom,(
% 2.22/0.97    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f21,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.22/0.97    inference(ennf_transformation,[],[f10])).
% 2.22/0.97  
% 2.22/0.97  fof(f53,plain,(
% 2.22/0.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f21])).
% 2.22/0.97  
% 2.22/0.97  fof(f9,axiom,(
% 2.22/0.97    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : (m1_subset_1(X3,X0) => ! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X0) => ! [X8] : (m1_subset_1(X8,X0) => (k1_xboole_0 != X0 => m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)))))))))))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f19,plain,(
% 2.22/0.97    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (! [X8] : ((m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X8,X0)) | ~m1_subset_1(X7,X0)) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 2.22/0.97    inference(ennf_transformation,[],[f9])).
% 2.22/0.97  
% 2.22/0.97  fof(f20,plain,(
% 2.22/0.97    ! [X0,X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (! [X7] : (! [X8] : (m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X8,X0)) | ~m1_subset_1(X7,X0)) | ~m1_subset_1(X6,X0)) | ~m1_subset_1(X5,X0)) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,X0))),
% 2.22/0.97    inference(flattening,[],[f19])).
% 2.22/0.97  
% 2.22/0.97  fof(f52,plain,(
% 2.22/0.97    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X8,X0) | ~m1_subset_1(X7,X0) | ~m1_subset_1(X6,X0) | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f20])).
% 2.22/0.97  
% 2.22/0.97  fof(f11,axiom,(
% 2.22/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f22,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.22/0.97    inference(ennf_transformation,[],[f11])).
% 2.22/0.97  
% 2.22/0.97  fof(f54,plain,(
% 2.22/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f22])).
% 2.22/0.97  
% 2.22/0.97  fof(f75,plain,(
% 2.22/0.97    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f77,plain,(
% 2.22/0.97    sK4 = sK5),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f87,plain,(
% 2.22/0.97    m1_subset_1(sK5,u1_struct_0(sK2))),
% 2.22/0.97    inference(definition_unfolding,[],[f75,f77])).
% 2.22/0.97  
% 2.22/0.97  fof(f78,plain,(
% 2.22/0.97    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f86,plain,(
% 2.22/0.97    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 2.22/0.97    inference(definition_unfolding,[],[f78,f77])).
% 2.22/0.97  
% 2.22/0.97  fof(f16,axiom,(
% 2.22/0.97    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f30,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.97    inference(ennf_transformation,[],[f16])).
% 2.22/0.97  
% 2.22/0.97  fof(f31,plain,(
% 2.22/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.97    inference(flattening,[],[f30])).
% 2.22/0.97  
% 2.22/0.97  fof(f62,plain,(
% 2.22/0.97    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.97    inference(cnf_transformation,[],[f31])).
% 2.22/0.97  
% 2.22/0.97  fof(f89,plain,(
% 2.22/0.97    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.97    inference(equality_resolution,[],[f62])).
% 2.22/0.97  
% 2.22/0.97  fof(f74,plain,(
% 2.22/0.97    v3_borsuk_1(sK3,sK1,sK2)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f65,plain,(
% 2.22/0.97    v3_tdlat_3(sK1)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f67,plain,(
% 2.22/0.97    ~v2_struct_0(sK2)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f70,plain,(
% 2.22/0.97    v1_funct_1(sK3)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f71,plain,(
% 2.22/0.97    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f72,plain,(
% 2.22/0.97    v5_pre_topc(sK3,sK1,sK2)),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f73,plain,(
% 2.22/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 2.22/0.97    inference(cnf_transformation,[],[f43])).
% 2.22/0.97  
% 2.22/0.97  fof(f1,axiom,(
% 2.22/0.97    v1_xboole_0(k1_xboole_0)),
% 2.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.97  
% 2.22/0.97  fof(f44,plain,(
% 2.22/0.97    v1_xboole_0(k1_xboole_0)),
% 2.22/0.97    inference(cnf_transformation,[],[f1])).
% 2.22/0.97  
% 2.22/0.97  cnf(c_13,negated_conjecture,
% 2.22/0.97      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 2.22/0.97      inference(cnf_transformation,[],[f76]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_546,negated_conjecture,
% 2.22/0.97      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 2.22/0.97      inference(subtyping,[status(esa)],[c_13]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_770,plain,
% 2.22/0.97      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.22/0.97      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_4,plain,
% 2.22/0.97      ( ~ m1_subset_1(X0,X1)
% 2.22/0.97      | v1_xboole_0(X1)
% 2.22/0.97      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.22/0.97      inference(cnf_transformation,[],[f85]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_548,plain,
% 2.22/0.97      ( ~ m1_subset_1(X0_54,X1_54)
% 2.22/0.97      | v1_xboole_0(X1_54)
% 2.22/0.97      | k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54) ),
% 2.22/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_769,plain,
% 2.22/0.97      ( k6_enumset1(X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54,X0_54) = k6_domain_1(X1_54,X0_54)
% 2.22/0.97      | m1_subset_1(X0_54,X1_54) != iProver_top
% 2.22/0.97      | v1_xboole_0(X1_54) = iProver_top ),
% 2.22/0.97      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_1250,plain,
% 2.22/0.97      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
% 2.22/0.97      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.22/0.97      inference(superposition,[status(thm)],[c_770,c_769]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_23,negated_conjecture,
% 2.22/0.97      ( l1_pre_topc(sK1) ),
% 2.22/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_30,plain,
% 2.22/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 2.22/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_40,plain,
% 2.22/0.97      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 2.22/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_5,plain,
% 2.22/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.22/0.97      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.97      | ~ l1_pre_topc(X1) ),
% 2.22/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_20,negated_conjecture,
% 2.22/0.97      ( m1_pre_topc(sK2,sK1) ),
% 2.22/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_406,plain,
% 2.22/0.97      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.97      | ~ l1_pre_topc(X1)
% 2.22/0.97      | sK2 != X0
% 2.22/0.97      | sK1 != X1 ),
% 2.22/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_20]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_407,plain,
% 2.22/0.97      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.97      | ~ l1_pre_topc(sK1) ),
% 2.22/0.97      inference(unflattening,[status(thm)],[c_406]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_408,plain,
% 2.22/0.97      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.22/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 2.22/0.97      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_10,plain,
% 2.22/0.97      ( ~ v3_tex_2(X0,X1)
% 2.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.97      | ~ v2_pre_topc(X1)
% 2.22/0.97      | v2_struct_0(X1)
% 2.22/0.97      | ~ l1_pre_topc(X1)
% 2.22/0.97      | ~ v1_xboole_0(X0) ),
% 2.22/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_25,negated_conjecture,
% 2.22/0.97      ( v2_pre_topc(sK1) ),
% 2.22/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.22/0.97  
% 2.22/0.97  cnf(c_306,plain,
% 2.22/0.97      ( ~ v3_tex_2(X0,X1)
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | ~ l1_pre_topc(X1)
% 2.22/0.98      | ~ v1_xboole_0(X0)
% 2.22/0.98      | sK1 != X1 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_307,plain,
% 2.22/0.98      ( ~ v3_tex_2(X0,sK1)
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | v2_struct_0(sK1)
% 2.22/0.98      | ~ l1_pre_topc(sK1)
% 2.22/0.98      | ~ v1_xboole_0(X0) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_26,negated_conjecture,
% 2.22/0.98      ( ~ v2_struct_0(sK1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_311,plain,
% 2.22/0.98      ( ~ v3_tex_2(X0,sK1)
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | ~ v1_xboole_0(X0) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_307,c_26,c_23]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_9,plain,
% 2.22/0.98      ( v3_tex_2(u1_struct_0(X0),X1)
% 2.22/0.98      | ~ v4_tex_2(X0,X1)
% 2.22/0.98      | ~ m1_pre_topc(X0,X1)
% 2.22/0.98      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | ~ l1_pre_topc(X1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_140,plain,
% 2.22/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.22/0.98      | ~ v4_tex_2(X0,X1)
% 2.22/0.98      | v3_tex_2(u1_struct_0(X0),X1)
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | ~ l1_pre_topc(X1) ),
% 2.22/0.98      inference(global_propositional_subsumption,[status(thm)],[c_9,c_5]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_141,plain,
% 2.22/0.98      ( v3_tex_2(u1_struct_0(X0),X1)
% 2.22/0.98      | ~ v4_tex_2(X0,X1)
% 2.22/0.98      | ~ m1_pre_topc(X0,X1)
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | ~ l1_pre_topc(X1) ),
% 2.22/0.98      inference(renaming,[status(thm)],[c_140]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_391,plain,
% 2.22/0.98      ( v3_tex_2(u1_struct_0(X0),X1)
% 2.22/0.98      | ~ v4_tex_2(X0,X1)
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | ~ l1_pre_topc(X1)
% 2.22/0.98      | sK2 != X0
% 2.22/0.98      | sK1 != X1 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_141,c_20]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_392,plain,
% 2.22/0.98      ( v3_tex_2(u1_struct_0(sK2),sK1)
% 2.22/0.98      | ~ v4_tex_2(sK2,sK1)
% 2.22/0.98      | v2_struct_0(sK1)
% 2.22/0.98      | ~ l1_pre_topc(sK1) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_391]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_21,negated_conjecture,
% 2.22/0.98      ( v4_tex_2(sK2,sK1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_394,plain,
% 2.22/0.98      ( v3_tex_2(u1_struct_0(sK2),sK1) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_392,c_26,c_23,c_21]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_448,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | ~ v1_xboole_0(X0)
% 2.22/0.98      | u1_struct_0(sK2) != X0
% 2.22/0.98      | sK1 != sK1 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_311,c_394]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_449,plain,
% 2.22/0.98      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_448]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_450,plain,
% 2.22/0.98      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.22/0.98      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_880,plain,
% 2.22/0.98      ( ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 2.22/0.98      | v1_xboole_0(u1_struct_0(sK1))
% 2.22/0.98      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.22/0.98      inference(instantiation,[status(thm)],[c_548]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_881,plain,
% 2.22/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5)
% 2.22/0.98      | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
% 2.22/0.98      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_880]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_409,plain,
% 2.22/0.98      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_407,c_23]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_543,plain,
% 2.22/0.98      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_409]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_773,plain,
% 2.22/0.98      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_2,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/0.98      | ~ v1_xboole_0(X1)
% 2.22/0.98      | v1_xboole_0(X0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_549,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.22/0.98      | ~ v1_xboole_0(X1_54)
% 2.22/0.98      | v1_xboole_0(X0_54) ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_768,plain,
% 2.22/0.98      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 2.22/0.98      | v1_xboole_0(X1_54) != iProver_top
% 2.22/0.98      | v1_xboole_0(X0_54) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_549]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1209,plain,
% 2.22/0.98      ( v1_xboole_0(u1_struct_0(sK2)) = iProver_top
% 2.22/0.98      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_773,c_768]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1456,plain,
% 2.22/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK1),sK5) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1250,c_30,c_40,c_408,c_450,c_881,c_1209]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,X1)
% 2.22/0.98      | ~ m1_subset_1(X2,X1)
% 2.22/0.98      | ~ m1_subset_1(X3,X1)
% 2.22/0.98      | ~ m1_subset_1(X4,X1)
% 2.22/0.98      | ~ m1_subset_1(X5,X1)
% 2.22/0.98      | ~ m1_subset_1(X6,X1)
% 2.22/0.98      | ~ m1_subset_1(X7,X1)
% 2.22/0.98      | ~ m1_subset_1(X8,X1)
% 2.22/0.98      | m1_subset_1(k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X0),k1_zfmisc_1(X1))
% 2.22/0.98      | k1_xboole_0 = X1 ),
% 2.22/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_550,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0_54,X1_54)
% 2.22/0.98      | ~ m1_subset_1(X2_54,X1_54)
% 2.22/0.98      | ~ m1_subset_1(X3_54,X1_54)
% 2.22/0.98      | ~ m1_subset_1(X4_54,X1_54)
% 2.22/0.98      | ~ m1_subset_1(X5_54,X1_54)
% 2.22/0.98      | ~ m1_subset_1(X6_54,X1_54)
% 2.22/0.98      | ~ m1_subset_1(X7_54,X1_54)
% 2.22/0.98      | ~ m1_subset_1(X8_54,X1_54)
% 2.22/0.98      | m1_subset_1(k6_enumset1(X8_54,X7_54,X6_54,X5_54,X4_54,X3_54,X2_54,X0_54),k1_zfmisc_1(X1_54))
% 2.22/0.98      | k1_xboole_0 = X1_54 ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_767,plain,
% 2.22/0.98      ( k1_xboole_0 = X0_54
% 2.22/0.98      | m1_subset_1(X1_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(X2_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(X3_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(X4_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(X5_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(X6_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(X7_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(X8_54,X0_54) != iProver_top
% 2.22/0.98      | m1_subset_1(k6_enumset1(X8_54,X7_54,X6_54,X5_54,X4_54,X3_54,X2_54,X1_54),k1_zfmisc_1(X0_54)) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1459,plain,
% 2.22/0.98      ( k1_xboole_0 = X0_54
% 2.22/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK5),k1_zfmisc_1(X0_54)) = iProver_top
% 2.22/0.98      | m1_subset_1(sK5,X0_54) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_1456,c_767]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_3,plain,
% 2.22/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.22/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.98      | ~ l1_pre_topc(X1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_417,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.98      | ~ l1_pre_topc(X2)
% 2.22/0.98      | sK2 != X1
% 2.22/0.98      | sK1 != X2 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_418,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | ~ l1_pre_topc(sK1) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_417]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_422,plain,
% 2.22/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_418,c_23]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_423,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.22/0.98      inference(renaming,[status(thm)],[c_422]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_542,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_423]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_774,plain,
% 2.22/0.98      ( m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.22/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1559,plain,
% 2.22/0.98      ( u1_struct_0(sK2) = k1_xboole_0
% 2.22/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK5),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.22/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_1459,c_774]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_14,negated_conjecture,
% 2.22/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.22/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_39,plain,
% 2.22/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_545,negated_conjecture,
% 2.22/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_771,plain,
% 2.22/0.98      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1251,plain,
% 2.22/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5)
% 2.22/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_771,c_769]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_883,plain,
% 2.22/0.98      ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
% 2.22/0.98      | v1_xboole_0(u1_struct_0(sK2))
% 2.22/0.98      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 2.22/0.98      inference(instantiation,[status(thm)],[c_548]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1464,plain,
% 2.22/0.98      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1251,c_23,c_14,c_407,c_449,c_883]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1466,plain,
% 2.22/0.98      ( k6_domain_1(u1_struct_0(sK1),sK5) = k6_domain_1(u1_struct_0(sK2),sK5) ),
% 2.22/0.98      inference(light_normalisation,[status(thm)],[c_1464,c_1456]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_12,negated_conjecture,
% 2.22/0.98      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.22/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_547,negated_conjecture,
% 2.22/0.98      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1468,plain,
% 2.22/0.98      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_1466,c_547]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_11,plain,
% 2.22/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.22/0.98      | ~ v5_pre_topc(X0,X1,X2)
% 2.22/0.98      | ~ v3_borsuk_1(X0,X1,X2)
% 2.22/0.98      | ~ v4_tex_2(X2,X1)
% 2.22/0.98      | ~ m1_pre_topc(X2,X1)
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.22/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.98      | ~ v3_tdlat_3(X1)
% 2.22/0.98      | ~ v1_funct_1(X0)
% 2.22/0.98      | ~ v2_pre_topc(X1)
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | v2_struct_0(X2)
% 2.22/0.98      | ~ l1_pre_topc(X1)
% 2.22/0.98      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 2.22/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_15,negated_conjecture,
% 2.22/0.98      ( v3_borsuk_1(sK3,sK1,sK2) ),
% 2.22/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_281,plain,
% 2.22/0.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.22/0.98      | ~ v5_pre_topc(X0,X1,X2)
% 2.22/0.98      | ~ v4_tex_2(X2,X1)
% 2.22/0.98      | ~ m1_pre_topc(X2,X1)
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.22/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.98      | ~ v3_tdlat_3(X1)
% 2.22/0.98      | ~ v1_funct_1(X0)
% 2.22/0.98      | ~ v2_pre_topc(X1)
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | v2_struct_0(X2)
% 2.22/0.98      | ~ l1_pre_topc(X1)
% 2.22/0.98      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 2.22/0.98      | sK3 != X0
% 2.22/0.98      | sK2 != X2
% 2.22/0.98      | sK1 != X1 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_282,plain,
% 2.22/0.98      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 2.22/0.98      | ~ v5_pre_topc(sK3,sK1,sK2)
% 2.22/0.98      | ~ v4_tex_2(sK2,sK1)
% 2.22/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 2.22/0.98      | ~ v3_tdlat_3(sK1)
% 2.22/0.98      | ~ v1_funct_1(sK3)
% 2.22/0.98      | ~ v2_pre_topc(sK1)
% 2.22/0.98      | v2_struct_0(sK2)
% 2.22/0.98      | v2_struct_0(sK1)
% 2.22/0.98      | ~ l1_pre_topc(sK1)
% 2.22/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_281]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_24,negated_conjecture,
% 2.22/0.98      ( v3_tdlat_3(sK1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_22,negated_conjecture,
% 2.22/0.98      ( ~ v2_struct_0(sK2) ),
% 2.22/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_19,negated_conjecture,
% 2.22/0.98      ( v1_funct_1(sK3) ),
% 2.22/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_18,negated_conjecture,
% 2.22/0.98      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 2.22/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_17,negated_conjecture,
% 2.22/0.98      ( v5_pre_topc(sK3,sK1,sK2) ),
% 2.22/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_16,negated_conjecture,
% 2.22/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 2.22/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_286,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_282,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,
% 2.22/0.98                 c_16]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_287,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.22/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.22/0.98      inference(renaming,[status(thm)],[c_286]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_443,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 2.22/0.98      inference(backward_subsumption_resolution,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_423,c_287]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_541,plain,
% 2.22/0.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54) ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_443]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_775,plain,
% 2.22/0.98      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_54) = k2_pre_topc(sK1,X0_54)
% 2.22/0.98      | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1558,plain,
% 2.22/0.98      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK1),sK5)) = k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))
% 2.22/0.98      | u1_struct_0(sK2) = k1_xboole_0
% 2.22/0.98      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
% 2.22/0.98      inference(superposition,[status(thm)],[c_1459,c_775]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1599,plain,
% 2.22/0.98      ( u1_struct_0(sK2) = k1_xboole_0 ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1559,c_39,c_1468,c_1558]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_451,plain,
% 2.22/0.98      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_449,c_23,c_407]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_540,plain,
% 2.22/0.98      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.22/0.98      inference(subtyping,[status(esa)],[c_451]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_776,plain,
% 2.22/0.98      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1607,plain,
% 2.22/0.98      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.22/0.98      inference(demodulation,[status(thm)],[c_1599,c_776]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_0,plain,
% 2.22/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_70,plain,
% 2.22/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.22/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(contradiction,plain,
% 2.22/0.98      ( $false ),
% 2.22/0.98      inference(minisat,[status(thm)],[c_1607,c_70]) ).
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/0.98  
% 2.22/0.98  ------                               Statistics
% 2.22/0.98  
% 2.22/0.98  ------ General
% 2.22/0.98  
% 2.22/0.98  abstr_ref_over_cycles:                  0
% 2.22/0.98  abstr_ref_under_cycles:                 0
% 2.22/0.98  gc_basic_clause_elim:                   0
% 2.22/0.98  forced_gc_time:                         0
% 2.22/0.98  parsing_time:                           0.01
% 2.22/0.98  unif_index_cands_time:                  0.
% 2.22/0.98  unif_index_add_time:                    0.
% 2.22/0.98  orderings_time:                         0.
% 2.22/0.98  out_proof_time:                         0.014
% 2.22/0.98  total_time:                             0.1
% 2.22/0.98  num_of_symbols:                         63
% 2.22/0.98  num_of_terms:                           2354
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing
% 2.22/0.98  
% 2.22/0.98  num_of_splits:                          0
% 2.22/0.98  num_of_split_atoms:                     0
% 2.22/0.98  num_of_reused_defs:                     0
% 2.22/0.98  num_eq_ax_congr_red:                    29
% 2.22/0.98  num_of_sem_filtered_clauses:            1
% 2.22/0.98  num_of_subtypes:                        3
% 2.22/0.98  monotx_restored_types:                  0
% 2.22/0.98  sat_num_of_epr_types:                   0
% 2.22/0.98  sat_num_of_non_cyclic_types:            0
% 2.22/0.98  sat_guarded_non_collapsed_types:        1
% 2.22/0.98  num_pure_diseq_elim:                    0
% 2.22/0.98  simp_replaced_by:                       0
% 2.22/0.98  res_preprocessed:                       86
% 2.22/0.98  prep_upred:                             0
% 2.22/0.98  prep_unflattend:                        20
% 2.22/0.98  smt_new_axioms:                         0
% 2.22/0.98  pred_elim_cands:                        2
% 2.22/0.98  pred_elim:                              11
% 2.22/0.98  pred_elim_cl:                           15
% 2.22/0.98  pred_elim_cycles:                       14
% 2.22/0.98  merged_defs:                            0
% 2.22/0.98  merged_defs_ncl:                        0
% 2.22/0.98  bin_hyper_res:                          0
% 2.22/0.98  prep_cycles:                            4
% 2.22/0.98  pred_elim_time:                         0.005
% 2.22/0.98  splitting_time:                         0.
% 2.22/0.98  sem_filter_time:                        0.
% 2.22/0.98  monotx_time:                            0.
% 2.22/0.98  subtype_inf_time:                       0.
% 2.22/0.98  
% 2.22/0.98  ------ Problem properties
% 2.22/0.98  
% 2.22/0.98  clauses:                                12
% 2.22/0.98  conjectures:                            4
% 2.22/0.98  epr:                                    1
% 2.22/0.98  horn:                                   10
% 2.22/0.98  ground:                                 7
% 2.22/0.98  unary:                                  7
% 2.22/0.98  binary:                                 2
% 2.22/0.98  lits:                                   27
% 2.22/0.98  lits_eq:                                4
% 2.22/0.98  fd_pure:                                0
% 2.22/0.98  fd_pseudo:                              0
% 2.22/0.98  fd_cond:                                1
% 2.22/0.98  fd_pseudo_cond:                         0
% 2.22/0.98  ac_symbols:                             0
% 2.22/0.98  
% 2.22/0.98  ------ Propositional Solver
% 2.22/0.98  
% 2.22/0.98  prop_solver_calls:                      25
% 2.22/0.98  prop_fast_solver_calls:                 557
% 2.22/0.98  smt_solver_calls:                       0
% 2.22/0.98  smt_fast_solver_calls:                  0
% 2.22/0.98  prop_num_of_clauses:                    540
% 2.22/0.98  prop_preprocess_simplified:             2243
% 2.22/0.98  prop_fo_subsumed:                       27
% 2.22/0.98  prop_solver_time:                       0.
% 2.22/0.98  smt_solver_time:                        0.
% 2.22/0.98  smt_fast_solver_time:                   0.
% 2.22/0.98  prop_fast_solver_time:                  0.
% 2.22/0.98  prop_unsat_core_time:                   0.
% 2.22/0.98  
% 2.22/0.98  ------ QBF
% 2.22/0.98  
% 2.22/0.98  qbf_q_res:                              0
% 2.22/0.98  qbf_num_tautologies:                    0
% 2.22/0.98  qbf_prep_cycles:                        0
% 2.22/0.98  
% 2.22/0.98  ------ BMC1
% 2.22/0.98  
% 2.22/0.98  bmc1_current_bound:                     -1
% 2.22/0.98  bmc1_last_solved_bound:                 -1
% 2.22/0.98  bmc1_unsat_core_size:                   -1
% 2.22/0.98  bmc1_unsat_core_parents_size:           -1
% 2.22/0.98  bmc1_merge_next_fun:                    0
% 2.22/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.22/0.98  
% 2.22/0.98  ------ Instantiation
% 2.22/0.98  
% 2.22/0.98  inst_num_of_clauses:                    141
% 2.22/0.98  inst_num_in_passive:                    11
% 2.22/0.98  inst_num_in_active:                     93
% 2.22/0.98  inst_num_in_unprocessed:                37
% 2.22/0.98  inst_num_of_loops:                      100
% 2.22/0.98  inst_num_of_learning_restarts:          0
% 2.22/0.98  inst_num_moves_active_passive:          5
% 2.22/0.98  inst_lit_activity:                      0
% 2.22/0.98  inst_lit_activity_moves:                0
% 2.22/0.98  inst_num_tautologies:                   0
% 2.22/0.98  inst_num_prop_implied:                  0
% 2.22/0.98  inst_num_existing_simplified:           0
% 2.22/0.98  inst_num_eq_res_simplified:             0
% 2.22/0.98  inst_num_child_elim:                    0
% 2.22/0.98  inst_num_of_dismatching_blockings:      8
% 2.22/0.98  inst_num_of_non_proper_insts:           95
% 2.22/0.98  inst_num_of_duplicates:                 0
% 2.22/0.98  inst_inst_num_from_inst_to_res:         0
% 2.22/0.98  inst_dismatching_checking_time:         0.
% 2.22/0.98  
% 2.22/0.98  ------ Resolution
% 2.22/0.98  
% 2.22/0.98  res_num_of_clauses:                     0
% 2.22/0.98  res_num_in_passive:                     0
% 2.22/0.98  res_num_in_active:                      0
% 2.22/0.98  res_num_of_loops:                       90
% 2.22/0.98  res_forward_subset_subsumed:            20
% 2.22/0.98  res_backward_subset_subsumed:           2
% 2.22/0.98  res_forward_subsumed:                   0
% 2.22/0.98  res_backward_subsumed:                  0
% 2.22/0.98  res_forward_subsumption_resolution:     0
% 2.22/0.98  res_backward_subsumption_resolution:    1
% 2.22/0.98  res_clause_to_clause_subsumption:       54
% 2.22/0.98  res_orphan_elimination:                 0
% 2.22/0.98  res_tautology_del:                      11
% 2.22/0.98  res_num_eq_res_simplified:              0
% 2.22/0.98  res_num_sel_changes:                    0
% 2.22/0.98  res_moves_from_active_to_pass:          0
% 2.22/0.98  
% 2.22/0.98  ------ Superposition
% 2.22/0.98  
% 2.22/0.98  sup_time_total:                         0.
% 2.22/0.98  sup_time_generating:                    0.
% 2.22/0.98  sup_time_sim_full:                      0.
% 2.22/0.98  sup_time_sim_immed:                     0.
% 2.22/0.98  
% 2.22/0.98  sup_num_of_clauses:                     21
% 2.22/0.98  sup_num_in_active:                      8
% 2.22/0.98  sup_num_in_passive:                     13
% 2.22/0.98  sup_num_of_loops:                       19
% 2.22/0.98  sup_fw_superposition:                   8
% 2.22/0.98  sup_bw_superposition:                   7
% 2.22/0.98  sup_immediate_simplified:               1
% 2.22/0.98  sup_given_eliminated:                   0
% 2.22/0.98  comparisons_done:                       0
% 2.22/0.98  comparisons_avoided:                    0
% 2.22/0.98  
% 2.22/0.98  ------ Simplifications
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  sim_fw_subset_subsumed:                 0
% 2.22/0.98  sim_bw_subset_subsumed:                 1
% 2.22/0.98  sim_fw_subsumed:                        0
% 2.22/0.98  sim_bw_subsumed:                        0
% 2.22/0.98  sim_fw_subsumption_res:                 0
% 2.22/0.98  sim_bw_subsumption_res:                 0
% 2.22/0.98  sim_tautology_del:                      0
% 2.22/0.98  sim_eq_tautology_del:                   0
% 2.22/0.98  sim_eq_res_simp:                        0
% 2.22/0.98  sim_fw_demodulated:                     0
% 2.22/0.98  sim_bw_demodulated:                     11
% 2.22/0.98  sim_light_normalised:                   2
% 2.22/0.98  sim_joinable_taut:                      0
% 2.22/0.98  sim_joinable_simp:                      0
% 2.22/0.98  sim_ac_normalised:                      0
% 2.22/0.98  sim_smt_subsumption:                    0
% 2.22/0.98  
%------------------------------------------------------------------------------
