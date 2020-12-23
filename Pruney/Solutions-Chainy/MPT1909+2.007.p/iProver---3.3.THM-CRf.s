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
% DateTime   : Thu Dec  3 12:27:55 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  151 (1102 expanded)
%              Number of clauses        :   86 ( 245 expanded)
%              Number of leaves         :   16 ( 418 expanded)
%              Depth                    :   17
%              Number of atoms          :  597 (11679 expanded)
%              Number of equality atoms :  145 (2093 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))
        & sK5 = X3
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f29,f36,f35,f34,f33,f32])).

fof(f63,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(definition_unfolding,[],[f61,f63])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f30])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(flattening,[],[f26])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
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
    inference(equality_resolution,[],[f48])).

fof(f60,plain,(
    v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f54,plain,(
    v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(definition_unfolding,[],[f64,f63])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_467,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_719,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | v1_xboole_0(X1_53)
    | k2_tarski(X0_53,X0_53) = k6_domain_1(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_717,plain,
    ( k2_tarski(X0_53,X0_53) = k6_domain_1(X1_53,X0_53)
    | m1_subset_1(X0_53,X1_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_1093,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_719,c_717])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_289,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_290,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_291,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_5,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_300,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_301,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_pre_topc(sK2)
    | ~ v2_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_303,plain,
    ( v2_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_301,c_23,c_21])).

cnf(c_339,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_303])).

cnf(c_340,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_341,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_350,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_303])).

cnf(c_351,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(sK0(sK2)) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_352,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_894,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_53)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_991,plain,
    ( ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_894])).

cnf(c_992,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_991])).

cnf(c_1327,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1093,c_28,c_29,c_291,c_341,c_352,c_992])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0_53,X1_53)
    | m1_subset_1(k6_domain_1(X1_53,X0_53),k1_zfmisc_1(X1_53))
    | v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_716,plain,
    ( m1_subset_1(X0_53,X1_53) != iProver_top
    | m1_subset_1(k6_domain_1(X1_53,X0_53),k1_zfmisc_1(X1_53)) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_1331,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1327,c_716])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1796,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1331,c_28,c_29,c_37,c_291,c_341,c_352,c_992])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_466,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_720,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_715,plain,
    ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_1041,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_720,c_715])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_13,negated_conjecture,
    ( v3_borsuk_1(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_253,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_254,plain,
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
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v4_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,negated_conjecture,
    ( v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,c_14])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_465,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_53) = k2_pre_topc(sK1,X0_53) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_721,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_53) = k2_pre_topc(sK1,X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_1211,plain,
    ( k2_pre_topc(sK1,X0_53) = k10_relat_1(sK3,X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1041,c_721])).

cnf(c_1801,plain,
    ( k2_pre_topc(sK1,k2_tarski(sK5,sK5)) = k10_relat_1(sK3,k2_tarski(sK5,sK5))
    | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1211])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_468,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_718,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_1092,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_717])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_51,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_53,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_54,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_56,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v1_xboole_0(sK0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_884,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0_53)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_982,plain,
    ( ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_983,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(sK0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_1269,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1092,c_25,c_26,c_28,c_53,c_56,c_983])).

cnf(c_10,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_469,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1210,plain,
    ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k10_relat_1(sK3,k6_domain_1(u1_struct_0(sK2),sK5)) ),
    inference(demodulation,[status(thm)],[c_1041,c_469])).

cnf(c_1272,plain,
    ( k10_relat_1(sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_1269,c_1210])).

cnf(c_1330,plain,
    ( k2_pre_topc(sK1,k2_tarski(sK5,sK5)) != k10_relat_1(sK3,k2_tarski(sK5,sK5)) ),
    inference(demodulation,[status(thm)],[c_1327,c_1272])).

cnf(c_1273,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_716])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1801,c_1330,c_1273,c_983,c_56,c_53,c_38,c_28,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.67/0.93  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/0.93  
% 1.67/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.67/0.93  
% 1.67/0.93  ------  iProver source info
% 1.67/0.93  
% 1.67/0.93  git: date: 2020-06-30 10:37:57 +0100
% 1.67/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.67/0.93  git: non_committed_changes: false
% 1.67/0.93  git: last_make_outside_of_git: false
% 1.67/0.93  
% 1.67/0.93  ------ 
% 1.67/0.93  
% 1.67/0.93  ------ Input Options
% 1.67/0.93  
% 1.67/0.93  --out_options                           all
% 1.67/0.93  --tptp_safe_out                         true
% 1.67/0.93  --problem_path                          ""
% 1.67/0.93  --include_path                          ""
% 1.67/0.93  --clausifier                            res/vclausify_rel
% 1.67/0.93  --clausifier_options                    --mode clausify
% 1.67/0.93  --stdin                                 false
% 1.67/0.93  --stats_out                             all
% 1.67/0.93  
% 1.67/0.93  ------ General Options
% 1.67/0.93  
% 1.67/0.93  --fof                                   false
% 1.67/0.93  --time_out_real                         305.
% 1.67/0.93  --time_out_virtual                      -1.
% 1.67/0.93  --symbol_type_check                     false
% 1.67/0.93  --clausify_out                          false
% 1.67/0.93  --sig_cnt_out                           false
% 1.67/0.93  --trig_cnt_out                          false
% 1.67/0.93  --trig_cnt_out_tolerance                1.
% 1.67/0.93  --trig_cnt_out_sk_spl                   false
% 1.67/0.93  --abstr_cl_out                          false
% 1.67/0.93  
% 1.67/0.93  ------ Global Options
% 1.67/0.93  
% 1.67/0.93  --schedule                              default
% 1.67/0.93  --add_important_lit                     false
% 1.67/0.93  --prop_solver_per_cl                    1000
% 1.67/0.93  --min_unsat_core                        false
% 1.67/0.93  --soft_assumptions                      false
% 1.67/0.93  --soft_lemma_size                       3
% 1.67/0.93  --prop_impl_unit_size                   0
% 1.67/0.93  --prop_impl_unit                        []
% 1.67/0.93  --share_sel_clauses                     true
% 1.67/0.93  --reset_solvers                         false
% 1.67/0.93  --bc_imp_inh                            [conj_cone]
% 1.67/0.93  --conj_cone_tolerance                   3.
% 1.67/0.93  --extra_neg_conj                        none
% 1.67/0.93  --large_theory_mode                     true
% 1.67/0.93  --prolific_symb_bound                   200
% 1.67/0.93  --lt_threshold                          2000
% 1.67/0.93  --clause_weak_htbl                      true
% 1.67/0.93  --gc_record_bc_elim                     false
% 1.67/0.93  
% 1.67/0.93  ------ Preprocessing Options
% 1.67/0.93  
% 1.67/0.93  --preprocessing_flag                    true
% 1.67/0.93  --time_out_prep_mult                    0.1
% 1.67/0.93  --splitting_mode                        input
% 1.67/0.93  --splitting_grd                         true
% 1.67/0.93  --splitting_cvd                         false
% 1.67/0.93  --splitting_cvd_svl                     false
% 1.67/0.93  --splitting_nvd                         32
% 1.67/0.93  --sub_typing                            true
% 1.67/0.93  --prep_gs_sim                           true
% 1.67/0.93  --prep_unflatten                        true
% 1.67/0.93  --prep_res_sim                          true
% 1.67/0.93  --prep_upred                            true
% 1.67/0.93  --prep_sem_filter                       exhaustive
% 1.67/0.93  --prep_sem_filter_out                   false
% 1.67/0.93  --pred_elim                             true
% 1.67/0.93  --res_sim_input                         true
% 1.67/0.93  --eq_ax_congr_red                       true
% 1.67/0.93  --pure_diseq_elim                       true
% 1.67/0.93  --brand_transform                       false
% 1.67/0.93  --non_eq_to_eq                          false
% 1.67/0.93  --prep_def_merge                        true
% 1.67/0.93  --prep_def_merge_prop_impl              false
% 1.67/0.93  --prep_def_merge_mbd                    true
% 1.67/0.93  --prep_def_merge_tr_red                 false
% 1.67/0.93  --prep_def_merge_tr_cl                  false
% 1.67/0.93  --smt_preprocessing                     true
% 1.67/0.93  --smt_ac_axioms                         fast
% 1.67/0.93  --preprocessed_out                      false
% 1.67/0.93  --preprocessed_stats                    false
% 1.67/0.93  
% 1.67/0.93  ------ Abstraction refinement Options
% 1.67/0.93  
% 1.67/0.93  --abstr_ref                             []
% 1.67/0.93  --abstr_ref_prep                        false
% 1.67/0.93  --abstr_ref_until_sat                   false
% 1.67/0.93  --abstr_ref_sig_restrict                funpre
% 1.67/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/0.93  --abstr_ref_under                       []
% 1.67/0.93  
% 1.67/0.93  ------ SAT Options
% 1.67/0.93  
% 1.67/0.93  --sat_mode                              false
% 1.67/0.93  --sat_fm_restart_options                ""
% 1.67/0.93  --sat_gr_def                            false
% 1.67/0.93  --sat_epr_types                         true
% 1.67/0.93  --sat_non_cyclic_types                  false
% 1.67/0.93  --sat_finite_models                     false
% 1.67/0.93  --sat_fm_lemmas                         false
% 1.67/0.93  --sat_fm_prep                           false
% 1.67/0.93  --sat_fm_uc_incr                        true
% 1.67/0.93  --sat_out_model                         small
% 1.67/0.93  --sat_out_clauses                       false
% 1.67/0.93  
% 1.67/0.93  ------ QBF Options
% 1.67/0.93  
% 1.67/0.93  --qbf_mode                              false
% 1.67/0.93  --qbf_elim_univ                         false
% 1.67/0.93  --qbf_dom_inst                          none
% 1.67/0.93  --qbf_dom_pre_inst                      false
% 1.67/0.93  --qbf_sk_in                             false
% 1.67/0.93  --qbf_pred_elim                         true
% 1.67/0.93  --qbf_split                             512
% 1.67/0.93  
% 1.67/0.93  ------ BMC1 Options
% 1.67/0.93  
% 1.67/0.93  --bmc1_incremental                      false
% 1.67/0.93  --bmc1_axioms                           reachable_all
% 1.67/0.93  --bmc1_min_bound                        0
% 1.67/0.93  --bmc1_max_bound                        -1
% 1.67/0.93  --bmc1_max_bound_default                -1
% 1.67/0.93  --bmc1_symbol_reachability              true
% 1.67/0.93  --bmc1_property_lemmas                  false
% 1.67/0.93  --bmc1_k_induction                      false
% 1.67/0.93  --bmc1_non_equiv_states                 false
% 1.67/0.93  --bmc1_deadlock                         false
% 1.67/0.93  --bmc1_ucm                              false
% 1.67/0.93  --bmc1_add_unsat_core                   none
% 1.67/0.93  --bmc1_unsat_core_children              false
% 1.67/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/0.93  --bmc1_out_stat                         full
% 1.67/0.93  --bmc1_ground_init                      false
% 1.67/0.93  --bmc1_pre_inst_next_state              false
% 1.67/0.93  --bmc1_pre_inst_state                   false
% 1.67/0.93  --bmc1_pre_inst_reach_state             false
% 1.67/0.93  --bmc1_out_unsat_core                   false
% 1.67/0.93  --bmc1_aig_witness_out                  false
% 1.67/0.93  --bmc1_verbose                          false
% 1.67/0.93  --bmc1_dump_clauses_tptp                false
% 1.67/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.67/0.93  --bmc1_dump_file                        -
% 1.67/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.67/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.67/0.93  --bmc1_ucm_extend_mode                  1
% 1.67/0.93  --bmc1_ucm_init_mode                    2
% 1.67/0.93  --bmc1_ucm_cone_mode                    none
% 1.67/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.67/0.93  --bmc1_ucm_relax_model                  4
% 1.67/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.67/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/0.93  --bmc1_ucm_layered_model                none
% 1.67/0.93  --bmc1_ucm_max_lemma_size               10
% 1.67/0.93  
% 1.67/0.93  ------ AIG Options
% 1.67/0.93  
% 1.67/0.93  --aig_mode                              false
% 1.67/0.93  
% 1.67/0.93  ------ Instantiation Options
% 1.67/0.93  
% 1.67/0.93  --instantiation_flag                    true
% 1.67/0.93  --inst_sos_flag                         false
% 1.67/0.93  --inst_sos_phase                        true
% 1.67/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/0.93  --inst_lit_sel_side                     num_symb
% 1.67/0.93  --inst_solver_per_active                1400
% 1.67/0.93  --inst_solver_calls_frac                1.
% 1.67/0.93  --inst_passive_queue_type               priority_queues
% 1.67/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.67/0.93  --inst_passive_queues_freq              [25;2]
% 1.67/0.93  --inst_dismatching                      true
% 1.67/0.93  --inst_eager_unprocessed_to_passive     true
% 1.67/0.93  --inst_prop_sim_given                   true
% 1.67/0.93  --inst_prop_sim_new                     false
% 1.67/0.93  --inst_subs_new                         false
% 1.67/0.93  --inst_eq_res_simp                      false
% 1.67/0.93  --inst_subs_given                       false
% 1.67/0.93  --inst_orphan_elimination               true
% 1.67/0.93  --inst_learning_loop_flag               true
% 1.67/0.93  --inst_learning_start                   3000
% 1.67/0.93  --inst_learning_factor                  2
% 1.67/0.93  --inst_start_prop_sim_after_learn       3
% 1.67/0.93  --inst_sel_renew                        solver
% 1.67/0.93  --inst_lit_activity_flag                true
% 1.67/0.93  --inst_restr_to_given                   false
% 1.67/0.93  --inst_activity_threshold               500
% 1.67/0.93  --inst_out_proof                        true
% 1.67/0.93  
% 1.67/0.93  ------ Resolution Options
% 1.67/0.93  
% 1.67/0.93  --resolution_flag                       true
% 1.67/0.93  --res_lit_sel                           adaptive
% 1.67/0.93  --res_lit_sel_side                      none
% 1.67/0.93  --res_ordering                          kbo
% 1.67/0.93  --res_to_prop_solver                    active
% 1.67/0.93  --res_prop_simpl_new                    false
% 1.67/0.93  --res_prop_simpl_given                  true
% 1.67/0.93  --res_passive_queue_type                priority_queues
% 1.67/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.67/0.93  --res_passive_queues_freq               [15;5]
% 1.67/0.93  --res_forward_subs                      full
% 1.67/0.93  --res_backward_subs                     full
% 1.67/0.93  --res_forward_subs_resolution           true
% 1.67/0.93  --res_backward_subs_resolution          true
% 1.67/0.93  --res_orphan_elimination                true
% 1.67/0.93  --res_time_limit                        2.
% 1.67/0.93  --res_out_proof                         true
% 1.67/0.93  
% 1.67/0.93  ------ Superposition Options
% 1.67/0.93  
% 1.67/0.93  --superposition_flag                    true
% 1.67/0.93  --sup_passive_queue_type                priority_queues
% 1.67/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.67/0.93  --demod_completeness_check              fast
% 1.67/0.93  --demod_use_ground                      true
% 1.67/0.93  --sup_to_prop_solver                    passive
% 1.67/0.93  --sup_prop_simpl_new                    true
% 1.67/0.93  --sup_prop_simpl_given                  true
% 1.67/0.93  --sup_fun_splitting                     false
% 1.67/0.93  --sup_smt_interval                      50000
% 1.67/0.93  
% 1.67/0.93  ------ Superposition Simplification Setup
% 1.67/0.93  
% 1.67/0.93  --sup_indices_passive                   []
% 1.67/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.93  --sup_full_bw                           [BwDemod]
% 1.67/0.93  --sup_immed_triv                        [TrivRules]
% 1.67/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.93  --sup_immed_bw_main                     []
% 1.67/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.93  
% 1.67/0.93  ------ Combination Options
% 1.67/0.93  
% 1.67/0.93  --comb_res_mult                         3
% 1.67/0.93  --comb_sup_mult                         2
% 1.67/0.93  --comb_inst_mult                        10
% 1.67/0.93  
% 1.67/0.93  ------ Debug Options
% 1.67/0.93  
% 1.67/0.93  --dbg_backtrace                         false
% 1.67/0.93  --dbg_dump_prop_clauses                 false
% 1.67/0.93  --dbg_dump_prop_clauses_file            -
% 1.67/0.93  --dbg_out_stat                          false
% 1.67/0.93  ------ Parsing...
% 1.67/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.67/0.93  
% 1.67/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.67/0.93  
% 1.67/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.67/0.93  
% 1.67/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.67/0.93  ------ Proving...
% 1.67/0.93  ------ Problem Properties 
% 1.67/0.93  
% 1.67/0.93  
% 1.67/0.93  clauses                                 14
% 1.67/0.93  conjectures                             4
% 1.67/0.93  EPR                                     0
% 1.67/0.93  Horn                                    12
% 1.67/0.93  unary                                   9
% 1.67/0.93  binary                                  1
% 1.67/0.93  lits                                    23
% 1.67/0.93  lits eq                                 4
% 1.67/0.93  fd_pure                                 0
% 1.67/0.93  fd_pseudo                               0
% 1.67/0.93  fd_cond                                 0
% 1.67/0.93  fd_pseudo_cond                          0
% 1.67/0.93  AC symbols                              0
% 1.67/0.93  
% 1.67/0.93  ------ Schedule dynamic 5 is on 
% 1.67/0.93  
% 1.67/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.67/0.93  
% 1.67/0.93  
% 1.67/0.93  ------ 
% 1.67/0.93  Current options:
% 1.67/0.93  ------ 
% 1.67/0.93  
% 1.67/0.93  ------ Input Options
% 1.67/0.93  
% 1.67/0.93  --out_options                           all
% 1.67/0.93  --tptp_safe_out                         true
% 1.67/0.93  --problem_path                          ""
% 1.67/0.93  --include_path                          ""
% 1.67/0.93  --clausifier                            res/vclausify_rel
% 1.67/0.93  --clausifier_options                    --mode clausify
% 1.67/0.93  --stdin                                 false
% 1.67/0.93  --stats_out                             all
% 1.67/0.93  
% 1.67/0.93  ------ General Options
% 1.67/0.93  
% 1.67/0.93  --fof                                   false
% 1.67/0.93  --time_out_real                         305.
% 1.67/0.93  --time_out_virtual                      -1.
% 1.67/0.93  --symbol_type_check                     false
% 1.67/0.93  --clausify_out                          false
% 1.67/0.93  --sig_cnt_out                           false
% 1.67/0.93  --trig_cnt_out                          false
% 1.67/0.93  --trig_cnt_out_tolerance                1.
% 1.67/0.93  --trig_cnt_out_sk_spl                   false
% 1.67/0.93  --abstr_cl_out                          false
% 1.67/0.93  
% 1.67/0.93  ------ Global Options
% 1.67/0.93  
% 1.67/0.93  --schedule                              default
% 1.67/0.93  --add_important_lit                     false
% 1.67/0.93  --prop_solver_per_cl                    1000
% 1.67/0.93  --min_unsat_core                        false
% 1.67/0.93  --soft_assumptions                      false
% 1.67/0.93  --soft_lemma_size                       3
% 1.67/0.93  --prop_impl_unit_size                   0
% 1.67/0.93  --prop_impl_unit                        []
% 1.67/0.93  --share_sel_clauses                     true
% 1.67/0.93  --reset_solvers                         false
% 1.67/0.93  --bc_imp_inh                            [conj_cone]
% 1.67/0.93  --conj_cone_tolerance                   3.
% 1.67/0.93  --extra_neg_conj                        none
% 1.67/0.93  --large_theory_mode                     true
% 1.67/0.93  --prolific_symb_bound                   200
% 1.67/0.93  --lt_threshold                          2000
% 1.67/0.93  --clause_weak_htbl                      true
% 1.67/0.93  --gc_record_bc_elim                     false
% 1.67/0.93  
% 1.67/0.93  ------ Preprocessing Options
% 1.67/0.93  
% 1.67/0.93  --preprocessing_flag                    true
% 1.67/0.93  --time_out_prep_mult                    0.1
% 1.67/0.93  --splitting_mode                        input
% 1.67/0.93  --splitting_grd                         true
% 1.67/0.93  --splitting_cvd                         false
% 1.67/0.93  --splitting_cvd_svl                     false
% 1.67/0.93  --splitting_nvd                         32
% 1.67/0.93  --sub_typing                            true
% 1.67/0.93  --prep_gs_sim                           true
% 1.67/0.93  --prep_unflatten                        true
% 1.67/0.93  --prep_res_sim                          true
% 1.67/0.93  --prep_upred                            true
% 1.67/0.93  --prep_sem_filter                       exhaustive
% 1.67/0.93  --prep_sem_filter_out                   false
% 1.67/0.93  --pred_elim                             true
% 1.67/0.93  --res_sim_input                         true
% 1.67/0.93  --eq_ax_congr_red                       true
% 1.67/0.93  --pure_diseq_elim                       true
% 1.67/0.93  --brand_transform                       false
% 1.67/0.93  --non_eq_to_eq                          false
% 1.67/0.93  --prep_def_merge                        true
% 1.67/0.93  --prep_def_merge_prop_impl              false
% 1.67/0.93  --prep_def_merge_mbd                    true
% 1.67/0.93  --prep_def_merge_tr_red                 false
% 1.67/0.93  --prep_def_merge_tr_cl                  false
% 1.67/0.93  --smt_preprocessing                     true
% 1.67/0.93  --smt_ac_axioms                         fast
% 1.67/0.93  --preprocessed_out                      false
% 1.67/0.93  --preprocessed_stats                    false
% 1.67/0.93  
% 1.67/0.93  ------ Abstraction refinement Options
% 1.67/0.93  
% 1.67/0.93  --abstr_ref                             []
% 1.67/0.93  --abstr_ref_prep                        false
% 1.67/0.93  --abstr_ref_until_sat                   false
% 1.67/0.93  --abstr_ref_sig_restrict                funpre
% 1.67/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/0.93  --abstr_ref_under                       []
% 1.67/0.93  
% 1.67/0.93  ------ SAT Options
% 1.67/0.93  
% 1.67/0.93  --sat_mode                              false
% 1.67/0.93  --sat_fm_restart_options                ""
% 1.67/0.93  --sat_gr_def                            false
% 1.67/0.93  --sat_epr_types                         true
% 1.67/0.93  --sat_non_cyclic_types                  false
% 1.67/0.93  --sat_finite_models                     false
% 1.67/0.93  --sat_fm_lemmas                         false
% 1.67/0.93  --sat_fm_prep                           false
% 1.67/0.93  --sat_fm_uc_incr                        true
% 1.67/0.93  --sat_out_model                         small
% 1.67/0.93  --sat_out_clauses                       false
% 1.67/0.93  
% 1.67/0.93  ------ QBF Options
% 1.67/0.93  
% 1.67/0.93  --qbf_mode                              false
% 1.67/0.93  --qbf_elim_univ                         false
% 1.67/0.93  --qbf_dom_inst                          none
% 1.67/0.93  --qbf_dom_pre_inst                      false
% 1.67/0.93  --qbf_sk_in                             false
% 1.67/0.93  --qbf_pred_elim                         true
% 1.67/0.93  --qbf_split                             512
% 1.67/0.93  
% 1.67/0.93  ------ BMC1 Options
% 1.67/0.93  
% 1.67/0.93  --bmc1_incremental                      false
% 1.67/0.93  --bmc1_axioms                           reachable_all
% 1.67/0.93  --bmc1_min_bound                        0
% 1.67/0.93  --bmc1_max_bound                        -1
% 1.67/0.93  --bmc1_max_bound_default                -1
% 1.67/0.93  --bmc1_symbol_reachability              true
% 1.67/0.93  --bmc1_property_lemmas                  false
% 1.67/0.93  --bmc1_k_induction                      false
% 1.67/0.93  --bmc1_non_equiv_states                 false
% 1.67/0.93  --bmc1_deadlock                         false
% 1.67/0.93  --bmc1_ucm                              false
% 1.67/0.93  --bmc1_add_unsat_core                   none
% 1.67/0.93  --bmc1_unsat_core_children              false
% 1.67/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/0.93  --bmc1_out_stat                         full
% 1.67/0.93  --bmc1_ground_init                      false
% 1.67/0.93  --bmc1_pre_inst_next_state              false
% 1.67/0.93  --bmc1_pre_inst_state                   false
% 1.67/0.93  --bmc1_pre_inst_reach_state             false
% 1.67/0.93  --bmc1_out_unsat_core                   false
% 1.67/0.93  --bmc1_aig_witness_out                  false
% 1.67/0.93  --bmc1_verbose                          false
% 1.67/0.93  --bmc1_dump_clauses_tptp                false
% 1.67/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.67/0.93  --bmc1_dump_file                        -
% 1.67/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.67/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.67/0.93  --bmc1_ucm_extend_mode                  1
% 1.67/0.93  --bmc1_ucm_init_mode                    2
% 1.67/0.93  --bmc1_ucm_cone_mode                    none
% 1.67/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.67/0.93  --bmc1_ucm_relax_model                  4
% 1.67/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.67/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/0.93  --bmc1_ucm_layered_model                none
% 1.67/0.93  --bmc1_ucm_max_lemma_size               10
% 1.67/0.93  
% 1.67/0.93  ------ AIG Options
% 1.67/0.93  
% 1.67/0.93  --aig_mode                              false
% 1.67/0.93  
% 1.67/0.93  ------ Instantiation Options
% 1.67/0.93  
% 1.67/0.93  --instantiation_flag                    true
% 1.67/0.93  --inst_sos_flag                         false
% 1.67/0.93  --inst_sos_phase                        true
% 1.67/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/0.93  --inst_lit_sel_side                     none
% 1.67/0.93  --inst_solver_per_active                1400
% 1.67/0.93  --inst_solver_calls_frac                1.
% 1.67/0.93  --inst_passive_queue_type               priority_queues
% 1.67/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.67/0.93  --inst_passive_queues_freq              [25;2]
% 1.67/0.93  --inst_dismatching                      true
% 1.67/0.93  --inst_eager_unprocessed_to_passive     true
% 1.67/0.93  --inst_prop_sim_given                   true
% 1.67/0.93  --inst_prop_sim_new                     false
% 1.67/0.93  --inst_subs_new                         false
% 1.67/0.93  --inst_eq_res_simp                      false
% 1.67/0.93  --inst_subs_given                       false
% 1.67/0.93  --inst_orphan_elimination               true
% 1.67/0.93  --inst_learning_loop_flag               true
% 1.67/0.93  --inst_learning_start                   3000
% 1.67/0.93  --inst_learning_factor                  2
% 1.67/0.93  --inst_start_prop_sim_after_learn       3
% 1.67/0.93  --inst_sel_renew                        solver
% 1.67/0.93  --inst_lit_activity_flag                true
% 1.67/0.93  --inst_restr_to_given                   false
% 1.67/0.93  --inst_activity_threshold               500
% 1.67/0.93  --inst_out_proof                        true
% 1.67/0.93  
% 1.67/0.93  ------ Resolution Options
% 1.67/0.93  
% 1.67/0.93  --resolution_flag                       false
% 1.67/0.93  --res_lit_sel                           adaptive
% 1.67/0.93  --res_lit_sel_side                      none
% 1.67/0.93  --res_ordering                          kbo
% 1.67/0.93  --res_to_prop_solver                    active
% 1.67/0.93  --res_prop_simpl_new                    false
% 1.67/0.93  --res_prop_simpl_given                  true
% 1.67/0.93  --res_passive_queue_type                priority_queues
% 1.67/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.67/0.93  --res_passive_queues_freq               [15;5]
% 1.67/0.93  --res_forward_subs                      full
% 1.67/0.93  --res_backward_subs                     full
% 1.67/0.93  --res_forward_subs_resolution           true
% 1.67/0.93  --res_backward_subs_resolution          true
% 1.67/0.93  --res_orphan_elimination                true
% 1.67/0.93  --res_time_limit                        2.
% 1.67/0.93  --res_out_proof                         true
% 1.67/0.93  
% 1.67/0.93  ------ Superposition Options
% 1.67/0.93  
% 1.67/0.93  --superposition_flag                    true
% 1.67/0.93  --sup_passive_queue_type                priority_queues
% 1.67/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.67/0.94  --demod_completeness_check              fast
% 1.67/0.94  --demod_use_ground                      true
% 1.67/0.94  --sup_to_prop_solver                    passive
% 1.67/0.94  --sup_prop_simpl_new                    true
% 1.67/0.94  --sup_prop_simpl_given                  true
% 1.67/0.94  --sup_fun_splitting                     false
% 1.67/0.94  --sup_smt_interval                      50000
% 1.67/0.94  
% 1.67/0.94  ------ Superposition Simplification Setup
% 1.67/0.94  
% 1.67/0.94  --sup_indices_passive                   []
% 1.67/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.94  --sup_full_bw                           [BwDemod]
% 1.67/0.94  --sup_immed_triv                        [TrivRules]
% 1.67/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.94  --sup_immed_bw_main                     []
% 1.67/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.94  
% 1.67/0.94  ------ Combination Options
% 1.67/0.94  
% 1.67/0.94  --comb_res_mult                         3
% 1.67/0.94  --comb_sup_mult                         2
% 1.67/0.94  --comb_inst_mult                        10
% 1.67/0.94  
% 1.67/0.94  ------ Debug Options
% 1.67/0.94  
% 1.67/0.94  --dbg_backtrace                         false
% 1.67/0.94  --dbg_dump_prop_clauses                 false
% 1.67/0.94  --dbg_dump_prop_clauses_file            -
% 1.67/0.94  --dbg_out_stat                          false
% 1.67/0.94  
% 1.67/0.94  
% 1.67/0.94  
% 1.67/0.94  
% 1.67/0.94  ------ Proving...
% 1.67/0.94  
% 1.67/0.94  
% 1.67/0.94  % SZS status Theorem for theBenchmark.p
% 1.67/0.94  
% 1.67/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 1.67/0.94  
% 1.67/0.94  fof(f61,plain,(
% 1.67/0.94    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f11,conjecture,(
% 1.67/0.94    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f12,negated_conjecture,(
% 1.67/0.94    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.67/0.94    inference(negated_conjecture,[],[f11])).
% 1.67/0.94  
% 1.67/0.94  fof(f28,plain,(
% 1.67/0.94    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.67/0.94    inference(ennf_transformation,[],[f12])).
% 1.67/0.94  
% 1.67/0.94  fof(f29,plain,(
% 1.67/0.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.67/0.94    inference(flattening,[],[f28])).
% 1.67/0.94  
% 1.67/0.94  fof(f36,plain,(
% 1.67/0.94    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)) & sK5 = X3 & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 1.67/0.94    introduced(choice_axiom,[])).
% 1.67/0.94  
% 1.67/0.94  fof(f35,plain,(
% 1.67/0.94    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK4)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK4 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.67/0.94    introduced(choice_axiom,[])).
% 1.67/0.94  
% 1.67/0.94  fof(f34,plain,(
% 1.67/0.94    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK3,X0,X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK3,X0,X1) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 1.67/0.94    introduced(choice_axiom,[])).
% 1.67/0.94  
% 1.67/0.94  fof(f33,plain,(
% 1.67/0.94    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2,k6_domain_1(u1_struct_0(sK2),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK2))) & v3_borsuk_1(X2,X0,sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v5_pre_topc(X2,X0,sK2) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & m1_pre_topc(sK2,X0) & v4_tex_2(sK2,X0) & ~v2_struct_0(sK2))) )),
% 1.67/0.94    introduced(choice_axiom,[])).
% 1.67/0.94  
% 1.67/0.94  fof(f32,plain,(
% 1.67/0.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK1,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v5_pre_topc(X2,sK1,X1) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK1) & v4_tex_2(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.67/0.94    introduced(choice_axiom,[])).
% 1.67/0.94  
% 1.67/0.94  fof(f37,plain,(
% 1.67/0.94    ((((k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) & sK4 = sK5 & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK2))) & v3_borsuk_1(sK3,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v5_pre_topc(sK3,sK1,sK2) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & v4_tex_2(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.67/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f29,f36,f35,f34,f33,f32])).
% 1.67/0.94  
% 1.67/0.94  fof(f63,plain,(
% 1.67/0.94    sK4 = sK5),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f67,plain,(
% 1.67/0.94    m1_subset_1(sK5,u1_struct_0(sK2))),
% 1.67/0.94    inference(definition_unfolding,[],[f61,f63])).
% 1.67/0.94  
% 1.67/0.94  fof(f8,axiom,(
% 1.67/0.94    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f23,plain,(
% 1.67/0.94    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.67/0.94    inference(ennf_transformation,[],[f8])).
% 1.67/0.94  
% 1.67/0.94  fof(f24,plain,(
% 1.67/0.94    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.67/0.94    inference(flattening,[],[f23])).
% 1.67/0.94  
% 1.67/0.94  fof(f46,plain,(
% 1.67/0.94    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f24])).
% 1.67/0.94  
% 1.67/0.94  fof(f1,axiom,(
% 1.67/0.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f38,plain,(
% 1.67/0.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f1])).
% 1.67/0.94  
% 1.67/0.94  fof(f65,plain,(
% 1.67/0.94    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.94    inference(definition_unfolding,[],[f46,f38])).
% 1.67/0.94  
% 1.67/0.94  fof(f52,plain,(
% 1.67/0.94    l1_pre_topc(sK1)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f53,plain,(
% 1.67/0.94    ~v2_struct_0(sK2)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f5,axiom,(
% 1.67/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f18,plain,(
% 1.67/0.94    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.67/0.94    inference(ennf_transformation,[],[f5])).
% 1.67/0.94  
% 1.67/0.94  fof(f42,plain,(
% 1.67/0.94    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f18])).
% 1.67/0.94  
% 1.67/0.94  fof(f55,plain,(
% 1.67/0.94    m1_pre_topc(sK2,sK1)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f6,axiom,(
% 1.67/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f13,plain,(
% 1.67/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.67/0.94    inference(pure_predicate_removal,[],[f6])).
% 1.67/0.94  
% 1.67/0.94  fof(f19,plain,(
% 1.67/0.94    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.94    inference(ennf_transformation,[],[f13])).
% 1.67/0.94  
% 1.67/0.94  fof(f20,plain,(
% 1.67/0.94    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.94    inference(flattening,[],[f19])).
% 1.67/0.94  
% 1.67/0.94  fof(f30,plain,(
% 1.67/0.94    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.67/0.94    introduced(choice_axiom,[])).
% 1.67/0.94  
% 1.67/0.94  fof(f31,plain,(
% 1.67/0.94    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f30])).
% 1.67/0.94  
% 1.67/0.94  fof(f43,plain,(
% 1.67/0.94    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f31])).
% 1.67/0.94  
% 1.67/0.94  fof(f4,axiom,(
% 1.67/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f16,plain,(
% 1.67/0.94    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.67/0.94    inference(ennf_transformation,[],[f4])).
% 1.67/0.94  
% 1.67/0.94  fof(f17,plain,(
% 1.67/0.94    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.67/0.94    inference(flattening,[],[f16])).
% 1.67/0.94  
% 1.67/0.94  fof(f41,plain,(
% 1.67/0.94    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f17])).
% 1.67/0.94  
% 1.67/0.94  fof(f50,plain,(
% 1.67/0.94    v2_pre_topc(sK1)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f44,plain,(
% 1.67/0.94    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f31])).
% 1.67/0.94  
% 1.67/0.94  fof(f2,axiom,(
% 1.67/0.94    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f14,plain,(
% 1.67/0.94    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.67/0.94    inference(ennf_transformation,[],[f2])).
% 1.67/0.94  
% 1.67/0.94  fof(f39,plain,(
% 1.67/0.94    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f14])).
% 1.67/0.94  
% 1.67/0.94  fof(f7,axiom,(
% 1.67/0.94    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f21,plain,(
% 1.67/0.94    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.67/0.94    inference(ennf_transformation,[],[f7])).
% 1.67/0.94  
% 1.67/0.94  fof(f22,plain,(
% 1.67/0.94    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.67/0.94    inference(flattening,[],[f21])).
% 1.67/0.94  
% 1.67/0.94  fof(f45,plain,(
% 1.67/0.94    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f22])).
% 1.67/0.94  
% 1.67/0.94  fof(f59,plain,(
% 1.67/0.94    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f3,axiom,(
% 1.67/0.94    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f15,plain,(
% 1.67/0.94    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.94    inference(ennf_transformation,[],[f3])).
% 1.67/0.94  
% 1.67/0.94  fof(f40,plain,(
% 1.67/0.94    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.94    inference(cnf_transformation,[],[f15])).
% 1.67/0.94  
% 1.67/0.94  fof(f10,axiom,(
% 1.67/0.94    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.67/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.67/0.94  
% 1.67/0.94  fof(f26,plain,(
% 1.67/0.94    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.94    inference(ennf_transformation,[],[f10])).
% 1.67/0.94  
% 1.67/0.94  fof(f27,plain,(
% 1.67/0.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.94    inference(flattening,[],[f26])).
% 1.67/0.94  
% 1.67/0.94  fof(f48,plain,(
% 1.67/0.94    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.94    inference(cnf_transformation,[],[f27])).
% 1.67/0.94  
% 1.67/0.94  fof(f68,plain,(
% 1.67/0.94    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.94    inference(equality_resolution,[],[f48])).
% 1.67/0.94  
% 1.67/0.94  fof(f60,plain,(
% 1.67/0.94    v3_borsuk_1(sK3,sK1,sK2)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f49,plain,(
% 1.67/0.94    ~v2_struct_0(sK1)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f51,plain,(
% 1.67/0.94    v3_tdlat_3(sK1)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f54,plain,(
% 1.67/0.94    v4_tex_2(sK2,sK1)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f56,plain,(
% 1.67/0.94    v1_funct_1(sK3)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f57,plain,(
% 1.67/0.94    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f58,plain,(
% 1.67/0.94    v5_pre_topc(sK3,sK1,sK2)),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f62,plain,(
% 1.67/0.94    m1_subset_1(sK5,u1_struct_0(sK1))),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f64,plain,(
% 1.67/0.94    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK4)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 1.67/0.94    inference(cnf_transformation,[],[f37])).
% 1.67/0.94  
% 1.67/0.94  fof(f66,plain,(
% 1.67/0.94    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5))),
% 1.67/0.94    inference(definition_unfolding,[],[f64,f63])).
% 1.67/0.94  
% 1.67/0.94  cnf(c_12,negated_conjecture,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.67/0.94      inference(cnf_transformation,[],[f67]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_467,negated_conjecture,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_12]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_719,plain,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_7,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0,X1)
% 1.67/0.94      | v1_xboole_0(X1)
% 1.67/0.94      | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
% 1.67/0.94      inference(cnf_transformation,[],[f65]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_470,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0_53,X1_53)
% 1.67/0.94      | v1_xboole_0(X1_53)
% 1.67/0.94      | k2_tarski(X0_53,X0_53) = k6_domain_1(X1_53,X0_53) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_7]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_717,plain,
% 1.67/0.94      ( k2_tarski(X0_53,X0_53) = k6_domain_1(X1_53,X0_53)
% 1.67/0.94      | m1_subset_1(X0_53,X1_53) != iProver_top
% 1.67/0.94      | v1_xboole_0(X1_53) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1093,plain,
% 1.67/0.94      ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5)
% 1.67/0.94      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.67/0.94      inference(superposition,[status(thm)],[c_719,c_717]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_21,negated_conjecture,
% 1.67/0.94      ( l1_pre_topc(sK1) ),
% 1.67/0.94      inference(cnf_transformation,[],[f52]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_28,plain,
% 1.67/0.94      ( l1_pre_topc(sK1) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_20,negated_conjecture,
% 1.67/0.94      ( ~ v2_struct_0(sK2) ),
% 1.67/0.94      inference(cnf_transformation,[],[f53]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_29,plain,
% 1.67/0.94      ( v2_struct_0(sK2) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_3,plain,
% 1.67/0.94      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.67/0.94      inference(cnf_transformation,[],[f42]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_18,negated_conjecture,
% 1.67/0.94      ( m1_pre_topc(sK2,sK1) ),
% 1.67/0.94      inference(cnf_transformation,[],[f55]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_289,plain,
% 1.67/0.94      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK2 != X1 | sK1 != X0 ),
% 1.67/0.94      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_290,plain,
% 1.67/0.94      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 1.67/0.94      inference(unflattening,[status(thm)],[c_289]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_291,plain,
% 1.67/0.94      ( l1_pre_topc(sK2) = iProver_top
% 1.67/0.94      | l1_pre_topc(sK1) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_5,plain,
% 1.67/0.94      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/0.94      | v2_struct_0(X0)
% 1.67/0.94      | ~ l1_pre_topc(X0)
% 1.67/0.94      | ~ v2_pre_topc(X0) ),
% 1.67/0.94      inference(cnf_transformation,[],[f43]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_2,plain,
% 1.67/0.94      ( ~ m1_pre_topc(X0,X1)
% 1.67/0.94      | ~ l1_pre_topc(X1)
% 1.67/0.94      | ~ v2_pre_topc(X1)
% 1.67/0.94      | v2_pre_topc(X0) ),
% 1.67/0.94      inference(cnf_transformation,[],[f41]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_300,plain,
% 1.67/0.94      ( ~ l1_pre_topc(X0)
% 1.67/0.94      | ~ v2_pre_topc(X0)
% 1.67/0.94      | v2_pre_topc(X1)
% 1.67/0.94      | sK2 != X1
% 1.67/0.94      | sK1 != X0 ),
% 1.67/0.94      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_301,plain,
% 1.67/0.94      ( ~ l1_pre_topc(sK1) | v2_pre_topc(sK2) | ~ v2_pre_topc(sK1) ),
% 1.67/0.94      inference(unflattening,[status(thm)],[c_300]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_23,negated_conjecture,
% 1.67/0.94      ( v2_pre_topc(sK1) ),
% 1.67/0.94      inference(cnf_transformation,[],[f50]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_303,plain,
% 1.67/0.94      ( v2_pre_topc(sK2) ),
% 1.67/0.94      inference(global_propositional_subsumption,
% 1.67/0.94                [status(thm)],
% 1.67/0.94                [c_301,c_23,c_21]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_339,plain,
% 1.67/0.94      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.67/0.94      | v2_struct_0(X0)
% 1.67/0.94      | ~ l1_pre_topc(X0)
% 1.67/0.94      | sK2 != X0 ),
% 1.67/0.94      inference(resolution_lifted,[status(thm)],[c_5,c_303]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_340,plain,
% 1.67/0.94      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.67/0.94      | v2_struct_0(sK2)
% 1.67/0.94      | ~ l1_pre_topc(sK2) ),
% 1.67/0.94      inference(unflattening,[status(thm)],[c_339]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_341,plain,
% 1.67/0.94      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.67/0.94      | v2_struct_0(sK2) = iProver_top
% 1.67/0.94      | l1_pre_topc(sK2) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_4,plain,
% 1.67/0.94      ( v2_struct_0(X0)
% 1.67/0.94      | ~ l1_pre_topc(X0)
% 1.67/0.94      | ~ v2_pre_topc(X0)
% 1.67/0.94      | ~ v1_xboole_0(sK0(X0)) ),
% 1.67/0.94      inference(cnf_transformation,[],[f44]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_350,plain,
% 1.67/0.94      ( v2_struct_0(X0)
% 1.67/0.94      | ~ l1_pre_topc(X0)
% 1.67/0.94      | ~ v1_xboole_0(sK0(X0))
% 1.67/0.94      | sK2 != X0 ),
% 1.67/0.94      inference(resolution_lifted,[status(thm)],[c_4,c_303]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_351,plain,
% 1.67/0.94      ( v2_struct_0(sK2) | ~ l1_pre_topc(sK2) | ~ v1_xboole_0(sK0(sK2)) ),
% 1.67/0.94      inference(unflattening,[status(thm)],[c_350]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_352,plain,
% 1.67/0.94      ( v2_struct_0(sK2) = iProver_top
% 1.67/0.94      | l1_pre_topc(sK2) != iProver_top
% 1.67/0.94      | v1_xboole_0(sK0(sK2)) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_0,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.67/0.94      | ~ v1_xboole_0(X1)
% 1.67/0.94      | v1_xboole_0(X0) ),
% 1.67/0.94      inference(cnf_transformation,[],[f39]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_473,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 1.67/0.94      | ~ v1_xboole_0(X1_53)
% 1.67/0.94      | v1_xboole_0(X0_53) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_0]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_894,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.67/0.94      | v1_xboole_0(X0_53)
% 1.67/0.94      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.67/0.94      inference(instantiation,[status(thm)],[c_473]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_991,plain,
% 1.67/0.94      ( ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.67/0.94      | ~ v1_xboole_0(u1_struct_0(sK2))
% 1.67/0.94      | v1_xboole_0(sK0(sK2)) ),
% 1.67/0.94      inference(instantiation,[status(thm)],[c_894]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_992,plain,
% 1.67/0.94      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.67/0.94      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 1.67/0.94      | v1_xboole_0(sK0(sK2)) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_991]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1327,plain,
% 1.67/0.94      ( k6_domain_1(u1_struct_0(sK2),sK5) = k2_tarski(sK5,sK5) ),
% 1.67/0.94      inference(global_propositional_subsumption,
% 1.67/0.94                [status(thm)],
% 1.67/0.94                [c_1093,c_28,c_29,c_291,c_341,c_352,c_992]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_6,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0,X1)
% 1.67/0.94      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.67/0.94      | v1_xboole_0(X1) ),
% 1.67/0.94      inference(cnf_transformation,[],[f45]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_471,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0_53,X1_53)
% 1.67/0.94      | m1_subset_1(k6_domain_1(X1_53,X0_53),k1_zfmisc_1(X1_53))
% 1.67/0.94      | v1_xboole_0(X1_53) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_6]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_716,plain,
% 1.67/0.94      ( m1_subset_1(X0_53,X1_53) != iProver_top
% 1.67/0.94      | m1_subset_1(k6_domain_1(X1_53,X0_53),k1_zfmisc_1(X1_53)) = iProver_top
% 1.67/0.94      | v1_xboole_0(X1_53) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1331,plain,
% 1.67/0.94      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 1.67/0.94      | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
% 1.67/0.94      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.67/0.94      inference(superposition,[status(thm)],[c_1327,c_716]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_37,plain,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1796,plain,
% 1.67/0.94      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.67/0.94      inference(global_propositional_subsumption,
% 1.67/0.94                [status(thm)],
% 1.67/0.94                [c_1331,c_28,c_29,c_37,c_291,c_341,c_352,c_992]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_14,negated_conjecture,
% 1.67/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.67/0.94      inference(cnf_transformation,[],[f59]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_466,negated_conjecture,
% 1.67/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_14]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_720,plain,
% 1.67/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.67/0.94      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.67/0.94      inference(cnf_transformation,[],[f40]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_472,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 1.67/0.94      | k8_relset_1(X1_53,X2_53,X0_53,X3_53) = k10_relat_1(X0_53,X3_53) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_1]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_715,plain,
% 1.67/0.94      ( k8_relset_1(X0_53,X1_53,X2_53,X3_53) = k10_relat_1(X2_53,X3_53)
% 1.67/0.94      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1041,plain,
% 1.67/0.94      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_53) = k10_relat_1(sK3,X0_53) ),
% 1.67/0.94      inference(superposition,[status(thm)],[c_720,c_715]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_9,plain,
% 1.67/0.94      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.67/0.94      | ~ v5_pre_topc(X0,X1,X2)
% 1.67/0.94      | ~ v3_borsuk_1(X0,X1,X2)
% 1.67/0.94      | ~ v4_tex_2(X2,X1)
% 1.67/0.94      | ~ m1_pre_topc(X2,X1)
% 1.67/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.67/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.67/0.94      | ~ v3_tdlat_3(X1)
% 1.67/0.94      | ~ v1_funct_1(X0)
% 1.67/0.94      | v2_struct_0(X1)
% 1.67/0.94      | v2_struct_0(X2)
% 1.67/0.94      | ~ l1_pre_topc(X1)
% 1.67/0.94      | ~ v2_pre_topc(X1)
% 1.67/0.94      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 1.67/0.94      inference(cnf_transformation,[],[f68]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_13,negated_conjecture,
% 1.67/0.94      ( v3_borsuk_1(sK3,sK1,sK2) ),
% 1.67/0.94      inference(cnf_transformation,[],[f60]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_253,plain,
% 1.67/0.94      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.67/0.94      | ~ v5_pre_topc(X0,X1,X2)
% 1.67/0.94      | ~ v4_tex_2(X2,X1)
% 1.67/0.94      | ~ m1_pre_topc(X2,X1)
% 1.67/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.67/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.67/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.67/0.94      | ~ v3_tdlat_3(X1)
% 1.67/0.94      | ~ v1_funct_1(X0)
% 1.67/0.94      | v2_struct_0(X1)
% 1.67/0.94      | v2_struct_0(X2)
% 1.67/0.94      | ~ l1_pre_topc(X1)
% 1.67/0.94      | ~ v2_pre_topc(X1)
% 1.67/0.94      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 1.67/0.94      | sK3 != X0
% 1.67/0.94      | sK2 != X2
% 1.67/0.94      | sK1 != X1 ),
% 1.67/0.94      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_254,plain,
% 1.67/0.94      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 1.67/0.94      | ~ v5_pre_topc(sK3,sK1,sK2)
% 1.67/0.94      | ~ v4_tex_2(sK2,sK1)
% 1.67/0.94      | ~ m1_pre_topc(sK2,sK1)
% 1.67/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.67/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.67/0.94      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 1.67/0.94      | ~ v3_tdlat_3(sK1)
% 1.67/0.94      | ~ v1_funct_1(sK3)
% 1.67/0.94      | v2_struct_0(sK2)
% 1.67/0.94      | v2_struct_0(sK1)
% 1.67/0.94      | ~ l1_pre_topc(sK1)
% 1.67/0.94      | ~ v2_pre_topc(sK1)
% 1.67/0.94      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 1.67/0.94      inference(unflattening,[status(thm)],[c_253]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_24,negated_conjecture,
% 1.67/0.94      ( ~ v2_struct_0(sK1) ),
% 1.67/0.94      inference(cnf_transformation,[],[f49]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_22,negated_conjecture,
% 1.67/0.94      ( v3_tdlat_3(sK1) ),
% 1.67/0.94      inference(cnf_transformation,[],[f51]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_19,negated_conjecture,
% 1.67/0.94      ( v4_tex_2(sK2,sK1) ),
% 1.67/0.94      inference(cnf_transformation,[],[f54]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_17,negated_conjecture,
% 1.67/0.94      ( v1_funct_1(sK3) ),
% 1.67/0.94      inference(cnf_transformation,[],[f56]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_16,negated_conjecture,
% 1.67/0.94      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 1.67/0.94      inference(cnf_transformation,[],[f57]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_15,negated_conjecture,
% 1.67/0.94      ( v5_pre_topc(sK3,sK1,sK2) ),
% 1.67/0.94      inference(cnf_transformation,[],[f58]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_258,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.67/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.67/0.94      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 1.67/0.94      inference(global_propositional_subsumption,
% 1.67/0.94                [status(thm)],
% 1.67/0.94                [c_254,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_16,c_15,
% 1.67/0.94                 c_14]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_259,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.67/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.67/0.94      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0) = k2_pre_topc(sK1,X0) ),
% 1.67/0.94      inference(renaming,[status(thm)],[c_258]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_465,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.67/0.94      | ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.67/0.94      | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_53) = k2_pre_topc(sK1,X0_53) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_259]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_721,plain,
% 1.67/0.94      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,X0_53) = k2_pre_topc(sK1,X0_53)
% 1.67/0.94      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.67/0.94      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1211,plain,
% 1.67/0.94      ( k2_pre_topc(sK1,X0_53) = k10_relat_1(sK3,X0_53)
% 1.67/0.94      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.67/0.94      | m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.67/0.94      inference(demodulation,[status(thm)],[c_1041,c_721]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1801,plain,
% 1.67/0.94      ( k2_pre_topc(sK1,k2_tarski(sK5,sK5)) = k10_relat_1(sK3,k2_tarski(sK5,sK5))
% 1.67/0.94      | m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.67/0.94      inference(superposition,[status(thm)],[c_1796,c_1211]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_11,negated_conjecture,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.67/0.94      inference(cnf_transformation,[],[f62]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_468,negated_conjecture,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_11]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_718,plain,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1092,plain,
% 1.67/0.94      ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5)
% 1.67/0.94      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.67/0.94      inference(superposition,[status(thm)],[c_718,c_717]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_25,plain,
% 1.67/0.94      ( v2_struct_0(sK1) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_26,plain,
% 1.67/0.94      ( v2_pre_topc(sK1) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_51,plain,
% 1.67/0.94      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 1.67/0.94      | v2_struct_0(X0) = iProver_top
% 1.67/0.94      | l1_pre_topc(X0) != iProver_top
% 1.67/0.94      | v2_pre_topc(X0) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_53,plain,
% 1.67/0.94      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.67/0.94      | v2_struct_0(sK1) = iProver_top
% 1.67/0.94      | l1_pre_topc(sK1) != iProver_top
% 1.67/0.94      | v2_pre_topc(sK1) != iProver_top ),
% 1.67/0.94      inference(instantiation,[status(thm)],[c_51]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_54,plain,
% 1.67/0.94      ( v2_struct_0(X0) = iProver_top
% 1.67/0.94      | l1_pre_topc(X0) != iProver_top
% 1.67/0.94      | v2_pre_topc(X0) != iProver_top
% 1.67/0.94      | v1_xboole_0(sK0(X0)) != iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_56,plain,
% 1.67/0.94      ( v2_struct_0(sK1) = iProver_top
% 1.67/0.94      | l1_pre_topc(sK1) != iProver_top
% 1.67/0.94      | v2_pre_topc(sK1) != iProver_top
% 1.67/0.94      | v1_xboole_0(sK0(sK1)) != iProver_top ),
% 1.67/0.94      inference(instantiation,[status(thm)],[c_54]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_884,plain,
% 1.67/0.94      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.67/0.94      | v1_xboole_0(X0_53)
% 1.67/0.94      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.67/0.94      inference(instantiation,[status(thm)],[c_473]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_982,plain,
% 1.67/0.94      ( ~ m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.67/0.94      | ~ v1_xboole_0(u1_struct_0(sK1))
% 1.67/0.94      | v1_xboole_0(sK0(sK1)) ),
% 1.67/0.94      inference(instantiation,[status(thm)],[c_884]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_983,plain,
% 1.67/0.94      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.67/0.94      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top
% 1.67/0.94      | v1_xboole_0(sK0(sK1)) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1269,plain,
% 1.67/0.94      ( k6_domain_1(u1_struct_0(sK1),sK5) = k2_tarski(sK5,sK5) ),
% 1.67/0.94      inference(global_propositional_subsumption,
% 1.67/0.94                [status(thm)],
% 1.67/0.94                [c_1092,c_25,c_26,c_28,c_53,c_56,c_983]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_10,negated_conjecture,
% 1.67/0.94      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 1.67/0.94      inference(cnf_transformation,[],[f66]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_469,negated_conjecture,
% 1.67/0.94      ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) ),
% 1.67/0.94      inference(subtyping,[status(esa)],[c_10]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1210,plain,
% 1.67/0.94      ( k2_pre_topc(sK1,k6_domain_1(u1_struct_0(sK1),sK5)) != k10_relat_1(sK3,k6_domain_1(u1_struct_0(sK2),sK5)) ),
% 1.67/0.94      inference(demodulation,[status(thm)],[c_1041,c_469]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1272,plain,
% 1.67/0.94      ( k10_relat_1(sK3,k6_domain_1(u1_struct_0(sK2),sK5)) != k2_pre_topc(sK1,k2_tarski(sK5,sK5)) ),
% 1.67/0.94      inference(demodulation,[status(thm)],[c_1269,c_1210]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1330,plain,
% 1.67/0.94      ( k2_pre_topc(sK1,k2_tarski(sK5,sK5)) != k10_relat_1(sK3,k2_tarski(sK5,sK5)) ),
% 1.67/0.94      inference(demodulation,[status(thm)],[c_1327,c_1272]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_1273,plain,
% 1.67/0.94      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 1.67/0.94      | m1_subset_1(sK5,u1_struct_0(sK1)) != iProver_top
% 1.67/0.94      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 1.67/0.94      inference(superposition,[status(thm)],[c_1269,c_716]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(c_38,plain,
% 1.67/0.94      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 1.67/0.94      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.67/0.94  
% 1.67/0.94  cnf(contradiction,plain,
% 1.67/0.94      ( $false ),
% 1.67/0.94      inference(minisat,
% 1.67/0.94                [status(thm)],
% 1.67/0.94                [c_1801,c_1330,c_1273,c_983,c_56,c_53,c_38,c_28,c_26,
% 1.67/0.94                 c_25]) ).
% 1.67/0.94  
% 1.67/0.94  
% 1.67/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 1.67/0.94  
% 1.67/0.94  ------                               Statistics
% 1.67/0.94  
% 1.67/0.94  ------ General
% 1.67/0.94  
% 1.67/0.94  abstr_ref_over_cycles:                  0
% 1.67/0.94  abstr_ref_under_cycles:                 0
% 1.67/0.94  gc_basic_clause_elim:                   0
% 1.67/0.94  forced_gc_time:                         0
% 1.67/0.94  parsing_time:                           0.01
% 1.67/0.94  unif_index_cands_time:                  0.
% 1.67/0.94  unif_index_add_time:                    0.
% 1.67/0.94  orderings_time:                         0.
% 1.67/0.94  out_proof_time:                         0.01
% 1.67/0.94  total_time:                             0.09
% 1.67/0.94  num_of_symbols:                         59
% 1.67/0.94  num_of_terms:                           1687
% 1.67/0.94  
% 1.67/0.94  ------ Preprocessing
% 1.67/0.94  
% 1.67/0.94  num_of_splits:                          0
% 1.67/0.94  num_of_split_atoms:                     0
% 1.67/0.94  num_of_reused_defs:                     0
% 1.67/0.94  num_eq_ax_congr_red:                    16
% 1.67/0.94  num_of_sem_filtered_clauses:            1
% 1.67/0.94  num_of_subtypes:                        3
% 1.67/0.94  monotx_restored_types:                  0
% 1.67/0.94  sat_num_of_epr_types:                   0
% 1.67/0.94  sat_num_of_non_cyclic_types:            0
% 1.67/0.94  sat_guarded_non_collapsed_types:        0
% 1.67/0.94  num_pure_diseq_elim:                    0
% 1.67/0.94  simp_replaced_by:                       0
% 1.67/0.94  res_preprocessed:                       90
% 1.67/0.94  prep_upred:                             0
% 1.67/0.94  prep_unflattend:                        13
% 1.67/0.94  smt_new_axioms:                         0
% 1.67/0.94  pred_elim_cands:                        2
% 1.67/0.94  pred_elim:                              10
% 1.67/0.94  pred_elim_cl:                           11
% 1.67/0.94  pred_elim_cycles:                       12
% 1.67/0.94  merged_defs:                            0
% 1.67/0.94  merged_defs_ncl:                        0
% 1.67/0.94  bin_hyper_res:                          0
% 1.67/0.94  prep_cycles:                            4
% 1.67/0.94  pred_elim_time:                         0.003
% 1.67/0.94  splitting_time:                         0.
% 1.67/0.94  sem_filter_time:                        0.
% 1.67/0.94  monotx_time:                            0.
% 1.67/0.94  subtype_inf_time:                       0.
% 1.67/0.94  
% 1.67/0.94  ------ Problem properties
% 1.67/0.94  
% 1.67/0.94  clauses:                                14
% 1.67/0.94  conjectures:                            4
% 1.67/0.94  epr:                                    0
% 1.67/0.94  horn:                                   12
% 1.67/0.94  ground:                                 9
% 1.67/0.94  unary:                                  9
% 1.67/0.94  binary:                                 1
% 1.67/0.94  lits:                                   23
% 1.67/0.94  lits_eq:                                4
% 1.67/0.94  fd_pure:                                0
% 1.67/0.94  fd_pseudo:                              0
% 1.67/0.94  fd_cond:                                0
% 1.67/0.94  fd_pseudo_cond:                         0
% 1.67/0.94  ac_symbols:                             0
% 1.67/0.94  
% 1.67/0.94  ------ Propositional Solver
% 1.67/0.94  
% 1.67/0.94  prop_solver_calls:                      26
% 1.67/0.94  prop_fast_solver_calls:                 482
% 1.67/0.94  smt_solver_calls:                       0
% 1.67/0.94  smt_fast_solver_calls:                  0
% 1.67/0.94  prop_num_of_clauses:                    605
% 1.67/0.94  prop_preprocess_simplified:             2373
% 1.67/0.94  prop_fo_subsumed:                       32
% 1.67/0.94  prop_solver_time:                       0.
% 1.67/0.94  smt_solver_time:                        0.
% 1.67/0.94  smt_fast_solver_time:                   0.
% 1.67/0.94  prop_fast_solver_time:                  0.
% 1.67/0.94  prop_unsat_core_time:                   0.
% 1.67/0.94  
% 1.67/0.94  ------ QBF
% 1.67/0.94  
% 1.67/0.94  qbf_q_res:                              0
% 1.67/0.94  qbf_num_tautologies:                    0
% 1.67/0.94  qbf_prep_cycles:                        0
% 1.67/0.94  
% 1.67/0.94  ------ BMC1
% 1.67/0.94  
% 1.67/0.94  bmc1_current_bound:                     -1
% 1.67/0.94  bmc1_last_solved_bound:                 -1
% 1.67/0.94  bmc1_unsat_core_size:                   -1
% 1.67/0.94  bmc1_unsat_core_parents_size:           -1
% 1.67/0.94  bmc1_merge_next_fun:                    0
% 1.67/0.94  bmc1_unsat_core_clauses_time:           0.
% 1.67/0.94  
% 1.67/0.94  ------ Instantiation
% 1.67/0.94  
% 1.67/0.94  inst_num_of_clauses:                    195
% 1.67/0.94  inst_num_in_passive:                    34
% 1.67/0.94  inst_num_in_active:                     139
% 1.67/0.94  inst_num_in_unprocessed:                23
% 1.67/0.94  inst_num_of_loops:                      150
% 1.67/0.94  inst_num_of_learning_restarts:          0
% 1.67/0.94  inst_num_moves_active_passive:          7
% 1.67/0.94  inst_lit_activity:                      0
% 1.67/0.94  inst_lit_activity_moves:                0
% 1.67/0.94  inst_num_tautologies:                   0
% 1.67/0.94  inst_num_prop_implied:                  0
% 1.67/0.94  inst_num_existing_simplified:           0
% 1.67/0.94  inst_num_eq_res_simplified:             0
% 1.67/0.94  inst_num_child_elim:                    0
% 1.67/0.94  inst_num_of_dismatching_blockings:      12
% 1.67/0.94  inst_num_of_non_proper_insts:           188
% 1.67/0.94  inst_num_of_duplicates:                 0
% 1.67/0.94  inst_inst_num_from_inst_to_res:         0
% 1.67/0.94  inst_dismatching_checking_time:         0.
% 1.67/0.94  
% 1.67/0.94  ------ Resolution
% 1.67/0.94  
% 1.67/0.94  res_num_of_clauses:                     0
% 1.67/0.94  res_num_in_passive:                     0
% 1.67/0.94  res_num_in_active:                      0
% 1.67/0.94  res_num_of_loops:                       94
% 1.67/0.94  res_forward_subset_subsumed:            32
% 1.67/0.94  res_backward_subset_subsumed:           4
% 1.67/0.94  res_forward_subsumed:                   0
% 1.67/0.94  res_backward_subsumed:                  0
% 1.67/0.94  res_forward_subsumption_resolution:     0
% 1.67/0.94  res_backward_subsumption_resolution:    0
% 1.67/0.94  res_clause_to_clause_subsumption:       38
% 1.67/0.94  res_orphan_elimination:                 0
% 1.67/0.94  res_tautology_del:                      32
% 1.67/0.94  res_num_eq_res_simplified:              0
% 1.67/0.94  res_num_sel_changes:                    0
% 1.67/0.94  res_moves_from_active_to_pass:          0
% 1.67/0.94  
% 1.67/0.94  ------ Superposition
% 1.67/0.94  
% 1.67/0.94  sup_time_total:                         0.
% 1.67/0.94  sup_time_generating:                    0.
% 1.67/0.94  sup_time_sim_full:                      0.
% 1.67/0.94  sup_time_sim_immed:                     0.
% 1.67/0.94  
% 1.67/0.94  sup_num_of_clauses:                     33
% 1.67/0.94  sup_num_in_active:                      25
% 1.67/0.94  sup_num_in_passive:                     8
% 1.67/0.94  sup_num_of_loops:                       28
% 1.67/0.94  sup_fw_superposition:                   11
% 1.67/0.94  sup_bw_superposition:                   13
% 1.67/0.94  sup_immediate_simplified:               1
% 1.67/0.94  sup_given_eliminated:                   0
% 1.67/0.94  comparisons_done:                       0
% 1.67/0.94  comparisons_avoided:                    0
% 1.67/0.94  
% 1.67/0.94  ------ Simplifications
% 1.67/0.94  
% 1.67/0.94  
% 1.67/0.94  sim_fw_subset_subsumed:                 2
% 1.67/0.94  sim_bw_subset_subsumed:                 0
% 1.67/0.94  sim_fw_subsumed:                        0
% 1.67/0.94  sim_bw_subsumed:                        0
% 1.67/0.94  sim_fw_subsumption_res:                 0
% 1.67/0.94  sim_bw_subsumption_res:                 0
% 1.67/0.94  sim_tautology_del:                      1
% 1.67/0.94  sim_eq_tautology_del:                   0
% 1.67/0.94  sim_eq_res_simp:                        0
% 1.67/0.94  sim_fw_demodulated:                     0
% 1.67/0.94  sim_bw_demodulated:                     4
% 1.67/0.94  sim_light_normalised:                   0
% 1.67/0.94  sim_joinable_taut:                      0
% 1.67/0.94  sim_joinable_simp:                      0
% 1.67/0.94  sim_ac_normalised:                      0
% 1.67/0.94  sim_smt_subsumption:                    0
% 1.67/0.94  
%------------------------------------------------------------------------------
