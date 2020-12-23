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

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  191 (1980 expanded)
%              Number of clauses        :   97 ( 341 expanded)
%              Number of leaves         :   25 ( 787 expanded)
%              Depth                    :   19
%              Number of atoms          :  758 (20763 expanded)
%              Number of equality atoms :  142 (3616 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f63])).

fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK7))
        & sK7 = X3
        & m1_subset_1(sK7,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f46,f62,f61,f60,f59,f58])).

fof(f106,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f63])).

fof(f116,plain,(
    m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(definition_unfolding,[],[f104,f106])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f74,f108])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f109])).

fof(f111,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f110])).

fof(f112,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f111])).

fof(f113,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f112])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f84,f113])).

fof(f92,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f93,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f95,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( v3_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_tdlat_3(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v3_tex_2(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f56])).

fof(f90,plain,(
    ! [X0] :
      ( v3_tex_2(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f105,plain,(
    m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f107,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(cnf_transformation,[],[f63])).

fof(f115,plain,(
    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(definition_unfolding,[],[f107,f106])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f22,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
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
    inference(equality_resolution,[],[f91])).

fof(f103,plain,(
    v3_borsuk_1(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    v4_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1503,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1505,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2299,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7)
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1503,c_1505])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_33,negated_conjecture,
    ( v3_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X1)
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_495,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | sK4 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_496,plain,
    ( v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v3_tdlat_3(sK4)
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_535,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_536,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_17,plain,
    ( ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_18,plain,
    ( v3_tex_2(sK2(X0),X0)
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_xboole_0(X0)
    | X2 != X1
    | sK2(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_18])).

cnf(c_438,plain,
    ( ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_19,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_442,plain,
    ( v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_19])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_546,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_547,plain,
    ( ~ l1_pre_topc(sK3)
    | v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_549,plain,
    ( v2_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_547,c_34,c_32])).

cnf(c_594,plain,
    ( v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_442,c_549])).

cnf(c_595,plain,
    ( v2_struct_0(sK4)
    | ~ v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_605,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_549])).

cnf(c_606,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_tdlat_3(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_608,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_35,c_34,c_33,c_32,c_31,c_496,c_536])).

cnf(c_1494,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1507,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1928,plain,
    ( r1_tarski(sK2(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1507])).

cnf(c_1940,plain,
    ( r1_tarski(sK2(sK4),u1_struct_0(sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1928])).

cnf(c_2044,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_245,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_246,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_310,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_246])).

cnf(c_1723,plain,
    ( ~ r1_tarski(sK2(sK4),X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_2104,plain,
    ( ~ r1_tarski(sK2(sK4),u1_struct_0(sK4))
    | v1_xboole_0(sK2(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_2509,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2299,c_35,c_34,c_33,c_32,c_31,c_23,c_496,c_536,c_595,c_1940,c_2044,c_2104])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1504,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2298,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1505])).

cnf(c_54,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_440,plain,
    ( ~ m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v1_xboole_0(sK2(sK3)) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_583,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_584,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_586,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_35,c_34,c_33,c_32,c_54])).

cnf(c_1496,plain,
    ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1926,plain,
    ( r1_tarski(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1507])).

cnf(c_1938,plain,
    ( r1_tarski(sK2(sK3),u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1926])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1718,plain,
    ( ~ r1_tarski(sK2(sK3),X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK3)) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_2080,plain,
    ( ~ r1_tarski(sK2(sK3),u1_struct_0(sK3))
    | v1_xboole_0(sK2(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1718])).

cnf(c_2505,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_35,c_34,c_33,c_32,c_22,c_54,c_440,c_1938,c_2041,c_2080])).

cnf(c_2511,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
    inference(light_normalisation,[status(thm)],[c_2509,c_2505])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1506,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2768,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2511,c_1506])).

cnf(c_21,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2513,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK3),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(demodulation,[status(thm)],[c_2511,c_21])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | sK4 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_517])).

cnf(c_522,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_518,c_32])).

cnf(c_523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_522])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f117])).

cnf(c_24,negated_conjecture,
    ( v3_borsuk_1(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v5_pre_topc(X0,X1,X2)
    | ~ v4_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_funct_1(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_471,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ v5_pre_topc(sK5,sK3,sK4)
    | ~ v4_tex_2(sK4,sK3)
    | ~ m1_pre_topc(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
    | ~ v1_funct_1(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | ~ v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_30,negated_conjecture,
    ( v4_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_26,negated_conjecture,
    ( v5_pre_topc(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_475,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,c_25])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(renaming,[status(thm)],[c_475])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_523,c_476])).

cnf(c_2409,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7),k1_zfmisc_1(u1_struct_0(sK4)))
    | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_2410,plain,
    ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2409])).

cnf(c_2122,plain,
    ( r1_tarski(sK2(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(sK2(sK4)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_596,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v3_tdlat_3(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v1_xboole_0(sK2(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_537,plain,
    ( l1_pre_topc(sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_497,plain,
    ( v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v3_tdlat_3(sK4) = iProver_top
    | v3_tdlat_3(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_40,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_38,plain,
    ( v3_tdlat_3(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_36,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2768,c_2513,c_2410,c_2122,c_1928,c_596,c_537,c_497,c_48,c_40,c_39,c_38,c_37,c_36])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.87/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.00  
% 1.87/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/1.00  
% 1.87/1.00  ------  iProver source info
% 1.87/1.00  
% 1.87/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.87/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/1.00  git: non_committed_changes: false
% 1.87/1.00  git: last_make_outside_of_git: false
% 1.87/1.00  
% 1.87/1.00  ------ 
% 1.87/1.00  
% 1.87/1.00  ------ Input Options
% 1.87/1.00  
% 1.87/1.00  --out_options                           all
% 1.87/1.00  --tptp_safe_out                         true
% 1.87/1.00  --problem_path                          ""
% 1.87/1.00  --include_path                          ""
% 1.87/1.00  --clausifier                            res/vclausify_rel
% 1.87/1.00  --clausifier_options                    --mode clausify
% 1.87/1.00  --stdin                                 false
% 1.87/1.00  --stats_out                             all
% 1.87/1.00  
% 1.87/1.00  ------ General Options
% 1.87/1.00  
% 1.87/1.00  --fof                                   false
% 1.87/1.00  --time_out_real                         305.
% 1.87/1.00  --time_out_virtual                      -1.
% 1.87/1.00  --symbol_type_check                     false
% 1.87/1.00  --clausify_out                          false
% 1.87/1.00  --sig_cnt_out                           false
% 1.87/1.00  --trig_cnt_out                          false
% 1.87/1.00  --trig_cnt_out_tolerance                1.
% 1.87/1.00  --trig_cnt_out_sk_spl                   false
% 1.87/1.00  --abstr_cl_out                          false
% 1.87/1.00  
% 1.87/1.00  ------ Global Options
% 1.87/1.00  
% 1.87/1.00  --schedule                              default
% 1.87/1.00  --add_important_lit                     false
% 1.87/1.00  --prop_solver_per_cl                    1000
% 1.87/1.00  --min_unsat_core                        false
% 1.87/1.00  --soft_assumptions                      false
% 1.87/1.00  --soft_lemma_size                       3
% 1.87/1.00  --prop_impl_unit_size                   0
% 1.87/1.00  --prop_impl_unit                        []
% 1.87/1.00  --share_sel_clauses                     true
% 1.87/1.00  --reset_solvers                         false
% 1.87/1.00  --bc_imp_inh                            [conj_cone]
% 1.87/1.00  --conj_cone_tolerance                   3.
% 1.87/1.00  --extra_neg_conj                        none
% 1.87/1.00  --large_theory_mode                     true
% 1.87/1.00  --prolific_symb_bound                   200
% 1.87/1.00  --lt_threshold                          2000
% 1.87/1.00  --clause_weak_htbl                      true
% 1.87/1.00  --gc_record_bc_elim                     false
% 1.87/1.00  
% 1.87/1.00  ------ Preprocessing Options
% 1.87/1.00  
% 1.87/1.00  --preprocessing_flag                    true
% 1.87/1.00  --time_out_prep_mult                    0.1
% 1.87/1.00  --splitting_mode                        input
% 1.87/1.00  --splitting_grd                         true
% 1.87/1.00  --splitting_cvd                         false
% 1.87/1.00  --splitting_cvd_svl                     false
% 1.87/1.00  --splitting_nvd                         32
% 1.87/1.00  --sub_typing                            true
% 1.87/1.00  --prep_gs_sim                           true
% 1.87/1.00  --prep_unflatten                        true
% 1.87/1.00  --prep_res_sim                          true
% 1.87/1.00  --prep_upred                            true
% 1.87/1.00  --prep_sem_filter                       exhaustive
% 1.87/1.00  --prep_sem_filter_out                   false
% 1.87/1.00  --pred_elim                             true
% 1.87/1.00  --res_sim_input                         true
% 1.87/1.00  --eq_ax_congr_red                       true
% 1.87/1.00  --pure_diseq_elim                       true
% 1.87/1.00  --brand_transform                       false
% 1.87/1.00  --non_eq_to_eq                          false
% 1.87/1.00  --prep_def_merge                        true
% 1.87/1.00  --prep_def_merge_prop_impl              false
% 1.87/1.00  --prep_def_merge_mbd                    true
% 1.87/1.00  --prep_def_merge_tr_red                 false
% 1.87/1.00  --prep_def_merge_tr_cl                  false
% 1.87/1.00  --smt_preprocessing                     true
% 1.87/1.00  --smt_ac_axioms                         fast
% 1.87/1.00  --preprocessed_out                      false
% 1.87/1.00  --preprocessed_stats                    false
% 1.87/1.00  
% 1.87/1.00  ------ Abstraction refinement Options
% 1.87/1.00  
% 1.87/1.00  --abstr_ref                             []
% 1.87/1.00  --abstr_ref_prep                        false
% 1.87/1.00  --abstr_ref_until_sat                   false
% 1.87/1.00  --abstr_ref_sig_restrict                funpre
% 1.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.00  --abstr_ref_under                       []
% 1.87/1.00  
% 1.87/1.00  ------ SAT Options
% 1.87/1.00  
% 1.87/1.00  --sat_mode                              false
% 1.87/1.00  --sat_fm_restart_options                ""
% 1.87/1.00  --sat_gr_def                            false
% 1.87/1.00  --sat_epr_types                         true
% 1.87/1.00  --sat_non_cyclic_types                  false
% 1.87/1.00  --sat_finite_models                     false
% 1.87/1.00  --sat_fm_lemmas                         false
% 1.87/1.00  --sat_fm_prep                           false
% 1.87/1.00  --sat_fm_uc_incr                        true
% 1.87/1.00  --sat_out_model                         small
% 1.87/1.00  --sat_out_clauses                       false
% 1.87/1.00  
% 1.87/1.00  ------ QBF Options
% 1.87/1.00  
% 1.87/1.00  --qbf_mode                              false
% 1.87/1.00  --qbf_elim_univ                         false
% 1.87/1.00  --qbf_dom_inst                          none
% 1.87/1.00  --qbf_dom_pre_inst                      false
% 1.87/1.00  --qbf_sk_in                             false
% 1.87/1.00  --qbf_pred_elim                         true
% 1.87/1.00  --qbf_split                             512
% 1.87/1.00  
% 1.87/1.00  ------ BMC1 Options
% 1.87/1.00  
% 1.87/1.00  --bmc1_incremental                      false
% 1.87/1.00  --bmc1_axioms                           reachable_all
% 1.87/1.00  --bmc1_min_bound                        0
% 1.87/1.00  --bmc1_max_bound                        -1
% 1.87/1.00  --bmc1_max_bound_default                -1
% 1.87/1.00  --bmc1_symbol_reachability              true
% 1.87/1.00  --bmc1_property_lemmas                  false
% 1.87/1.00  --bmc1_k_induction                      false
% 1.87/1.00  --bmc1_non_equiv_states                 false
% 1.87/1.00  --bmc1_deadlock                         false
% 1.87/1.00  --bmc1_ucm                              false
% 1.87/1.00  --bmc1_add_unsat_core                   none
% 1.87/1.00  --bmc1_unsat_core_children              false
% 1.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.00  --bmc1_out_stat                         full
% 1.87/1.00  --bmc1_ground_init                      false
% 1.87/1.00  --bmc1_pre_inst_next_state              false
% 1.87/1.00  --bmc1_pre_inst_state                   false
% 1.87/1.00  --bmc1_pre_inst_reach_state             false
% 1.87/1.00  --bmc1_out_unsat_core                   false
% 1.87/1.00  --bmc1_aig_witness_out                  false
% 1.87/1.00  --bmc1_verbose                          false
% 1.87/1.00  --bmc1_dump_clauses_tptp                false
% 1.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.00  --bmc1_dump_file                        -
% 1.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.00  --bmc1_ucm_extend_mode                  1
% 1.87/1.00  --bmc1_ucm_init_mode                    2
% 1.87/1.00  --bmc1_ucm_cone_mode                    none
% 1.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.00  --bmc1_ucm_relax_model                  4
% 1.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.00  --bmc1_ucm_layered_model                none
% 1.87/1.00  --bmc1_ucm_max_lemma_size               10
% 1.87/1.00  
% 1.87/1.00  ------ AIG Options
% 1.87/1.00  
% 1.87/1.00  --aig_mode                              false
% 1.87/1.00  
% 1.87/1.00  ------ Instantiation Options
% 1.87/1.00  
% 1.87/1.00  --instantiation_flag                    true
% 1.87/1.00  --inst_sos_flag                         false
% 1.87/1.00  --inst_sos_phase                        true
% 1.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.00  --inst_lit_sel_side                     num_symb
% 1.87/1.00  --inst_solver_per_active                1400
% 1.87/1.00  --inst_solver_calls_frac                1.
% 1.87/1.00  --inst_passive_queue_type               priority_queues
% 1.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.00  --inst_passive_queues_freq              [25;2]
% 1.87/1.00  --inst_dismatching                      true
% 1.87/1.00  --inst_eager_unprocessed_to_passive     true
% 1.87/1.00  --inst_prop_sim_given                   true
% 1.87/1.00  --inst_prop_sim_new                     false
% 1.87/1.00  --inst_subs_new                         false
% 1.87/1.00  --inst_eq_res_simp                      false
% 1.87/1.00  --inst_subs_given                       false
% 1.87/1.00  --inst_orphan_elimination               true
% 1.87/1.00  --inst_learning_loop_flag               true
% 1.87/1.00  --inst_learning_start                   3000
% 1.87/1.00  --inst_learning_factor                  2
% 1.87/1.00  --inst_start_prop_sim_after_learn       3
% 1.87/1.00  --inst_sel_renew                        solver
% 1.87/1.00  --inst_lit_activity_flag                true
% 1.87/1.00  --inst_restr_to_given                   false
% 1.87/1.00  --inst_activity_threshold               500
% 1.87/1.00  --inst_out_proof                        true
% 1.87/1.00  
% 1.87/1.00  ------ Resolution Options
% 1.87/1.00  
% 1.87/1.00  --resolution_flag                       true
% 1.87/1.00  --res_lit_sel                           adaptive
% 1.87/1.00  --res_lit_sel_side                      none
% 1.87/1.00  --res_ordering                          kbo
% 1.87/1.00  --res_to_prop_solver                    active
% 1.87/1.00  --res_prop_simpl_new                    false
% 1.87/1.00  --res_prop_simpl_given                  true
% 1.87/1.00  --res_passive_queue_type                priority_queues
% 1.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.00  --res_passive_queues_freq               [15;5]
% 1.87/1.00  --res_forward_subs                      full
% 1.87/1.00  --res_backward_subs                     full
% 1.87/1.00  --res_forward_subs_resolution           true
% 1.87/1.00  --res_backward_subs_resolution          true
% 1.87/1.00  --res_orphan_elimination                true
% 1.87/1.00  --res_time_limit                        2.
% 1.87/1.00  --res_out_proof                         true
% 1.87/1.00  
% 1.87/1.00  ------ Superposition Options
% 1.87/1.00  
% 1.87/1.00  --superposition_flag                    true
% 1.87/1.00  --sup_passive_queue_type                priority_queues
% 1.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.00  --demod_completeness_check              fast
% 1.87/1.00  --demod_use_ground                      true
% 1.87/1.00  --sup_to_prop_solver                    passive
% 1.87/1.00  --sup_prop_simpl_new                    true
% 1.87/1.00  --sup_prop_simpl_given                  true
% 1.87/1.00  --sup_fun_splitting                     false
% 1.87/1.00  --sup_smt_interval                      50000
% 1.87/1.00  
% 1.87/1.00  ------ Superposition Simplification Setup
% 1.87/1.00  
% 1.87/1.00  --sup_indices_passive                   []
% 1.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.00  --sup_full_bw                           [BwDemod]
% 1.87/1.00  --sup_immed_triv                        [TrivRules]
% 1.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.00  --sup_immed_bw_main                     []
% 1.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.00  
% 1.87/1.00  ------ Combination Options
% 1.87/1.00  
% 1.87/1.00  --comb_res_mult                         3
% 1.87/1.00  --comb_sup_mult                         2
% 1.87/1.00  --comb_inst_mult                        10
% 1.87/1.00  
% 1.87/1.00  ------ Debug Options
% 1.87/1.00  
% 1.87/1.00  --dbg_backtrace                         false
% 1.87/1.00  --dbg_dump_prop_clauses                 false
% 1.87/1.00  --dbg_dump_prop_clauses_file            -
% 1.87/1.00  --dbg_out_stat                          false
% 1.87/1.00  ------ Parsing...
% 1.87/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/1.00  
% 1.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.87/1.00  
% 1.87/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/1.00  
% 1.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/1.00  ------ Proving...
% 1.87/1.00  ------ Problem Properties 
% 1.87/1.00  
% 1.87/1.00  
% 1.87/1.00  clauses                                 22
% 1.87/1.00  conjectures                             4
% 1.87/1.00  EPR                                     4
% 1.87/1.00  Horn                                    18
% 1.87/1.00  unary                                   9
% 1.87/1.00  binary                                  8
% 1.87/1.00  lits                                    40
% 1.87/1.00  lits eq                                 4
% 1.87/1.00  fd_pure                                 0
% 1.87/1.00  fd_pseudo                               0
% 1.87/1.00  fd_cond                                 0
% 1.87/1.00  fd_pseudo_cond                          1
% 1.87/1.00  AC symbols                              0
% 1.87/1.00  
% 1.87/1.00  ------ Schedule dynamic 5 is on 
% 1.87/1.00  
% 1.87/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.87/1.00  
% 1.87/1.00  
% 1.87/1.00  ------ 
% 1.87/1.00  Current options:
% 1.87/1.00  ------ 
% 1.87/1.00  
% 1.87/1.00  ------ Input Options
% 1.87/1.00  
% 1.87/1.00  --out_options                           all
% 1.87/1.00  --tptp_safe_out                         true
% 1.87/1.00  --problem_path                          ""
% 1.87/1.00  --include_path                          ""
% 1.87/1.00  --clausifier                            res/vclausify_rel
% 1.87/1.00  --clausifier_options                    --mode clausify
% 1.87/1.00  --stdin                                 false
% 1.87/1.00  --stats_out                             all
% 1.87/1.00  
% 1.87/1.00  ------ General Options
% 1.87/1.00  
% 1.87/1.00  --fof                                   false
% 1.87/1.00  --time_out_real                         305.
% 1.87/1.00  --time_out_virtual                      -1.
% 1.87/1.00  --symbol_type_check                     false
% 1.87/1.00  --clausify_out                          false
% 1.87/1.00  --sig_cnt_out                           false
% 1.87/1.00  --trig_cnt_out                          false
% 1.87/1.00  --trig_cnt_out_tolerance                1.
% 1.87/1.00  --trig_cnt_out_sk_spl                   false
% 1.87/1.00  --abstr_cl_out                          false
% 1.87/1.00  
% 1.87/1.00  ------ Global Options
% 1.87/1.00  
% 1.87/1.00  --schedule                              default
% 1.87/1.00  --add_important_lit                     false
% 1.87/1.00  --prop_solver_per_cl                    1000
% 1.87/1.00  --min_unsat_core                        false
% 1.87/1.00  --soft_assumptions                      false
% 1.87/1.00  --soft_lemma_size                       3
% 1.87/1.00  --prop_impl_unit_size                   0
% 1.87/1.00  --prop_impl_unit                        []
% 1.87/1.00  --share_sel_clauses                     true
% 1.87/1.00  --reset_solvers                         false
% 1.87/1.00  --bc_imp_inh                            [conj_cone]
% 1.87/1.00  --conj_cone_tolerance                   3.
% 1.87/1.00  --extra_neg_conj                        none
% 1.87/1.00  --large_theory_mode                     true
% 1.87/1.00  --prolific_symb_bound                   200
% 1.87/1.00  --lt_threshold                          2000
% 1.87/1.00  --clause_weak_htbl                      true
% 1.87/1.00  --gc_record_bc_elim                     false
% 1.87/1.00  
% 1.87/1.00  ------ Preprocessing Options
% 1.87/1.00  
% 1.87/1.00  --preprocessing_flag                    true
% 1.87/1.00  --time_out_prep_mult                    0.1
% 1.87/1.00  --splitting_mode                        input
% 1.87/1.00  --splitting_grd                         true
% 1.87/1.00  --splitting_cvd                         false
% 1.87/1.00  --splitting_cvd_svl                     false
% 1.87/1.00  --splitting_nvd                         32
% 1.87/1.00  --sub_typing                            true
% 1.87/1.00  --prep_gs_sim                           true
% 1.87/1.00  --prep_unflatten                        true
% 1.87/1.00  --prep_res_sim                          true
% 1.87/1.00  --prep_upred                            true
% 1.87/1.00  --prep_sem_filter                       exhaustive
% 1.87/1.00  --prep_sem_filter_out                   false
% 1.87/1.00  --pred_elim                             true
% 1.87/1.00  --res_sim_input                         true
% 1.87/1.00  --eq_ax_congr_red                       true
% 1.87/1.00  --pure_diseq_elim                       true
% 1.87/1.00  --brand_transform                       false
% 1.87/1.00  --non_eq_to_eq                          false
% 1.87/1.00  --prep_def_merge                        true
% 1.87/1.00  --prep_def_merge_prop_impl              false
% 1.87/1.00  --prep_def_merge_mbd                    true
% 1.87/1.00  --prep_def_merge_tr_red                 false
% 1.87/1.00  --prep_def_merge_tr_cl                  false
% 1.87/1.00  --smt_preprocessing                     true
% 1.87/1.00  --smt_ac_axioms                         fast
% 1.87/1.00  --preprocessed_out                      false
% 1.87/1.00  --preprocessed_stats                    false
% 1.87/1.00  
% 1.87/1.00  ------ Abstraction refinement Options
% 1.87/1.00  
% 1.87/1.00  --abstr_ref                             []
% 1.87/1.00  --abstr_ref_prep                        false
% 1.87/1.00  --abstr_ref_until_sat                   false
% 1.87/1.00  --abstr_ref_sig_restrict                funpre
% 1.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/1.00  --abstr_ref_under                       []
% 1.87/1.00  
% 1.87/1.00  ------ SAT Options
% 1.87/1.00  
% 1.87/1.00  --sat_mode                              false
% 1.87/1.00  --sat_fm_restart_options                ""
% 1.87/1.00  --sat_gr_def                            false
% 1.87/1.00  --sat_epr_types                         true
% 1.87/1.00  --sat_non_cyclic_types                  false
% 1.87/1.00  --sat_finite_models                     false
% 1.87/1.00  --sat_fm_lemmas                         false
% 1.87/1.00  --sat_fm_prep                           false
% 1.87/1.00  --sat_fm_uc_incr                        true
% 1.87/1.00  --sat_out_model                         small
% 1.87/1.00  --sat_out_clauses                       false
% 1.87/1.00  
% 1.87/1.00  ------ QBF Options
% 1.87/1.00  
% 1.87/1.00  --qbf_mode                              false
% 1.87/1.00  --qbf_elim_univ                         false
% 1.87/1.00  --qbf_dom_inst                          none
% 1.87/1.00  --qbf_dom_pre_inst                      false
% 1.87/1.00  --qbf_sk_in                             false
% 1.87/1.00  --qbf_pred_elim                         true
% 1.87/1.00  --qbf_split                             512
% 1.87/1.00  
% 1.87/1.00  ------ BMC1 Options
% 1.87/1.00  
% 1.87/1.00  --bmc1_incremental                      false
% 1.87/1.00  --bmc1_axioms                           reachable_all
% 1.87/1.00  --bmc1_min_bound                        0
% 1.87/1.00  --bmc1_max_bound                        -1
% 1.87/1.00  --bmc1_max_bound_default                -1
% 1.87/1.00  --bmc1_symbol_reachability              true
% 1.87/1.00  --bmc1_property_lemmas                  false
% 1.87/1.00  --bmc1_k_induction                      false
% 1.87/1.00  --bmc1_non_equiv_states                 false
% 1.87/1.00  --bmc1_deadlock                         false
% 1.87/1.00  --bmc1_ucm                              false
% 1.87/1.00  --bmc1_add_unsat_core                   none
% 1.87/1.00  --bmc1_unsat_core_children              false
% 1.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/1.00  --bmc1_out_stat                         full
% 1.87/1.00  --bmc1_ground_init                      false
% 1.87/1.00  --bmc1_pre_inst_next_state              false
% 1.87/1.00  --bmc1_pre_inst_state                   false
% 1.87/1.00  --bmc1_pre_inst_reach_state             false
% 1.87/1.00  --bmc1_out_unsat_core                   false
% 1.87/1.00  --bmc1_aig_witness_out                  false
% 1.87/1.00  --bmc1_verbose                          false
% 1.87/1.00  --bmc1_dump_clauses_tptp                false
% 1.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.87/1.00  --bmc1_dump_file                        -
% 1.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.87/1.00  --bmc1_ucm_extend_mode                  1
% 1.87/1.00  --bmc1_ucm_init_mode                    2
% 1.87/1.00  --bmc1_ucm_cone_mode                    none
% 1.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.87/1.00  --bmc1_ucm_relax_model                  4
% 1.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/1.00  --bmc1_ucm_layered_model                none
% 1.87/1.00  --bmc1_ucm_max_lemma_size               10
% 1.87/1.00  
% 1.87/1.00  ------ AIG Options
% 1.87/1.00  
% 1.87/1.00  --aig_mode                              false
% 1.87/1.00  
% 1.87/1.00  ------ Instantiation Options
% 1.87/1.00  
% 1.87/1.00  --instantiation_flag                    true
% 1.87/1.00  --inst_sos_flag                         false
% 1.87/1.00  --inst_sos_phase                        true
% 1.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/1.00  --inst_lit_sel_side                     none
% 1.87/1.00  --inst_solver_per_active                1400
% 1.87/1.00  --inst_solver_calls_frac                1.
% 1.87/1.00  --inst_passive_queue_type               priority_queues
% 1.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/1.00  --inst_passive_queues_freq              [25;2]
% 1.87/1.00  --inst_dismatching                      true
% 1.87/1.00  --inst_eager_unprocessed_to_passive     true
% 1.87/1.00  --inst_prop_sim_given                   true
% 1.87/1.00  --inst_prop_sim_new                     false
% 1.87/1.00  --inst_subs_new                         false
% 1.87/1.00  --inst_eq_res_simp                      false
% 1.87/1.00  --inst_subs_given                       false
% 1.87/1.00  --inst_orphan_elimination               true
% 1.87/1.00  --inst_learning_loop_flag               true
% 1.87/1.00  --inst_learning_start                   3000
% 1.87/1.00  --inst_learning_factor                  2
% 1.87/1.00  --inst_start_prop_sim_after_learn       3
% 1.87/1.00  --inst_sel_renew                        solver
% 1.87/1.00  --inst_lit_activity_flag                true
% 1.87/1.00  --inst_restr_to_given                   false
% 1.87/1.00  --inst_activity_threshold               500
% 1.87/1.00  --inst_out_proof                        true
% 1.87/1.00  
% 1.87/1.00  ------ Resolution Options
% 1.87/1.00  
% 1.87/1.00  --resolution_flag                       false
% 1.87/1.00  --res_lit_sel                           adaptive
% 1.87/1.00  --res_lit_sel_side                      none
% 1.87/1.00  --res_ordering                          kbo
% 1.87/1.00  --res_to_prop_solver                    active
% 1.87/1.00  --res_prop_simpl_new                    false
% 1.87/1.00  --res_prop_simpl_given                  true
% 1.87/1.00  --res_passive_queue_type                priority_queues
% 1.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/1.00  --res_passive_queues_freq               [15;5]
% 1.87/1.00  --res_forward_subs                      full
% 1.87/1.00  --res_backward_subs                     full
% 1.87/1.00  --res_forward_subs_resolution           true
% 1.87/1.00  --res_backward_subs_resolution          true
% 1.87/1.00  --res_orphan_elimination                true
% 1.87/1.00  --res_time_limit                        2.
% 1.87/1.00  --res_out_proof                         true
% 1.87/1.00  
% 1.87/1.00  ------ Superposition Options
% 1.87/1.00  
% 1.87/1.00  --superposition_flag                    true
% 1.87/1.00  --sup_passive_queue_type                priority_queues
% 1.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.87/1.00  --demod_completeness_check              fast
% 1.87/1.00  --demod_use_ground                      true
% 1.87/1.00  --sup_to_prop_solver                    passive
% 1.87/1.00  --sup_prop_simpl_new                    true
% 1.87/1.00  --sup_prop_simpl_given                  true
% 1.87/1.00  --sup_fun_splitting                     false
% 1.87/1.00  --sup_smt_interval                      50000
% 1.87/1.00  
% 1.87/1.00  ------ Superposition Simplification Setup
% 1.87/1.00  
% 1.87/1.00  --sup_indices_passive                   []
% 1.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.00  --sup_full_bw                           [BwDemod]
% 1.87/1.00  --sup_immed_triv                        [TrivRules]
% 1.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.00  --sup_immed_bw_main                     []
% 1.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/1.00  
% 1.87/1.00  ------ Combination Options
% 1.87/1.00  
% 1.87/1.00  --comb_res_mult                         3
% 1.87/1.00  --comb_sup_mult                         2
% 1.87/1.00  --comb_inst_mult                        10
% 1.87/1.00  
% 1.87/1.00  ------ Debug Options
% 1.87/1.00  
% 1.87/1.00  --dbg_backtrace                         false
% 1.87/1.00  --dbg_dump_prop_clauses                 false
% 1.87/1.00  --dbg_dump_prop_clauses_file            -
% 1.87/1.00  --dbg_out_stat                          false
% 1.87/1.00  
% 1.87/1.00  
% 1.87/1.00  
% 1.87/1.00  
% 1.87/1.00  ------ Proving...
% 1.87/1.00  
% 1.87/1.00  
% 1.87/1.00  % SZS status Theorem for theBenchmark.p
% 1.87/1.00  
% 1.87/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/1.00  
% 1.87/1.00  fof(f104,plain,(
% 1.87/1.00    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.87/1.00    inference(cnf_transformation,[],[f63])).
% 1.87/1.00  
% 1.87/1.00  fof(f23,conjecture,(
% 1.87/1.00    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.00  
% 1.87/1.00  fof(f24,negated_conjecture,(
% 1.87/1.00    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 1.87/1.00    inference(negated_conjecture,[],[f23])).
% 1.87/1.00  
% 1.87/1.00  fof(f45,plain,(
% 1.87/1.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.87/1.00    inference(ennf_transformation,[],[f24])).
% 1.87/1.00  
% 1.87/1.00  fof(f46,plain,(
% 1.87/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.87/1.00    inference(flattening,[],[f45])).
% 1.87/1.00  
% 1.87/1.00  fof(f62,plain,(
% 1.87/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK7)) & sK7 = X3 & m1_subset_1(sK7,u1_struct_0(X0)))) )),
% 1.87/1.00    introduced(choice_axiom,[])).
% 1.87/1.00  
% 1.87/1.00  fof(f61,plain,(
% 1.87/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),sK6)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & sK6 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 1.87/1.00    introduced(choice_axiom,[])).
% 1.87/1.00  
% 1.87/1.00  fof(f60,plain,(
% 1.87/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK5,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(sK5,X0,X1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(sK5,X0,X1) & v1_funct_2(sK5,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK5))) )),
% 1.87/1.00    introduced(choice_axiom,[])).
% 1.87/1.00  
% 1.87/1.00  fof(f59,plain,(
% 1.87/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK4),X2,k6_domain_1(u1_struct_0(sK4),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(sK4))) & v3_borsuk_1(X2,X0,sK4) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK4)))) & v5_pre_topc(X2,X0,sK4) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK4)) & v1_funct_1(X2)) & m1_pre_topc(sK4,X0) & v4_tex_2(sK4,X0) & ~v2_struct_0(sK4))) )),
% 1.87/1.00    introduced(choice_axiom,[])).
% 1.87/1.00  
% 1.87/1.00  fof(f58,plain,(
% 1.87/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK3),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,sK3,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X1)))) & v5_pre_topc(X2,sK3,X1) & v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,sK3) & v4_tex_2(X1,sK3) & ~v2_struct_0(X1)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.87/1.00    introduced(choice_axiom,[])).
% 1.87/1.00  
% 1.87/1.00  fof(f63,plain,(
% 1.87/1.00    ((((k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) & sK6 = sK7 & m1_subset_1(sK7,u1_struct_0(sK3))) & m1_subset_1(sK6,u1_struct_0(sK4))) & v3_borsuk_1(sK5,sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) & v5_pre_topc(sK5,sK3,sK4) & v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) & v1_funct_1(sK5)) & m1_pre_topc(sK4,sK3) & v4_tex_2(sK4,sK3) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v3_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.87/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f46,f62,f61,f60,f59,f58])).
% 1.87/1.00  
% 1.87/1.00  fof(f106,plain,(
% 1.87/1.00    sK6 = sK7),
% 1.87/1.00    inference(cnf_transformation,[],[f63])).
% 1.87/1.00  
% 1.87/1.00  fof(f116,plain,(
% 1.87/1.00    m1_subset_1(sK7,u1_struct_0(sK4))),
% 1.87/1.00    inference(definition_unfolding,[],[f104,f106])).
% 1.87/1.00  
% 1.87/1.00  fof(f17,axiom,(
% 1.87/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.00  
% 1.87/1.00  fof(f34,plain,(
% 1.87/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.87/1.00    inference(ennf_transformation,[],[f17])).
% 1.87/1.00  
% 1.87/1.00  fof(f35,plain,(
% 1.87/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.87/1.01    inference(flattening,[],[f34])).
% 1.87/1.01  
% 1.87/1.01  fof(f84,plain,(
% 1.87/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f35])).
% 1.87/1.01  
% 1.87/1.01  fof(f4,axiom,(
% 1.87/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f70,plain,(
% 1.87/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f4])).
% 1.87/1.01  
% 1.87/1.01  fof(f5,axiom,(
% 1.87/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f71,plain,(
% 1.87/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f5])).
% 1.87/1.01  
% 1.87/1.01  fof(f6,axiom,(
% 1.87/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f72,plain,(
% 1.87/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f6])).
% 1.87/1.01  
% 1.87/1.01  fof(f7,axiom,(
% 1.87/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f73,plain,(
% 1.87/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f7])).
% 1.87/1.01  
% 1.87/1.01  fof(f8,axiom,(
% 1.87/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f74,plain,(
% 1.87/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f8])).
% 1.87/1.01  
% 1.87/1.01  fof(f9,axiom,(
% 1.87/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f75,plain,(
% 1.87/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f9])).
% 1.87/1.01  
% 1.87/1.01  fof(f10,axiom,(
% 1.87/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f76,plain,(
% 1.87/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f10])).
% 1.87/1.01  
% 1.87/1.01  fof(f108,plain,(
% 1.87/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.87/1.01    inference(definition_unfolding,[],[f75,f76])).
% 1.87/1.01  
% 1.87/1.01  fof(f109,plain,(
% 1.87/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.87/1.01    inference(definition_unfolding,[],[f74,f108])).
% 1.87/1.01  
% 1.87/1.01  fof(f110,plain,(
% 1.87/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.87/1.01    inference(definition_unfolding,[],[f73,f109])).
% 1.87/1.01  
% 1.87/1.01  fof(f111,plain,(
% 1.87/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.87/1.01    inference(definition_unfolding,[],[f72,f110])).
% 1.87/1.01  
% 1.87/1.01  fof(f112,plain,(
% 1.87/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.87/1.01    inference(definition_unfolding,[],[f71,f111])).
% 1.87/1.01  
% 1.87/1.01  fof(f113,plain,(
% 1.87/1.01    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.87/1.01    inference(definition_unfolding,[],[f70,f112])).
% 1.87/1.01  
% 1.87/1.01  fof(f114,plain,(
% 1.87/1.01    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.87/1.01    inference(definition_unfolding,[],[f84,f113])).
% 1.87/1.01  
% 1.87/1.01  fof(f92,plain,(
% 1.87/1.01    ~v2_struct_0(sK3)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f93,plain,(
% 1.87/1.01    v2_pre_topc(sK3)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f94,plain,(
% 1.87/1.01    v3_tdlat_3(sK3)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f95,plain,(
% 1.87/1.01    l1_pre_topc(sK3)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f96,plain,(
% 1.87/1.01    ~v2_struct_0(sK4)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f19,axiom,(
% 1.87/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (v3_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f37,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (((v3_tdlat_3(X1) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.87/1.01    inference(ennf_transformation,[],[f19])).
% 1.87/1.01  
% 1.87/1.01  fof(f38,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : ((v3_tdlat_3(X1) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/1.01    inference(flattening,[],[f37])).
% 1.87/1.01  
% 1.87/1.01  fof(f87,plain,(
% 1.87/1.01    ( ! [X0,X1] : (v3_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f38])).
% 1.87/1.01  
% 1.87/1.01  fof(f98,plain,(
% 1.87/1.01    m1_pre_topc(sK4,sK3)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f14,axiom,(
% 1.87/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f30,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.87/1.01    inference(ennf_transformation,[],[f14])).
% 1.87/1.01  
% 1.87/1.01  fof(f81,plain,(
% 1.87/1.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f30])).
% 1.87/1.01  
% 1.87/1.01  fof(f20,axiom,(
% 1.87/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f39,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.87/1.01    inference(ennf_transformation,[],[f20])).
% 1.87/1.01  
% 1.87/1.01  fof(f40,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/1.01    inference(flattening,[],[f39])).
% 1.87/1.01  
% 1.87/1.01  fof(f88,plain,(
% 1.87/1.01    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f40])).
% 1.87/1.01  
% 1.87/1.01  fof(f21,axiom,(
% 1.87/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f41,plain,(
% 1.87/1.01    ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.87/1.01    inference(ennf_transformation,[],[f21])).
% 1.87/1.01  
% 1.87/1.01  fof(f42,plain,(
% 1.87/1.01    ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/1.01    inference(flattening,[],[f41])).
% 1.87/1.01  
% 1.87/1.01  fof(f56,plain,(
% 1.87/1.01    ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.87/1.01    introduced(choice_axiom,[])).
% 1.87/1.01  
% 1.87/1.01  fof(f57,plain,(
% 1.87/1.01    ! [X0] : ((v3_tex_2(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f56])).
% 1.87/1.01  
% 1.87/1.01  fof(f90,plain,(
% 1.87/1.01    ( ! [X0] : (v3_tex_2(sK2(X0),X0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f57])).
% 1.87/1.01  
% 1.87/1.01  fof(f89,plain,(
% 1.87/1.01    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f57])).
% 1.87/1.01  
% 1.87/1.01  fof(f13,axiom,(
% 1.87/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f28,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.87/1.01    inference(ennf_transformation,[],[f13])).
% 1.87/1.01  
% 1.87/1.01  fof(f29,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.87/1.01    inference(flattening,[],[f28])).
% 1.87/1.01  
% 1.87/1.01  fof(f80,plain,(
% 1.87/1.01    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f29])).
% 1.87/1.01  
% 1.87/1.01  fof(f12,axiom,(
% 1.87/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f55,plain,(
% 1.87/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.87/1.01    inference(nnf_transformation,[],[f12])).
% 1.87/1.01  
% 1.87/1.01  fof(f78,plain,(
% 1.87/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.87/1.01    inference(cnf_transformation,[],[f55])).
% 1.87/1.01  
% 1.87/1.01  fof(f11,axiom,(
% 1.87/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f27,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.87/1.01    inference(ennf_transformation,[],[f11])).
% 1.87/1.01  
% 1.87/1.01  fof(f77,plain,(
% 1.87/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f27])).
% 1.87/1.01  
% 1.87/1.01  fof(f79,plain,(
% 1.87/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f55])).
% 1.87/1.01  
% 1.87/1.01  fof(f105,plain,(
% 1.87/1.01    m1_subset_1(sK7,u1_struct_0(sK3))),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f16,axiom,(
% 1.87/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f32,plain,(
% 1.87/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.87/1.01    inference(ennf_transformation,[],[f16])).
% 1.87/1.01  
% 1.87/1.01  fof(f33,plain,(
% 1.87/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.87/1.01    inference(flattening,[],[f32])).
% 1.87/1.01  
% 1.87/1.01  fof(f83,plain,(
% 1.87/1.01    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f33])).
% 1.87/1.01  
% 1.87/1.01  fof(f107,plain,(
% 1.87/1.01    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK6)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f115,plain,(
% 1.87/1.01    k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))),
% 1.87/1.01    inference(definition_unfolding,[],[f107,f106])).
% 1.87/1.01  
% 1.87/1.01  fof(f15,axiom,(
% 1.87/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f31,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.87/1.01    inference(ennf_transformation,[],[f15])).
% 1.87/1.01  
% 1.87/1.01  fof(f82,plain,(
% 1.87/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f31])).
% 1.87/1.01  
% 1.87/1.01  fof(f22,axiom,(
% 1.87/1.01    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 1.87/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/1.01  
% 1.87/1.01  fof(f43,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.87/1.01    inference(ennf_transformation,[],[f22])).
% 1.87/1.01  
% 1.87/1.01  fof(f44,plain,(
% 1.87/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.87/1.01    inference(flattening,[],[f43])).
% 1.87/1.01  
% 1.87/1.01  fof(f91,plain,(
% 1.87/1.01    ( ! [X4,X2,X0,X3,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/1.01    inference(cnf_transformation,[],[f44])).
% 1.87/1.01  
% 1.87/1.01  fof(f117,plain,(
% 1.87/1.01    ( ! [X4,X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) = k2_pre_topc(X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.87/1.01    inference(equality_resolution,[],[f91])).
% 1.87/1.01  
% 1.87/1.01  fof(f103,plain,(
% 1.87/1.01    v3_borsuk_1(sK5,sK3,sK4)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f97,plain,(
% 1.87/1.01    v4_tex_2(sK4,sK3)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f99,plain,(
% 1.87/1.01    v1_funct_1(sK5)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f100,plain,(
% 1.87/1.01    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f101,plain,(
% 1.87/1.01    v5_pre_topc(sK5,sK3,sK4)),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  fof(f102,plain,(
% 1.87/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))),
% 1.87/1.01    inference(cnf_transformation,[],[f63])).
% 1.87/1.01  
% 1.87/1.01  cnf(c_23,negated_conjecture,
% 1.87/1.01      ( m1_subset_1(sK7,u1_struct_0(sK4)) ),
% 1.87/1.01      inference(cnf_transformation,[],[f116]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1503,plain,
% 1.87/1.01      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_13,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,X1)
% 1.87/1.01      | v1_xboole_0(X1)
% 1.87/1.01      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 1.87/1.01      inference(cnf_transformation,[],[f114]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1505,plain,
% 1.87/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 1.87/1.01      | m1_subset_1(X0,X1) != iProver_top
% 1.87/1.01      | v1_xboole_0(X1) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2299,plain,
% 1.87/1.01      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7)
% 1.87/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 1.87/1.01      inference(superposition,[status(thm)],[c_1503,c_1505]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_35,negated_conjecture,
% 1.87/1.01      ( ~ v2_struct_0(sK3) ),
% 1.87/1.01      inference(cnf_transformation,[],[f92]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_34,negated_conjecture,
% 1.87/1.01      ( v2_pre_topc(sK3) ),
% 1.87/1.01      inference(cnf_transformation,[],[f93]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_33,negated_conjecture,
% 1.87/1.01      ( v3_tdlat_3(sK3) ),
% 1.87/1.01      inference(cnf_transformation,[],[f94]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_32,negated_conjecture,
% 1.87/1.01      ( l1_pre_topc(sK3) ),
% 1.87/1.01      inference(cnf_transformation,[],[f95]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_31,negated_conjecture,
% 1.87/1.01      ( ~ v2_struct_0(sK4) ),
% 1.87/1.01      inference(cnf_transformation,[],[f96]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_15,plain,
% 1.87/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.87/1.01      | v2_struct_0(X1)
% 1.87/1.01      | v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X1)
% 1.87/1.01      | v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X1)
% 1.87/1.01      | ~ v2_pre_topc(X1) ),
% 1.87/1.01      inference(cnf_transformation,[],[f87]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_29,negated_conjecture,
% 1.87/1.01      ( m1_pre_topc(sK4,sK3) ),
% 1.87/1.01      inference(cnf_transformation,[],[f98]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_495,plain,
% 1.87/1.01      ( v2_struct_0(X0)
% 1.87/1.01      | v2_struct_0(X1)
% 1.87/1.01      | ~ v3_tdlat_3(X1)
% 1.87/1.01      | v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X1)
% 1.87/1.01      | ~ v2_pre_topc(X1)
% 1.87/1.01      | sK4 != X0
% 1.87/1.01      | sK3 != X1 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_496,plain,
% 1.87/1.01      ( v2_struct_0(sK4)
% 1.87/1.01      | v2_struct_0(sK3)
% 1.87/1.01      | v3_tdlat_3(sK4)
% 1.87/1.01      | ~ v3_tdlat_3(sK3)
% 1.87/1.01      | ~ l1_pre_topc(sK3)
% 1.87/1.01      | ~ v2_pre_topc(sK3) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_495]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_10,plain,
% 1.87/1.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.87/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_535,plain,
% 1.87/1.01      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK4 != X1 | sK3 != X0 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_536,plain,
% 1.87/1.01      ( l1_pre_topc(sK4) | ~ l1_pre_topc(sK3) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_535]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_17,plain,
% 1.87/1.01      ( ~ v3_tex_2(X0,X1)
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/1.01      | v2_struct_0(X1)
% 1.87/1.01      | ~ l1_pre_topc(X1)
% 1.87/1.01      | ~ v2_pre_topc(X1)
% 1.87/1.01      | ~ v1_xboole_0(X0) ),
% 1.87/1.01      inference(cnf_transformation,[],[f88]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_18,plain,
% 1.87/1.01      ( v3_tex_2(sK2(X0),X0)
% 1.87/1.01      | v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X0)
% 1.87/1.01      | ~ v2_pre_topc(X0) ),
% 1.87/1.01      inference(cnf_transformation,[],[f90]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_437,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/1.01      | v2_struct_0(X2)
% 1.87/1.01      | v2_struct_0(X1)
% 1.87/1.01      | ~ v3_tdlat_3(X2)
% 1.87/1.01      | ~ l1_pre_topc(X1)
% 1.87/1.01      | ~ l1_pre_topc(X2)
% 1.87/1.01      | ~ v2_pre_topc(X1)
% 1.87/1.01      | ~ v2_pre_topc(X2)
% 1.87/1.01      | ~ v1_xboole_0(X0)
% 1.87/1.01      | X2 != X1
% 1.87/1.01      | sK2(X2) != X0 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_18]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_438,plain,
% 1.87/1.01      ( ~ m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.87/1.01      | v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X0)
% 1.87/1.01      | ~ v2_pre_topc(X0)
% 1.87/1.01      | ~ v1_xboole_0(sK2(X0)) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_437]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_19,plain,
% 1.87/1.01      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.87/1.01      | v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X0)
% 1.87/1.01      | ~ v2_pre_topc(X0) ),
% 1.87/1.01      inference(cnf_transformation,[],[f89]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_442,plain,
% 1.87/1.01      ( v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X0)
% 1.87/1.01      | ~ v2_pre_topc(X0)
% 1.87/1.01      | ~ v1_xboole_0(sK2(X0)) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_438,c_19]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_9,plain,
% 1.87/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.87/1.01      | ~ l1_pre_topc(X1)
% 1.87/1.01      | ~ v2_pre_topc(X1)
% 1.87/1.01      | v2_pre_topc(X0) ),
% 1.87/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_546,plain,
% 1.87/1.01      ( ~ l1_pre_topc(X0)
% 1.87/1.01      | ~ v2_pre_topc(X0)
% 1.87/1.01      | v2_pre_topc(X1)
% 1.87/1.01      | sK4 != X1
% 1.87/1.01      | sK3 != X0 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_547,plain,
% 1.87/1.01      ( ~ l1_pre_topc(sK3) | v2_pre_topc(sK4) | ~ v2_pre_topc(sK3) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_546]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_549,plain,
% 1.87/1.01      ( v2_pre_topc(sK4) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_547,c_34,c_32]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_594,plain,
% 1.87/1.01      ( v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X0)
% 1.87/1.01      | ~ v1_xboole_0(sK2(X0))
% 1.87/1.01      | sK4 != X0 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_442,c_549]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_595,plain,
% 1.87/1.01      ( v2_struct_0(sK4)
% 1.87/1.01      | ~ v3_tdlat_3(sK4)
% 1.87/1.01      | ~ l1_pre_topc(sK4)
% 1.87/1.01      | ~ v1_xboole_0(sK2(sK4)) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_594]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_605,plain,
% 1.87/1.01      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.87/1.01      | v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X0)
% 1.87/1.01      | sK4 != X0 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_549]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_606,plain,
% 1.87/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | v2_struct_0(sK4)
% 1.87/1.01      | ~ v3_tdlat_3(sK4)
% 1.87/1.01      | ~ l1_pre_topc(sK4) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_605]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_608,plain,
% 1.87/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_606,c_35,c_34,c_33,c_32,c_31,c_496,c_536]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1494,plain,
% 1.87/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_8,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.87/1.01      inference(cnf_transformation,[],[f78]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1507,plain,
% 1.87/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.87/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1928,plain,
% 1.87/1.01      ( r1_tarski(sK2(sK4),u1_struct_0(sK4)) = iProver_top ),
% 1.87/1.01      inference(superposition,[status(thm)],[c_1494,c_1507]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1940,plain,
% 1.87/1.01      ( r1_tarski(sK2(sK4),u1_struct_0(sK4)) ),
% 1.87/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1928]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2044,plain,
% 1.87/1.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK4))
% 1.87/1.01      | v1_xboole_0(u1_struct_0(sK4))
% 1.87/1.01      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_6,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.87/1.01      | ~ v1_xboole_0(X1)
% 1.87/1.01      | v1_xboole_0(X0) ),
% 1.87/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_7,plain,
% 1.87/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.87/1.01      inference(cnf_transformation,[],[f79]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_245,plain,
% 1.87/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.87/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_246,plain,
% 1.87/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.87/1.01      inference(renaming,[status(thm)],[c_245]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_310,plain,
% 1.87/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 1.87/1.01      inference(bin_hyper_res,[status(thm)],[c_6,c_246]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1723,plain,
% 1.87/1.01      ( ~ r1_tarski(sK2(sK4),X0)
% 1.87/1.01      | ~ v1_xboole_0(X0)
% 1.87/1.01      | v1_xboole_0(sK2(sK4)) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_310]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2104,plain,
% 1.87/1.01      ( ~ r1_tarski(sK2(sK4),u1_struct_0(sK4))
% 1.87/1.01      | v1_xboole_0(sK2(sK4))
% 1.87/1.01      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_1723]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2509,plain,
% 1.87/1.01      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_2299,c_35,c_34,c_33,c_32,c_31,c_23,c_496,c_536,c_595,
% 1.87/1.01                 c_1940,c_2044,c_2104]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_22,negated_conjecture,
% 1.87/1.01      ( m1_subset_1(sK7,u1_struct_0(sK3)) ),
% 1.87/1.01      inference(cnf_transformation,[],[f105]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1504,plain,
% 1.87/1.01      ( m1_subset_1(sK7,u1_struct_0(sK3)) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2298,plain,
% 1.87/1.01      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7)
% 1.87/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 1.87/1.01      inference(superposition,[status(thm)],[c_1504,c_1505]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_54,plain,
% 1.87/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | v2_struct_0(sK3)
% 1.87/1.01      | ~ v3_tdlat_3(sK3)
% 1.87/1.01      | ~ l1_pre_topc(sK3)
% 1.87/1.01      | ~ v2_pre_topc(sK3) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_440,plain,
% 1.87/1.01      ( ~ m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | v2_struct_0(sK3)
% 1.87/1.01      | ~ v3_tdlat_3(sK3)
% 1.87/1.01      | ~ l1_pre_topc(sK3)
% 1.87/1.01      | ~ v2_pre_topc(sK3)
% 1.87/1.01      | ~ v1_xboole_0(sK2(sK3)) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_438]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_583,plain,
% 1.87/1.01      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.87/1.01      | v2_struct_0(X0)
% 1.87/1.01      | ~ v3_tdlat_3(X0)
% 1.87/1.01      | ~ l1_pre_topc(X0)
% 1.87/1.01      | sK3 != X0 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_584,plain,
% 1.87/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | v2_struct_0(sK3)
% 1.87/1.01      | ~ v3_tdlat_3(sK3)
% 1.87/1.01      | ~ l1_pre_topc(sK3) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_583]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_586,plain,
% 1.87/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_584,c_35,c_34,c_33,c_32,c_54]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1496,plain,
% 1.87/1.01      ( m1_subset_1(sK2(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1926,plain,
% 1.87/1.01      ( r1_tarski(sK2(sK3),u1_struct_0(sK3)) = iProver_top ),
% 1.87/1.01      inference(superposition,[status(thm)],[c_1496,c_1507]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1938,plain,
% 1.87/1.01      ( r1_tarski(sK2(sK3),u1_struct_0(sK3)) ),
% 1.87/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1926]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2041,plain,
% 1.87/1.01      ( ~ m1_subset_1(sK7,u1_struct_0(sK3))
% 1.87/1.01      | v1_xboole_0(u1_struct_0(sK3))
% 1.87/1.01      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1718,plain,
% 1.87/1.01      ( ~ r1_tarski(sK2(sK3),X0)
% 1.87/1.01      | ~ v1_xboole_0(X0)
% 1.87/1.01      | v1_xboole_0(sK2(sK3)) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_310]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2080,plain,
% 1.87/1.01      ( ~ r1_tarski(sK2(sK3),u1_struct_0(sK3))
% 1.87/1.01      | v1_xboole_0(sK2(sK3))
% 1.87/1.01      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_1718]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2505,plain,
% 1.87/1.01      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k6_domain_1(u1_struct_0(sK3),sK7) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_2298,c_35,c_34,c_33,c_32,c_22,c_54,c_440,c_1938,
% 1.87/1.01                 c_2041,c_2080]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2511,plain,
% 1.87/1.01      ( k6_domain_1(u1_struct_0(sK3),sK7) = k6_domain_1(u1_struct_0(sK4),sK7) ),
% 1.87/1.01      inference(light_normalisation,[status(thm)],[c_2509,c_2505]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_12,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,X1)
% 1.87/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 1.87/1.01      | v1_xboole_0(X1) ),
% 1.87/1.01      inference(cnf_transformation,[],[f83]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_1506,plain,
% 1.87/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 1.87/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 1.87/1.01      | v1_xboole_0(X1) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2768,plain,
% 1.87/1.01      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 1.87/1.01      | m1_subset_1(sK7,u1_struct_0(sK4)) != iProver_top
% 1.87/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 1.87/1.01      inference(superposition,[status(thm)],[c_2511,c_1506]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_21,negated_conjecture,
% 1.87/1.01      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK4),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 1.87/1.01      inference(cnf_transformation,[],[f115]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2513,plain,
% 1.87/1.01      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK3),sK7)) != k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 1.87/1.01      inference(demodulation,[status(thm)],[c_2511,c_21]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_11,plain,
% 1.87/1.01      ( ~ m1_pre_topc(X0,X1)
% 1.87/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 1.87/1.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/1.01      | ~ l1_pre_topc(X1) ),
% 1.87/1.01      inference(cnf_transformation,[],[f82]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_517,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 1.87/1.01      | ~ l1_pre_topc(X2)
% 1.87/1.01      | sK4 != X1
% 1.87/1.01      | sK3 != X2 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_518,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | ~ l1_pre_topc(sK3) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_517]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_522,plain,
% 1.87/1.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_518,c_32]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_523,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 1.87/1.01      inference(renaming,[status(thm)],[c_522]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_20,plain,
% 1.87/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.87/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 1.87/1.01      | ~ v3_borsuk_1(X0,X1,X2)
% 1.87/1.01      | ~ v4_tex_2(X2,X1)
% 1.87/1.01      | ~ m1_pre_topc(X2,X1)
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.87/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.87/1.01      | ~ v1_funct_1(X0)
% 1.87/1.01      | v2_struct_0(X1)
% 1.87/1.01      | v2_struct_0(X2)
% 1.87/1.01      | ~ v3_tdlat_3(X1)
% 1.87/1.01      | ~ l1_pre_topc(X1)
% 1.87/1.01      | ~ v2_pre_topc(X1)
% 1.87/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3) ),
% 1.87/1.01      inference(cnf_transformation,[],[f117]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_24,negated_conjecture,
% 1.87/1.01      ( v3_borsuk_1(sK5,sK3,sK4) ),
% 1.87/1.01      inference(cnf_transformation,[],[f103]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_470,plain,
% 1.87/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.87/1.01      | ~ v5_pre_topc(X0,X1,X2)
% 1.87/1.01      | ~ v4_tex_2(X2,X1)
% 1.87/1.01      | ~ m1_pre_topc(X2,X1)
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.87/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.87/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
% 1.87/1.01      | ~ v1_funct_1(X0)
% 1.87/1.01      | v2_struct_0(X2)
% 1.87/1.01      | v2_struct_0(X1)
% 1.87/1.01      | ~ v3_tdlat_3(X1)
% 1.87/1.01      | ~ l1_pre_topc(X1)
% 1.87/1.01      | ~ v2_pre_topc(X1)
% 1.87/1.01      | k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0,X3) = k2_pre_topc(X1,X3)
% 1.87/1.01      | sK5 != X0
% 1.87/1.01      | sK4 != X2
% 1.87/1.01      | sK3 != X1 ),
% 1.87/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_471,plain,
% 1.87/1.01      ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4))
% 1.87/1.01      | ~ v5_pre_topc(sK5,sK3,sK4)
% 1.87/1.01      | ~ v4_tex_2(sK4,sK3)
% 1.87/1.01      | ~ m1_pre_topc(sK4,sK3)
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4))))
% 1.87/1.01      | ~ v1_funct_1(sK5)
% 1.87/1.01      | v2_struct_0(sK4)
% 1.87/1.01      | v2_struct_0(sK3)
% 1.87/1.01      | ~ v3_tdlat_3(sK3)
% 1.87/1.01      | ~ l1_pre_topc(sK3)
% 1.87/1.01      | ~ v2_pre_topc(sK3)
% 1.87/1.01      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.87/1.01      inference(unflattening,[status(thm)],[c_470]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_30,negated_conjecture,
% 1.87/1.01      ( v4_tex_2(sK4,sK3) ),
% 1.87/1.01      inference(cnf_transformation,[],[f97]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_28,negated_conjecture,
% 1.87/1.01      ( v1_funct_1(sK5) ),
% 1.87/1.01      inference(cnf_transformation,[],[f99]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_27,negated_conjecture,
% 1.87/1.01      ( v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK4)) ),
% 1.87/1.01      inference(cnf_transformation,[],[f100]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_26,negated_conjecture,
% 1.87/1.01      ( v5_pre_topc(sK5,sK3,sK4) ),
% 1.87/1.01      inference(cnf_transformation,[],[f101]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_25,negated_conjecture,
% 1.87/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK4)))) ),
% 1.87/1.01      inference(cnf_transformation,[],[f102]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_475,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.87/1.01      inference(global_propositional_subsumption,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_471,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_27,c_26,
% 1.87/1.01                 c_25]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_476,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 1.87/1.01      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.87/1.01      inference(renaming,[status(thm)],[c_475]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_563,plain,
% 1.87/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,X0) = k2_pre_topc(sK3,X0) ),
% 1.87/1.01      inference(backward_subsumption_resolution,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_523,c_476]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2409,plain,
% 1.87/1.01      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7),k1_zfmisc_1(u1_struct_0(sK4)))
% 1.87/1.01      | k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7)) ),
% 1.87/1.01      inference(instantiation,[status(thm)],[c_563]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2410,plain,
% 1.87/1.01      ( k8_relset_1(u1_struct_0(sK3),u1_struct_0(sK4),sK5,k6_domain_1(u1_struct_0(sK3),sK7)) = k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK7))
% 1.87/1.01      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK7),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_2409]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_2122,plain,
% 1.87/1.01      ( r1_tarski(sK2(sK4),u1_struct_0(sK4)) != iProver_top
% 1.87/1.01      | v1_xboole_0(sK2(sK4)) = iProver_top
% 1.87/1.01      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_2104]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_596,plain,
% 1.87/1.01      ( v2_struct_0(sK4) = iProver_top
% 1.87/1.01      | v3_tdlat_3(sK4) != iProver_top
% 1.87/1.01      | l1_pre_topc(sK4) != iProver_top
% 1.87/1.01      | v1_xboole_0(sK2(sK4)) != iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_537,plain,
% 1.87/1.01      ( l1_pre_topc(sK4) = iProver_top
% 1.87/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_497,plain,
% 1.87/1.01      ( v2_struct_0(sK4) = iProver_top
% 1.87/1.01      | v2_struct_0(sK3) = iProver_top
% 1.87/1.01      | v3_tdlat_3(sK4) = iProver_top
% 1.87/1.01      | v3_tdlat_3(sK3) != iProver_top
% 1.87/1.01      | l1_pre_topc(sK3) != iProver_top
% 1.87/1.01      | v2_pre_topc(sK3) != iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_48,plain,
% 1.87/1.01      ( m1_subset_1(sK7,u1_struct_0(sK4)) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_40,plain,
% 1.87/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_39,plain,
% 1.87/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_38,plain,
% 1.87/1.01      ( v3_tdlat_3(sK3) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_37,plain,
% 1.87/1.01      ( v2_pre_topc(sK3) = iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(c_36,plain,
% 1.87/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 1.87/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 1.87/1.01  
% 1.87/1.01  cnf(contradiction,plain,
% 1.87/1.01      ( $false ),
% 1.87/1.01      inference(minisat,
% 1.87/1.01                [status(thm)],
% 1.87/1.01                [c_2768,c_2513,c_2410,c_2122,c_1928,c_596,c_537,c_497,
% 1.87/1.01                 c_48,c_40,c_39,c_38,c_37,c_36]) ).
% 1.87/1.01  
% 1.87/1.01  
% 1.87/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/1.01  
% 1.87/1.01  ------                               Statistics
% 1.87/1.01  
% 1.87/1.01  ------ General
% 1.87/1.01  
% 1.87/1.01  abstr_ref_over_cycles:                  0
% 1.87/1.01  abstr_ref_under_cycles:                 0
% 1.87/1.01  gc_basic_clause_elim:                   0
% 1.87/1.01  forced_gc_time:                         0
% 1.87/1.01  parsing_time:                           0.013
% 1.87/1.01  unif_index_cands_time:                  0.
% 1.87/1.01  unif_index_add_time:                    0.
% 1.87/1.01  orderings_time:                         0.
% 1.87/1.01  out_proof_time:                         0.016
% 1.87/1.01  total_time:                             0.125
% 1.87/1.01  num_of_symbols:                         60
% 1.87/1.01  num_of_terms:                           1844
% 1.87/1.01  
% 1.87/1.01  ------ Preprocessing
% 1.87/1.01  
% 1.87/1.01  num_of_splits:                          0
% 1.87/1.01  num_of_split_atoms:                     0
% 1.87/1.01  num_of_reused_defs:                     0
% 1.87/1.01  num_eq_ax_congr_red:                    45
% 1.87/1.01  num_of_sem_filtered_clauses:            1
% 1.87/1.01  num_of_subtypes:                        0
% 1.87/1.01  monotx_restored_types:                  0
% 1.87/1.01  sat_num_of_epr_types:                   0
% 1.87/1.01  sat_num_of_non_cyclic_types:            0
% 1.87/1.01  sat_guarded_non_collapsed_types:        0
% 1.87/1.01  num_pure_diseq_elim:                    0
% 1.87/1.01  simp_replaced_by:                       0
% 1.87/1.01  res_preprocessed:                       126
% 1.87/1.01  prep_upred:                             0
% 1.87/1.01  prep_unflattend:                        19
% 1.87/1.01  smt_new_axioms:                         0
% 1.87/1.01  pred_elim_cands:                        4
% 1.87/1.01  pred_elim:                              11
% 1.87/1.01  pred_elim_cl:                           13
% 1.87/1.01  pred_elim_cycles:                       13
% 1.87/1.01  merged_defs:                            8
% 1.87/1.01  merged_defs_ncl:                        0
% 1.87/1.01  bin_hyper_res:                          9
% 1.87/1.01  prep_cycles:                            4
% 1.87/1.01  pred_elim_time:                         0.006
% 1.87/1.01  splitting_time:                         0.
% 1.87/1.01  sem_filter_time:                        0.
% 1.87/1.01  monotx_time:                            0.001
% 1.87/1.01  subtype_inf_time:                       0.
% 1.87/1.01  
% 1.87/1.01  ------ Problem properties
% 1.87/1.01  
% 1.87/1.01  clauses:                                22
% 1.87/1.01  conjectures:                            4
% 1.87/1.01  epr:                                    4
% 1.87/1.01  horn:                                   18
% 1.87/1.01  ground:                                 9
% 1.87/1.01  unary:                                  9
% 1.87/1.01  binary:                                 8
% 1.87/1.01  lits:                                   40
% 1.87/1.01  lits_eq:                                4
% 1.87/1.01  fd_pure:                                0
% 1.87/1.01  fd_pseudo:                              0
% 1.87/1.01  fd_cond:                                0
% 1.87/1.01  fd_pseudo_cond:                         1
% 1.87/1.01  ac_symbols:                             0
% 1.87/1.01  
% 1.87/1.01  ------ Propositional Solver
% 1.87/1.01  
% 1.87/1.01  prop_solver_calls:                      27
% 1.87/1.01  prop_fast_solver_calls:                 743
% 1.87/1.01  smt_solver_calls:                       0
% 1.87/1.01  smt_fast_solver_calls:                  0
% 1.87/1.01  prop_num_of_clauses:                    783
% 1.87/1.01  prop_preprocess_simplified:             3879
% 1.87/1.01  prop_fo_subsumed:                       36
% 1.87/1.01  prop_solver_time:                       0.
% 1.87/1.01  smt_solver_time:                        0.
% 1.87/1.01  smt_fast_solver_time:                   0.
% 1.87/1.01  prop_fast_solver_time:                  0.
% 1.87/1.01  prop_unsat_core_time:                   0.
% 1.87/1.01  
% 1.87/1.01  ------ QBF
% 1.87/1.01  
% 1.87/1.01  qbf_q_res:                              0
% 1.87/1.01  qbf_num_tautologies:                    0
% 1.87/1.01  qbf_prep_cycles:                        0
% 1.87/1.01  
% 1.87/1.01  ------ BMC1
% 1.87/1.01  
% 1.87/1.01  bmc1_current_bound:                     -1
% 1.87/1.01  bmc1_last_solved_bound:                 -1
% 1.87/1.01  bmc1_unsat_core_size:                   -1
% 1.87/1.01  bmc1_unsat_core_parents_size:           -1
% 1.87/1.01  bmc1_merge_next_fun:                    0
% 1.87/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.87/1.01  
% 1.87/1.01  ------ Instantiation
% 1.87/1.01  
% 1.87/1.01  inst_num_of_clauses:                    221
% 1.87/1.01  inst_num_in_passive:                    51
% 1.87/1.01  inst_num_in_active:                     151
% 1.87/1.01  inst_num_in_unprocessed:                19
% 1.87/1.01  inst_num_of_loops:                      180
% 1.87/1.01  inst_num_of_learning_restarts:          0
% 1.87/1.01  inst_num_moves_active_passive:          26
% 1.87/1.01  inst_lit_activity:                      0
% 1.87/1.01  inst_lit_activity_moves:                0
% 1.87/1.01  inst_num_tautologies:                   0
% 1.87/1.01  inst_num_prop_implied:                  0
% 1.87/1.01  inst_num_existing_simplified:           0
% 1.87/1.01  inst_num_eq_res_simplified:             0
% 1.87/1.01  inst_num_child_elim:                    0
% 1.87/1.01  inst_num_of_dismatching_blockings:      51
% 1.87/1.01  inst_num_of_non_proper_insts:           185
% 1.87/1.01  inst_num_of_duplicates:                 0
% 1.87/1.01  inst_inst_num_from_inst_to_res:         0
% 1.87/1.01  inst_dismatching_checking_time:         0.
% 1.87/1.01  
% 1.87/1.01  ------ Resolution
% 1.87/1.01  
% 1.87/1.01  res_num_of_clauses:                     0
% 1.87/1.01  res_num_in_passive:                     0
% 1.87/1.01  res_num_in_active:                      0
% 1.87/1.01  res_num_of_loops:                       130
% 1.87/1.01  res_forward_subset_subsumed:            24
% 1.87/1.01  res_backward_subset_subsumed:           0
% 1.87/1.01  res_forward_subsumed:                   2
% 1.87/1.01  res_backward_subsumed:                  0
% 1.87/1.01  res_forward_subsumption_resolution:     0
% 1.87/1.01  res_backward_subsumption_resolution:    1
% 1.87/1.01  res_clause_to_clause_subsumption:       113
% 1.87/1.01  res_orphan_elimination:                 0
% 1.87/1.01  res_tautology_del:                      31
% 1.87/1.01  res_num_eq_res_simplified:              0
% 1.87/1.01  res_num_sel_changes:                    0
% 1.87/1.01  res_moves_from_active_to_pass:          0
% 1.87/1.01  
% 1.87/1.01  ------ Superposition
% 1.87/1.01  
% 1.87/1.01  sup_time_total:                         0.
% 1.87/1.01  sup_time_generating:                    0.
% 1.87/1.01  sup_time_sim_full:                      0.
% 1.87/1.01  sup_time_sim_immed:                     0.
% 1.87/1.01  
% 1.87/1.01  sup_num_of_clauses:                     56
% 1.87/1.01  sup_num_in_active:                      34
% 1.87/1.01  sup_num_in_passive:                     22
% 1.87/1.01  sup_num_of_loops:                       34
% 1.87/1.01  sup_fw_superposition:                   25
% 1.87/1.01  sup_bw_superposition:                   15
% 1.87/1.01  sup_immediate_simplified:               0
% 1.87/1.01  sup_given_eliminated:                   0
% 1.87/1.01  comparisons_done:                       0
% 1.87/1.01  comparisons_avoided:                    1
% 1.87/1.01  
% 1.87/1.01  ------ Simplifications
% 1.87/1.01  
% 1.87/1.01  
% 1.87/1.01  sim_fw_subset_subsumed:                 0
% 1.87/1.01  sim_bw_subset_subsumed:                 0
% 1.87/1.01  sim_fw_subsumed:                        0
% 1.87/1.01  sim_bw_subsumed:                        0
% 1.87/1.01  sim_fw_subsumption_res:                 0
% 1.87/1.01  sim_bw_subsumption_res:                 0
% 1.87/1.01  sim_tautology_del:                      1
% 1.87/1.01  sim_eq_tautology_del:                   1
% 1.87/1.01  sim_eq_res_simp:                        0
% 1.87/1.01  sim_fw_demodulated:                     0
% 1.87/1.01  sim_bw_demodulated:                     1
% 1.87/1.01  sim_light_normalised:                   1
% 1.87/1.01  sim_joinable_taut:                      0
% 1.87/1.01  sim_joinable_simp:                      0
% 1.87/1.01  sim_ac_normalised:                      0
% 1.87/1.01  sim_smt_subsumption:                    0
% 1.87/1.01  
%------------------------------------------------------------------------------
