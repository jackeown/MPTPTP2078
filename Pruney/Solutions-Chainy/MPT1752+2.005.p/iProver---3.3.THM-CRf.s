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
% DateTime   : Thu Dec  3 12:22:35 EST 2020

% Result     : Theorem 19.21s
% Output     : CNFRefutation 19.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 421 expanded)
%              Number of clauses        :   96 ( 127 expanded)
%              Number of leaves         :   18 ( 148 expanded)
%              Depth                    :   25
%              Number of atoms          :  545 (3855 expanded)
%              Number of equality atoms :  149 ( 484 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                       => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4)
        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
              & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4)
            & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                  & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4)
                & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4)
                    & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f31,f37,f36,f35,f34,f33])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_649,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_27361,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_655,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k7_relset_1(X0_55,X1_55,X0_54,X2_55) = k9_relat_1(X0_54,X2_55) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_27356,plain,
    ( k7_relset_1(X0_55,X1_55,X0_54,X2_55) = k9_relat_1(X0_54,X2_55)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_27712,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_55) = k9_relat_1(sK3,X0_55) ),
    inference(superposition,[status(thm)],[c_27361,c_27356])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k7_relset_1(X0_55,X1_55,X0_54,X2_55),k1_zfmisc_1(X1_55)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_27355,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k7_relset_1(X0_55,X1_55,X0_54,X2_55),k1_zfmisc_1(X1_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_27852,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27712,c_27355])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_27889,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27852,c_37])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_661,plain,
    ( r1_tarski(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_27350,plain,
    ( r1_tarski(X0_54,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_27896,plain,
    ( r1_tarski(k9_relat_1(sK3,X0_55),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27889,c_27350])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_27354,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_27676,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_27361,c_27354])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_659,plain,
    ( ~ v1_relat_1(X0_54)
    | k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_27352,plain,
    ( k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_27688,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_55)) = k9_relat_1(sK3,X0_55) ),
    inference(superposition,[status(thm)],[c_27676,c_27352])).

cnf(c_4,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_658,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X0_55)),X0_55)
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_27353,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X0_55)),X0_55) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_653,plain,
    ( ~ r1_tarski(k1_relat_1(X0_54),X0_55)
    | ~ r1_tarski(k2_relat_1(X0_54),X1_55)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_27358,plain,
    ( r1_tarski(k1_relat_1(X0_54),X0_55) != iProver_top
    | r1_tarski(k2_relat_1(X0_54),X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k8_relset_1(X0_55,X1_55,X0_54,X1_54) = k10_relat_1(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_27357,plain,
    ( k8_relset_1(X0_55,X1_55,X0_54,X1_54) = k10_relat_1(X0_54,X1_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_27775,plain,
    ( k8_relset_1(X0_55,X1_55,X0_54,X1_54) = k10_relat_1(X0_54,X1_54)
    | r1_tarski(k1_relat_1(X0_54),X0_55) != iProver_top
    | r1_tarski(k2_relat_1(X0_54),X1_55) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_27358,c_27357])).

cnf(c_28953,plain,
    ( k8_relset_1(X0_55,X1_55,k7_relat_1(X0_54,X0_55),X1_54) = k10_relat_1(k7_relat_1(X0_54,X0_55),X1_54)
    | r1_tarski(k2_relat_1(k7_relat_1(X0_54,X0_55)),X1_55) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k7_relat_1(X0_54,X0_55)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27353,c_27775])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_660,plain,
    ( ~ v1_relat_1(X0_54)
    | v1_relat_1(k7_relat_1(X0_54,X0_55)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_703,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k7_relat_1(X0_54,X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_31519,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(X0_54,X0_55)),X1_55) != iProver_top
    | k8_relset_1(X0_55,X1_55,k7_relat_1(X0_54,X0_55),X1_54) = k10_relat_1(k7_relat_1(X0_54,X0_55),X1_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28953,c_703])).

cnf(c_31520,plain,
    ( k8_relset_1(X0_55,X1_55,k7_relat_1(X0_54,X0_55),X1_54) = k10_relat_1(k7_relat_1(X0_54,X0_55),X1_54)
    | r1_tarski(k2_relat_1(k7_relat_1(X0_54,X0_55)),X1_55) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_31519])).

cnf(c_31529,plain,
    ( k8_relset_1(X0_55,X1_55,k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54)
    | r1_tarski(k9_relat_1(sK3,X0_55),X1_55) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_27688,c_31520])).

cnf(c_9597,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_9598,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9597])).

cnf(c_31793,plain,
    ( r1_tarski(k9_relat_1(sK3,X0_55),X1_55) != iProver_top
    | k8_relset_1(X0_55,X1_55,k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31529,c_37,c_9598])).

cnf(c_31794,plain,
    ( k8_relset_1(X0_55,X1_55,k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54)
    | r1_tarski(k9_relat_1(sK3,X0_55),X1_55) != iProver_top ),
    inference(renaming,[status(thm)],[c_31793])).

cnf(c_31802,plain,
    ( k8_relset_1(X0_55,u1_struct_0(sK1),k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) ),
    inference(superposition,[status(thm)],[c_27896,c_31794])).

cnf(c_27735,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_54) = k10_relat_1(sK3,X0_54) ),
    inference(superposition,[status(thm)],[c_27361,c_27357])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_435,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_647,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_partfun1(X0_55,X1_55,sK3,X2_55) = k7_relat_1(sK3,X2_55) ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_27359,plain,
    ( k2_partfun1(X0_55,X1_55,sK3,X2_55) = k7_relat_1(sK3,X2_55)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_27541,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55) ),
    inference(superposition,[status(thm)],[c_27361,c_27359])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_341,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK2 != X3
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_342,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_346,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_342,c_26,c_25,c_24])).

cnf(c_347,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_346])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_347])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_387,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_18])).

cnf(c_388,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_387])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_453,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_388,c_21])).

cnf(c_454,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_456,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_23,c_22,c_16])).

cnf(c_504,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_456])).

cnf(c_645,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_504])).

cnf(c_27544,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_27541,c_645])).

cnf(c_13,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_652,negated_conjecture,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_27665,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_27544,c_652])).

cnf(c_27866,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_27735,c_27665])).

cnf(c_61011,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_31802,c_27866])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_651,negated_conjecture,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_27363,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_27867,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27735,c_27363])).

cnf(c_11,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_419,plain,
    ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_420,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_648,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0_54),X0_55)
    | ~ v1_relat_1(sK3)
    | k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(sK3,X0_54) ),
    inference(subtyping,[status(esa)],[c_420])).

cnf(c_27170,plain,
    ( ~ r1_tarski(k10_relat_1(sK3,X0_54),X0_55)
    | k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(sK3,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_16,c_9597])).

cnf(c_27345,plain,
    ( k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(sK3,X0_54)
    | r1_tarski(k10_relat_1(sK3,X0_54),X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27170])).

cnf(c_27876,plain,
    ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_27867,c_27345])).

cnf(c_61012,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_61011,c_27876])).

cnf(c_61013,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_61012])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:16:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 19.21/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.21/2.98  
% 19.21/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.21/2.98  
% 19.21/2.98  ------  iProver source info
% 19.21/2.98  
% 19.21/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.21/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.21/2.98  git: non_committed_changes: false
% 19.21/2.98  git: last_make_outside_of_git: false
% 19.21/2.98  
% 19.21/2.98  ------ 
% 19.21/2.98  ------ Parsing...
% 19.21/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  ------ Proving...
% 19.21/2.98  ------ Problem Properties 
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  clauses                                 18
% 19.21/2.98  conjectures                             4
% 19.21/2.98  EPR                                     0
% 19.21/2.98  Horn                                    18
% 19.21/2.98  unary                                   5
% 19.21/2.98  binary                                  10
% 19.21/2.98  lits                                    35
% 19.21/2.98  lits eq                                 9
% 19.21/2.98  fd_pure                                 0
% 19.21/2.98  fd_pseudo                               0
% 19.21/2.98  fd_cond                                 0
% 19.21/2.98  fd_pseudo_cond                          0
% 19.21/2.98  AC symbols                              0
% 19.21/2.98  
% 19.21/2.98  ------ Input Options Time Limit: Unbounded
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 19.21/2.98  Current options:
% 19.21/2.98  ------ 
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing...
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.21/2.98  
% 19.21/2.98  ------ Proving...
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  % SZS status Theorem for theBenchmark.p
% 19.21/2.98  
% 19.21/2.98   Resolution empty clause
% 19.21/2.98  
% 19.21/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.21/2.98  
% 19.21/2.98  fof(f13,conjecture,(
% 19.21/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f14,negated_conjecture,(
% 19.21/2.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 19.21/2.98    inference(negated_conjecture,[],[f13])).
% 19.21/2.98  
% 19.21/2.98  fof(f30,plain,(
% 19.21/2.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.21/2.98    inference(ennf_transformation,[],[f14])).
% 19.21/2.98  
% 19.21/2.98  fof(f31,plain,(
% 19.21/2.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.21/2.98    inference(flattening,[],[f30])).
% 19.21/2.98  
% 19.21/2.98  fof(f37,plain,(
% 19.21/2.98    ( ! [X2,X0,X3,X1] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,sK4),u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 19.21/2.98    introduced(choice_axiom,[])).
% 19.21/2.98  
% 19.21/2.98  fof(f36,plain,(
% 19.21/2.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,sK3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 19.21/2.98    introduced(choice_axiom,[])).
% 19.21/2.98  
% 19.21/2.98  fof(f35,plain,(
% 19.21/2.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 19.21/2.98    introduced(choice_axiom,[])).
% 19.21/2.98  
% 19.21/2.98  fof(f34,plain,(
% 19.21/2.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(X0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 19.21/2.98    introduced(choice_axiom,[])).
% 19.21/2.98  
% 19.21/2.98  fof(f33,plain,(
% 19.21/2.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 19.21/2.98    introduced(choice_axiom,[])).
% 19.21/2.98  
% 19.21/2.98  fof(f38,plain,(
% 19.21/2.98    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 19.21/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f31,f37,f36,f35,f34,f33])).
% 19.21/2.98  
% 19.21/2.98  fof(f62,plain,(
% 19.21/2.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f7,axiom,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f20,plain,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.21/2.98    inference(ennf_transformation,[],[f7])).
% 19.21/2.98  
% 19.21/2.98  fof(f46,plain,(
% 19.21/2.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f20])).
% 19.21/2.98  
% 19.21/2.98  fof(f6,axiom,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f19,plain,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.21/2.98    inference(ennf_transformation,[],[f6])).
% 19.21/2.98  
% 19.21/2.98  fof(f45,plain,(
% 19.21/2.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f19])).
% 19.21/2.98  
% 19.21/2.98  fof(f1,axiom,(
% 19.21/2.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f32,plain,(
% 19.21/2.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.21/2.98    inference(nnf_transformation,[],[f1])).
% 19.21/2.98  
% 19.21/2.98  fof(f39,plain,(
% 19.21/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f32])).
% 19.21/2.98  
% 19.21/2.98  fof(f5,axiom,(
% 19.21/2.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f18,plain,(
% 19.21/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.21/2.98    inference(ennf_transformation,[],[f5])).
% 19.21/2.98  
% 19.21/2.98  fof(f44,plain,(
% 19.21/2.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f18])).
% 19.21/2.98  
% 19.21/2.98  fof(f3,axiom,(
% 19.21/2.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f16,plain,(
% 19.21/2.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.21/2.98    inference(ennf_transformation,[],[f3])).
% 19.21/2.98  
% 19.21/2.98  fof(f42,plain,(
% 19.21/2.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f16])).
% 19.21/2.98  
% 19.21/2.98  fof(f4,axiom,(
% 19.21/2.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f17,plain,(
% 19.21/2.98    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 19.21/2.98    inference(ennf_transformation,[],[f4])).
% 19.21/2.98  
% 19.21/2.98  fof(f43,plain,(
% 19.21/2.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f17])).
% 19.21/2.98  
% 19.21/2.98  fof(f9,axiom,(
% 19.21/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f22,plain,(
% 19.21/2.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 19.21/2.98    inference(ennf_transformation,[],[f9])).
% 19.21/2.98  
% 19.21/2.98  fof(f23,plain,(
% 19.21/2.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 19.21/2.98    inference(flattening,[],[f22])).
% 19.21/2.98  
% 19.21/2.98  fof(f48,plain,(
% 19.21/2.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f23])).
% 19.21/2.98  
% 19.21/2.98  fof(f8,axiom,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f21,plain,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.21/2.98    inference(ennf_transformation,[],[f8])).
% 19.21/2.98  
% 19.21/2.98  fof(f47,plain,(
% 19.21/2.98    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.21/2.98    inference(cnf_transformation,[],[f21])).
% 19.21/2.98  
% 19.21/2.98  fof(f2,axiom,(
% 19.21/2.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f15,plain,(
% 19.21/2.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 19.21/2.98    inference(ennf_transformation,[],[f2])).
% 19.21/2.98  
% 19.21/2.98  fof(f41,plain,(
% 19.21/2.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f15])).
% 19.21/2.98  
% 19.21/2.98  fof(f10,axiom,(
% 19.21/2.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f24,plain,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.21/2.98    inference(ennf_transformation,[],[f10])).
% 19.21/2.98  
% 19.21/2.98  fof(f25,plain,(
% 19.21/2.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.21/2.98    inference(flattening,[],[f24])).
% 19.21/2.98  
% 19.21/2.98  fof(f49,plain,(
% 19.21/2.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f25])).
% 19.21/2.98  
% 19.21/2.98  fof(f60,plain,(
% 19.21/2.98    v1_funct_1(sK3)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f61,plain,(
% 19.21/2.98    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f12,axiom,(
% 19.21/2.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f28,plain,(
% 19.21/2.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.21/2.98    inference(ennf_transformation,[],[f12])).
% 19.21/2.98  
% 19.21/2.98  fof(f29,plain,(
% 19.21/2.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.21/2.98    inference(flattening,[],[f28])).
% 19.21/2.98  
% 19.21/2.98  fof(f51,plain,(
% 19.21/2.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f29])).
% 19.21/2.98  
% 19.21/2.98  fof(f59,plain,(
% 19.21/2.98    m1_pre_topc(sK2,sK0)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f52,plain,(
% 19.21/2.98    ~v2_struct_0(sK0)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f53,plain,(
% 19.21/2.98    v2_pre_topc(sK0)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f54,plain,(
% 19.21/2.98    l1_pre_topc(sK0)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f57,plain,(
% 19.21/2.98    l1_pre_topc(sK1)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f55,plain,(
% 19.21/2.98    ~v2_struct_0(sK1)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f56,plain,(
% 19.21/2.98    v2_pre_topc(sK1)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f65,plain,(
% 19.21/2.98    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f64,plain,(
% 19.21/2.98    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 19.21/2.98    inference(cnf_transformation,[],[f38])).
% 19.21/2.98  
% 19.21/2.98  fof(f11,axiom,(
% 19.21/2.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 19.21/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.21/2.98  
% 19.21/2.98  fof(f26,plain,(
% 19.21/2.98    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.21/2.98    inference(ennf_transformation,[],[f11])).
% 19.21/2.98  
% 19.21/2.98  fof(f27,plain,(
% 19.21/2.98    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.21/2.98    inference(flattening,[],[f26])).
% 19.21/2.98  
% 19.21/2.98  fof(f50,plain,(
% 19.21/2.98    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.21/2.98    inference(cnf_transformation,[],[f27])).
% 19.21/2.98  
% 19.21/2.98  cnf(c_16,negated_conjecture,
% 19.21/2.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 19.21/2.98      inference(cnf_transformation,[],[f62]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_649,negated_conjecture,
% 19.21/2.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_16]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27361,plain,
% 19.21/2.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_7,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.21/2.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 19.21/2.98      inference(cnf_transformation,[],[f46]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_655,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 19.21/2.98      | k7_relset_1(X0_55,X1_55,X0_54,X2_55) = k9_relat_1(X0_54,X2_55) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_7]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27356,plain,
% 19.21/2.98      ( k7_relset_1(X0_55,X1_55,X0_54,X2_55) = k9_relat_1(X0_54,X2_55)
% 19.21/2.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27712,plain,
% 19.21/2.98      ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_55) = k9_relat_1(sK3,X0_55) ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27361,c_27356]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_6,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.21/2.98      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 19.21/2.98      inference(cnf_transformation,[],[f45]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_656,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 19.21/2.98      | m1_subset_1(k7_relset_1(X0_55,X1_55,X0_54,X2_55),k1_zfmisc_1(X1_55)) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_6]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27355,plain,
% 19.21/2.98      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 19.21/2.98      | m1_subset_1(k7_relset_1(X0_55,X1_55,X0_54,X2_55),k1_zfmisc_1(X1_55)) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27852,plain,
% 19.21/2.98      ( m1_subset_1(k9_relat_1(sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 19.21/2.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27712,c_27355]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_37,plain,
% 19.21/2.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27889,plain,
% 19.21/2.98      ( m1_subset_1(k9_relat_1(sK3,X0_55),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.21/2.98      inference(global_propositional_subsumption,[status(thm)],[c_27852,c_37]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_1,plain,
% 19.21/2.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.21/2.98      inference(cnf_transformation,[],[f39]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_661,plain,
% 19.21/2.98      ( r1_tarski(X0_54,X0_55) | ~ m1_subset_1(X0_54,k1_zfmisc_1(X0_55)) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_1]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27350,plain,
% 19.21/2.98      ( r1_tarski(X0_54,X0_55) = iProver_top
% 19.21/2.98      | m1_subset_1(X0_54,k1_zfmisc_1(X0_55)) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27896,plain,
% 19.21/2.98      ( r1_tarski(k9_relat_1(sK3,X0_55),u1_struct_0(sK1)) = iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27889,c_27350]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_5,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f44]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_657,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 19.21/2.98      | v1_relat_1(X0_54) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_5]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27354,plain,
% 19.21/2.98      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 19.21/2.98      | v1_relat_1(X0_54) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27676,plain,
% 19.21/2.98      ( v1_relat_1(sK3) = iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27361,c_27354]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_3,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 19.21/2.98      inference(cnf_transformation,[],[f42]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_659,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0_54)
% 19.21/2.98      | k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_3]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27352,plain,
% 19.21/2.98      ( k2_relat_1(k7_relat_1(X0_54,X0_55)) = k9_relat_1(X0_54,X0_55)
% 19.21/2.98      | v1_relat_1(X0_54) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27688,plain,
% 19.21/2.98      ( k2_relat_1(k7_relat_1(sK3,X0_55)) = k9_relat_1(sK3,X0_55) ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27676,c_27352]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_4,plain,
% 19.21/2.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f43]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_658,plain,
% 19.21/2.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X0_55)),X0_55)
% 19.21/2.98      | ~ v1_relat_1(X0_54) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_4]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27353,plain,
% 19.21/2.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0_54,X0_55)),X0_55) = iProver_top
% 19.21/2.98      | v1_relat_1(X0_54) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_9,plain,
% 19.21/2.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 19.21/2.98      | ~ r1_tarski(k2_relat_1(X0),X2)
% 19.21/2.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.21/2.98      | ~ v1_relat_1(X0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f48]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_653,plain,
% 19.21/2.98      ( ~ r1_tarski(k1_relat_1(X0_54),X0_55)
% 19.21/2.98      | ~ r1_tarski(k2_relat_1(X0_54),X1_55)
% 19.21/2.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 19.21/2.98      | ~ v1_relat_1(X0_54) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_9]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27358,plain,
% 19.21/2.98      ( r1_tarski(k1_relat_1(X0_54),X0_55) != iProver_top
% 19.21/2.98      | r1_tarski(k2_relat_1(X0_54),X1_55) != iProver_top
% 19.21/2.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) = iProver_top
% 19.21/2.98      | v1_relat_1(X0_54) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_8,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.21/2.98      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 19.21/2.98      inference(cnf_transformation,[],[f47]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_654,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 19.21/2.98      | k8_relset_1(X0_55,X1_55,X0_54,X1_54) = k10_relat_1(X0_54,X1_54) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_8]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27357,plain,
% 19.21/2.98      ( k8_relset_1(X0_55,X1_55,X0_54,X1_54) = k10_relat_1(X0_54,X1_54)
% 19.21/2.98      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27775,plain,
% 19.21/2.98      ( k8_relset_1(X0_55,X1_55,X0_54,X1_54) = k10_relat_1(X0_54,X1_54)
% 19.21/2.98      | r1_tarski(k1_relat_1(X0_54),X0_55) != iProver_top
% 19.21/2.98      | r1_tarski(k2_relat_1(X0_54),X1_55) != iProver_top
% 19.21/2.98      | v1_relat_1(X0_54) != iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27358,c_27357]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_28953,plain,
% 19.21/2.98      ( k8_relset_1(X0_55,X1_55,k7_relat_1(X0_54,X0_55),X1_54) = k10_relat_1(k7_relat_1(X0_54,X0_55),X1_54)
% 19.21/2.98      | r1_tarski(k2_relat_1(k7_relat_1(X0_54,X0_55)),X1_55) != iProver_top
% 19.21/2.98      | v1_relat_1(X0_54) != iProver_top
% 19.21/2.98      | v1_relat_1(k7_relat_1(X0_54,X0_55)) != iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27353,c_27775]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_2,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 19.21/2.98      inference(cnf_transformation,[],[f41]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_660,plain,
% 19.21/2.98      ( ~ v1_relat_1(X0_54) | v1_relat_1(k7_relat_1(X0_54,X0_55)) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_2]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_703,plain,
% 19.21/2.98      ( v1_relat_1(X0_54) != iProver_top
% 19.21/2.98      | v1_relat_1(k7_relat_1(X0_54,X0_55)) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_31519,plain,
% 19.21/2.98      ( v1_relat_1(X0_54) != iProver_top
% 19.21/2.98      | r1_tarski(k2_relat_1(k7_relat_1(X0_54,X0_55)),X1_55) != iProver_top
% 19.21/2.98      | k8_relset_1(X0_55,X1_55,k7_relat_1(X0_54,X0_55),X1_54) = k10_relat_1(k7_relat_1(X0_54,X0_55),X1_54) ),
% 19.21/2.98      inference(global_propositional_subsumption,[status(thm)],[c_28953,c_703]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_31520,plain,
% 19.21/2.98      ( k8_relset_1(X0_55,X1_55,k7_relat_1(X0_54,X0_55),X1_54) = k10_relat_1(k7_relat_1(X0_54,X0_55),X1_54)
% 19.21/2.98      | r1_tarski(k2_relat_1(k7_relat_1(X0_54,X0_55)),X1_55) != iProver_top
% 19.21/2.98      | v1_relat_1(X0_54) != iProver_top ),
% 19.21/2.98      inference(renaming,[status(thm)],[c_31519]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_31529,plain,
% 19.21/2.98      ( k8_relset_1(X0_55,X1_55,k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54)
% 19.21/2.98      | r1_tarski(k9_relat_1(sK3,X0_55),X1_55) != iProver_top
% 19.21/2.98      | v1_relat_1(sK3) != iProver_top ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27688,c_31520]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_9597,plain,
% 19.21/2.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 19.21/2.98      | v1_relat_1(sK3) ),
% 19.21/2.98      inference(instantiation,[status(thm)],[c_657]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_9598,plain,
% 19.21/2.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 19.21/2.98      | v1_relat_1(sK3) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_9597]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_31793,plain,
% 19.21/2.98      ( r1_tarski(k9_relat_1(sK3,X0_55),X1_55) != iProver_top
% 19.21/2.98      | k8_relset_1(X0_55,X1_55,k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) ),
% 19.21/2.98      inference(global_propositional_subsumption,
% 19.21/2.98                [status(thm)],
% 19.21/2.98                [c_31529,c_37,c_9598]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_31794,plain,
% 19.21/2.98      ( k8_relset_1(X0_55,X1_55,k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54)
% 19.21/2.98      | r1_tarski(k9_relat_1(sK3,X0_55),X1_55) != iProver_top ),
% 19.21/2.98      inference(renaming,[status(thm)],[c_31793]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_31802,plain,
% 19.21/2.98      ( k8_relset_1(X0_55,u1_struct_0(sK1),k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27896,c_31794]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27735,plain,
% 19.21/2.98      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_54) = k10_relat_1(sK3,X0_54) ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27361,c_27357]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_10,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 19.21/2.98      inference(cnf_transformation,[],[f49]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_18,negated_conjecture,
% 19.21/2.98      ( v1_funct_1(sK3) ),
% 19.21/2.98      inference(cnf_transformation,[],[f60]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_434,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.21/2.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 19.21/2.98      | sK3 != X0 ),
% 19.21/2.98      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_435,plain,
% 19.21/2.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 19.21/2.98      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 19.21/2.98      inference(unflattening,[status(thm)],[c_434]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_647,plain,
% 19.21/2.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 19.21/2.98      | k2_partfun1(X0_55,X1_55,sK3,X2_55) = k7_relat_1(sK3,X2_55) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_435]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27359,plain,
% 19.21/2.98      ( k2_partfun1(X0_55,X1_55,sK3,X2_55) = k7_relat_1(sK3,X2_55)
% 19.21/2.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27541,plain,
% 19.21/2.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0_55) = k7_relat_1(sK3,X0_55) ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27361,c_27359]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_17,negated_conjecture,
% 19.21/2.98      ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 19.21/2.98      inference(cnf_transformation,[],[f61]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_12,plain,
% 19.21/2.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.21/2.98      | ~ m1_pre_topc(X3,X1)
% 19.21/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.21/2.98      | v2_struct_0(X1)
% 19.21/2.98      | v2_struct_0(X2)
% 19.21/2.98      | ~ v2_pre_topc(X2)
% 19.21/2.98      | ~ v2_pre_topc(X1)
% 19.21/2.98      | ~ l1_pre_topc(X2)
% 19.21/2.98      | ~ l1_pre_topc(X1)
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 19.21/2.98      inference(cnf_transformation,[],[f51]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_19,negated_conjecture,
% 19.21/2.98      ( m1_pre_topc(sK2,sK0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f59]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_341,plain,
% 19.21/2.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 19.21/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 19.21/2.98      | v2_struct_0(X1)
% 19.21/2.98      | v2_struct_0(X2)
% 19.21/2.98      | ~ v2_pre_topc(X1)
% 19.21/2.98      | ~ v2_pre_topc(X2)
% 19.21/2.98      | ~ l1_pre_topc(X1)
% 19.21/2.98      | ~ l1_pre_topc(X2)
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 19.21/2.98      | sK2 != X3
% 19.21/2.98      | sK0 != X1 ),
% 19.21/2.98      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_342,plain,
% 19.21/2.98      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 19.21/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 19.21/2.98      | v2_struct_0(X1)
% 19.21/2.98      | v2_struct_0(sK0)
% 19.21/2.98      | ~ v2_pre_topc(X1)
% 19.21/2.98      | ~ v2_pre_topc(sK0)
% 19.21/2.98      | ~ l1_pre_topc(X1)
% 19.21/2.98      | ~ l1_pre_topc(sK0)
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 19.21/2.98      inference(unflattening,[status(thm)],[c_341]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_26,negated_conjecture,
% 19.21/2.98      ( ~ v2_struct_0(sK0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f52]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_25,negated_conjecture,
% 19.21/2.98      ( v2_pre_topc(sK0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f53]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_24,negated_conjecture,
% 19.21/2.98      ( l1_pre_topc(sK0) ),
% 19.21/2.98      inference(cnf_transformation,[],[f54]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_346,plain,
% 19.21/2.98      ( ~ l1_pre_topc(X1)
% 19.21/2.98      | v2_struct_0(X1)
% 19.21/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 19.21/2.98      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 19.21/2.98      | ~ v2_pre_topc(X1)
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 19.21/2.98      inference(global_propositional_subsumption,
% 19.21/2.98                [status(thm)],
% 19.21/2.98                [c_342,c_26,c_25,c_24]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_347,plain,
% 19.21/2.98      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 19.21/2.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 19.21/2.98      | v2_struct_0(X1)
% 19.21/2.98      | ~ v2_pre_topc(X1)
% 19.21/2.98      | ~ l1_pre_topc(X1)
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2) ),
% 19.21/2.98      inference(renaming,[status(thm)],[c_346]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_382,plain,
% 19.21/2.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 19.21/2.98      | v2_struct_0(X1)
% 19.21/2.98      | ~ v2_pre_topc(X1)
% 19.21/2.98      | ~ l1_pre_topc(X1)
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK0,X1,X0,sK2)
% 19.21/2.98      | u1_struct_0(X1) != u1_struct_0(sK1)
% 19.21/2.98      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 19.21/2.98      | sK3 != X0 ),
% 19.21/2.98      inference(resolution_lifted,[status(thm)],[c_17,c_347]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_383,plain,
% 19.21/2.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 19.21/2.98      | v2_struct_0(X0)
% 19.21/2.98      | ~ v2_pre_topc(X0)
% 19.21/2.98      | ~ l1_pre_topc(X0)
% 19.21/2.98      | ~ v1_funct_1(sK3)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 19.21/2.98      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 19.21/2.98      inference(unflattening,[status(thm)],[c_382]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_387,plain,
% 19.21/2.98      ( ~ l1_pre_topc(X0)
% 19.21/2.98      | ~ v2_pre_topc(X0)
% 19.21/2.98      | v2_struct_0(X0)
% 19.21/2.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 19.21/2.98      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 19.21/2.98      inference(global_propositional_subsumption,[status(thm)],[c_383,c_18]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_388,plain,
% 19.21/2.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 19.21/2.98      | v2_struct_0(X0)
% 19.21/2.98      | ~ v2_pre_topc(X0)
% 19.21/2.98      | ~ l1_pre_topc(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 19.21/2.98      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 19.21/2.98      inference(renaming,[status(thm)],[c_387]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_21,negated_conjecture,
% 19.21/2.98      ( l1_pre_topc(sK1) ),
% 19.21/2.98      inference(cnf_transformation,[],[f57]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_453,plain,
% 19.21/2.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
% 19.21/2.98      | v2_struct_0(X0)
% 19.21/2.98      | ~ v2_pre_topc(X0)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,X0,sK3,sK2)
% 19.21/2.98      | u1_struct_0(X0) != u1_struct_0(sK1)
% 19.21/2.98      | sK1 != X0 ),
% 19.21/2.98      inference(resolution_lifted,[status(thm)],[c_388,c_21]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_454,plain,
% 19.21/2.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 19.21/2.98      | v2_struct_0(sK1)
% 19.21/2.98      | ~ v2_pre_topc(sK1)
% 19.21/2.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 19.21/2.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 19.21/2.98      inference(unflattening,[status(thm)],[c_453]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_23,negated_conjecture,
% 19.21/2.98      ( ~ v2_struct_0(sK1) ),
% 19.21/2.98      inference(cnf_transformation,[],[f55]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_22,negated_conjecture,
% 19.21/2.98      ( v2_pre_topc(sK1) ),
% 19.21/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_456,plain,
% 19.21/2.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2)
% 19.21/2.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 19.21/2.98      inference(global_propositional_subsumption,
% 19.21/2.98                [status(thm)],
% 19.21/2.98                [c_454,c_23,c_22,c_16]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_504,plain,
% 19.21/2.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 19.21/2.98      inference(equality_resolution_simp,[status(thm)],[c_456]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_645,plain,
% 19.21/2.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK3,sK2) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_504]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27544,plain,
% 19.21/2.98      ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 19.21/2.98      inference(demodulation,[status(thm)],[c_27541,c_645]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_13,negated_conjecture,
% 19.21/2.98      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 19.21/2.98      inference(cnf_transformation,[],[f65]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_652,negated_conjecture,
% 19.21/2.98      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_13]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27665,plain,
% 19.21/2.98      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) ),
% 19.21/2.98      inference(demodulation,[status(thm)],[c_27544,c_652]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27866,plain,
% 19.21/2.98      ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 19.21/2.98      inference(demodulation,[status(thm)],[c_27735,c_27665]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_61011,plain,
% 19.21/2.98      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k10_relat_1(sK3,sK4) ),
% 19.21/2.98      inference(demodulation,[status(thm)],[c_31802,c_27866]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_14,negated_conjecture,
% 19.21/2.98      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 19.21/2.98      inference(cnf_transformation,[],[f64]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_651,negated_conjecture,
% 19.21/2.98      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_14]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27363,plain,
% 19.21/2.98      ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27867,plain,
% 19.21/2.98      ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 19.21/2.98      inference(demodulation,[status(thm)],[c_27735,c_27363]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_11,plain,
% 19.21/2.98      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 19.21/2.98      | ~ v1_funct_1(X0)
% 19.21/2.98      | ~ v1_relat_1(X0)
% 19.21/2.98      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1) ),
% 19.21/2.98      inference(cnf_transformation,[],[f50]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_419,plain,
% 19.21/2.98      ( ~ r1_tarski(k10_relat_1(X0,X1),X2)
% 19.21/2.98      | ~ v1_relat_1(X0)
% 19.21/2.98      | k10_relat_1(k7_relat_1(X0,X2),X1) = k10_relat_1(X0,X1)
% 19.21/2.98      | sK3 != X0 ),
% 19.21/2.98      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_420,plain,
% 19.21/2.98      ( ~ r1_tarski(k10_relat_1(sK3,X0),X1)
% 19.21/2.98      | ~ v1_relat_1(sK3)
% 19.21/2.98      | k10_relat_1(k7_relat_1(sK3,X1),X0) = k10_relat_1(sK3,X0) ),
% 19.21/2.98      inference(unflattening,[status(thm)],[c_419]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_648,plain,
% 19.21/2.98      ( ~ r1_tarski(k10_relat_1(sK3,X0_54),X0_55)
% 19.21/2.98      | ~ v1_relat_1(sK3)
% 19.21/2.98      | k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(sK3,X0_54) ),
% 19.21/2.98      inference(subtyping,[status(esa)],[c_420]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27170,plain,
% 19.21/2.98      ( ~ r1_tarski(k10_relat_1(sK3,X0_54),X0_55)
% 19.21/2.98      | k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(sK3,X0_54) ),
% 19.21/2.98      inference(global_propositional_subsumption,
% 19.21/2.98                [status(thm)],
% 19.21/2.98                [c_648,c_16,c_9597]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27345,plain,
% 19.21/2.98      ( k10_relat_1(k7_relat_1(sK3,X0_55),X0_54) = k10_relat_1(sK3,X0_54)
% 19.21/2.98      | r1_tarski(k10_relat_1(sK3,X0_54),X0_55) != iProver_top ),
% 19.21/2.98      inference(predicate_to_equality,[status(thm)],[c_27170]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_27876,plain,
% 19.21/2.98      ( k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k10_relat_1(sK3,sK4) ),
% 19.21/2.98      inference(superposition,[status(thm)],[c_27867,c_27345]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_61012,plain,
% 19.21/2.98      ( k10_relat_1(sK3,sK4) != k10_relat_1(sK3,sK4) ),
% 19.21/2.98      inference(light_normalisation,[status(thm)],[c_61011,c_27876]) ).
% 19.21/2.98  
% 19.21/2.98  cnf(c_61013,plain,
% 19.21/2.98      ( $false ),
% 19.21/2.98      inference(equality_resolution_simp,[status(thm)],[c_61012]) ).
% 19.21/2.98  
% 19.21/2.98  
% 19.21/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.21/2.98  
% 19.21/2.98  ------                               Statistics
% 19.21/2.98  
% 19.21/2.98  ------ Selected
% 19.21/2.98  
% 19.21/2.98  total_time:                             2.08
% 19.21/2.98  
%------------------------------------------------------------------------------
