%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:31 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 376 expanded)
%              Number of clauses        :   91 ( 113 expanded)
%              Number of leaves         :   19 ( 130 expanded)
%              Depth                    :   25
%              Number of atoms          :  561 (3388 expanded)
%              Number of equality atoms :  131 ( 414 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(X4,u1_struct_0(X2))
                       => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(X4,u1_struct_0(X2))
                         => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & r1_tarski(X4,u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4)
        & r1_tarski(sK4,u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
              & r1_tarski(X4,u1_struct_0(X2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK3,X2),X4)
            & r1_tarski(X4,u1_struct_0(X2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                  & r1_tarski(X4,u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK2),X4)
                & r1_tarski(X4,u1_struct_0(sK2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(X3) )
        & m1_pre_topc(sK2,X1)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK1,X0,X3,X2),X4)
                    & r1_tarski(X4,u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & r1_tarski(X4,u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
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
                      ( k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & r1_tarski(X4,u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & r1_tarski(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f36,f42,f41,f40,f39,f38])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_581,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_921,plain,
    ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_573,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_928,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_577,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_925,plain,
    ( r1_tarski(X0_53,X1_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_1650,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_925])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_305,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_9,c_2])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_315,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_305,c_8])).

cnf(c_572,plain,
    ( r1_tarski(k2_relat_1(X0_53),X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_929,plain,
    ( r1_tarski(k2_relat_1(X0_53),X1_53) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_1825,plain,
    ( r1_tarski(X0_53,sK3) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_929])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_582,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_920,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_11,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_578,plain,
    ( ~ r1_tarski(k1_relat_1(X0_53),X1_53)
    | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_924,plain,
    ( r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
    | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_579,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | k7_relset_1(X1_53,X2_53,X0_53,X3_53) = k9_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_923,plain,
    ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_1662,plain,
    ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
    | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
    | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_923])).

cnf(c_3500,plain,
    ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top
    | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_1662])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_585,plain,
    ( ~ v1_relat_1(X0_53)
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_917,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_14437,plain,
    ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
    | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
    | v1_relat_1(X2_53) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3500,c_917])).

cnf(c_14442,plain,
    ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(X1_53,X0_53),X2_53) = k9_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
    | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_14437])).

cnf(c_15459,plain,
    ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_14442])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_1048,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_16523,plain,
    ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15459,c_39,c_1048])).

cnf(c_1571,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k9_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_928,c_923])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_402,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_571,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
    inference(subtyping,[status(esa)],[c_402])).

cnf(c_930,plain,
    ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1116,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_928,c_930])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_325,plain,
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
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_326,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_330,plain,
    ( ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_25,c_24,c_23])).

cnf(c_331,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_330])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
    | u1_struct_0(X1) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_331])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_20])).

cnf(c_370,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_433,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
    | u1_struct_0(X0) != u1_struct_0(sK0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_370,c_26])).

cnf(c_434,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_436,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_28,c_27,c_18])).

cnf(c_466,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_436])).

cnf(c_569,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_466])).

cnf(c_1144,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_1116,c_569])).

cnf(c_15,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_576,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1423,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1144,c_576])).

cnf(c_1753,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_1571,c_1423])).

cnf(c_16527,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_16523,c_1753])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_586,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_916,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_1219,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_916])).

cnf(c_1417,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1219,c_39,c_1048])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_575,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_926,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_583,plain,
    ( ~ r1_tarski(X0_53,X1_53)
    | ~ v1_relat_1(X2_53)
    | k9_relat_1(k7_relat_1(X2_53,X1_53),X0_53) = k9_relat_1(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_919,plain,
    ( k9_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k9_relat_1(X0_53,X2_53)
    | r1_tarski(X2_53,X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_1577,plain,
    ( k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK4) = k9_relat_1(X0_53,sK4)
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_919])).

cnf(c_1808,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1417,c_1577])).

cnf(c_16528,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_16527,c_1808])).

cnf(c_16529,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16528])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.21/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.01  
% 4.21/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.21/1.01  
% 4.21/1.01  ------  iProver source info
% 4.21/1.01  
% 4.21/1.01  git: date: 2020-06-30 10:37:57 +0100
% 4.21/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.21/1.01  git: non_committed_changes: false
% 4.21/1.01  git: last_make_outside_of_git: false
% 4.21/1.01  
% 4.21/1.01  ------ 
% 4.21/1.01  
% 4.21/1.01  ------ Input Options
% 4.21/1.01  
% 4.21/1.01  --out_options                           all
% 4.21/1.01  --tptp_safe_out                         true
% 4.21/1.01  --problem_path                          ""
% 4.21/1.01  --include_path                          ""
% 4.21/1.01  --clausifier                            res/vclausify_rel
% 4.21/1.01  --clausifier_options                    --mode clausify
% 4.21/1.01  --stdin                                 false
% 4.21/1.01  --stats_out                             all
% 4.21/1.01  
% 4.21/1.01  ------ General Options
% 4.21/1.01  
% 4.21/1.01  --fof                                   false
% 4.21/1.01  --time_out_real                         305.
% 4.21/1.01  --time_out_virtual                      -1.
% 4.21/1.01  --symbol_type_check                     false
% 4.21/1.01  --clausify_out                          false
% 4.21/1.01  --sig_cnt_out                           false
% 4.21/1.01  --trig_cnt_out                          false
% 4.21/1.01  --trig_cnt_out_tolerance                1.
% 4.21/1.01  --trig_cnt_out_sk_spl                   false
% 4.21/1.01  --abstr_cl_out                          false
% 4.21/1.01  
% 4.21/1.01  ------ Global Options
% 4.21/1.01  
% 4.21/1.01  --schedule                              default
% 4.21/1.01  --add_important_lit                     false
% 4.21/1.01  --prop_solver_per_cl                    1000
% 4.21/1.01  --min_unsat_core                        false
% 4.21/1.01  --soft_assumptions                      false
% 4.21/1.01  --soft_lemma_size                       3
% 4.21/1.01  --prop_impl_unit_size                   0
% 4.21/1.01  --prop_impl_unit                        []
% 4.21/1.01  --share_sel_clauses                     true
% 4.21/1.01  --reset_solvers                         false
% 4.21/1.01  --bc_imp_inh                            [conj_cone]
% 4.21/1.01  --conj_cone_tolerance                   3.
% 4.21/1.01  --extra_neg_conj                        none
% 4.21/1.01  --large_theory_mode                     true
% 4.21/1.01  --prolific_symb_bound                   200
% 4.21/1.01  --lt_threshold                          2000
% 4.21/1.01  --clause_weak_htbl                      true
% 4.21/1.01  --gc_record_bc_elim                     false
% 4.21/1.01  
% 4.21/1.01  ------ Preprocessing Options
% 4.21/1.01  
% 4.21/1.01  --preprocessing_flag                    true
% 4.21/1.01  --time_out_prep_mult                    0.1
% 4.21/1.01  --splitting_mode                        input
% 4.21/1.01  --splitting_grd                         true
% 4.21/1.01  --splitting_cvd                         false
% 4.21/1.01  --splitting_cvd_svl                     false
% 4.21/1.01  --splitting_nvd                         32
% 4.21/1.01  --sub_typing                            true
% 4.21/1.01  --prep_gs_sim                           true
% 4.21/1.01  --prep_unflatten                        true
% 4.21/1.01  --prep_res_sim                          true
% 4.21/1.01  --prep_upred                            true
% 4.21/1.01  --prep_sem_filter                       exhaustive
% 4.21/1.01  --prep_sem_filter_out                   false
% 4.21/1.01  --pred_elim                             true
% 4.21/1.01  --res_sim_input                         true
% 4.21/1.01  --eq_ax_congr_red                       true
% 4.21/1.01  --pure_diseq_elim                       true
% 4.21/1.01  --brand_transform                       false
% 4.21/1.01  --non_eq_to_eq                          false
% 4.21/1.01  --prep_def_merge                        true
% 4.21/1.01  --prep_def_merge_prop_impl              false
% 4.21/1.01  --prep_def_merge_mbd                    true
% 4.21/1.01  --prep_def_merge_tr_red                 false
% 4.21/1.01  --prep_def_merge_tr_cl                  false
% 4.21/1.01  --smt_preprocessing                     true
% 4.21/1.01  --smt_ac_axioms                         fast
% 4.21/1.01  --preprocessed_out                      false
% 4.21/1.01  --preprocessed_stats                    false
% 4.21/1.01  
% 4.21/1.01  ------ Abstraction refinement Options
% 4.21/1.01  
% 4.21/1.01  --abstr_ref                             []
% 4.21/1.01  --abstr_ref_prep                        false
% 4.21/1.01  --abstr_ref_until_sat                   false
% 4.21/1.01  --abstr_ref_sig_restrict                funpre
% 4.21/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.21/1.01  --abstr_ref_under                       []
% 4.21/1.01  
% 4.21/1.01  ------ SAT Options
% 4.21/1.01  
% 4.21/1.01  --sat_mode                              false
% 4.21/1.01  --sat_fm_restart_options                ""
% 4.21/1.01  --sat_gr_def                            false
% 4.21/1.01  --sat_epr_types                         true
% 4.21/1.01  --sat_non_cyclic_types                  false
% 4.21/1.01  --sat_finite_models                     false
% 4.21/1.01  --sat_fm_lemmas                         false
% 4.21/1.01  --sat_fm_prep                           false
% 4.21/1.01  --sat_fm_uc_incr                        true
% 4.21/1.01  --sat_out_model                         small
% 4.21/1.01  --sat_out_clauses                       false
% 4.21/1.01  
% 4.21/1.01  ------ QBF Options
% 4.21/1.01  
% 4.21/1.01  --qbf_mode                              false
% 4.21/1.01  --qbf_elim_univ                         false
% 4.21/1.01  --qbf_dom_inst                          none
% 4.21/1.01  --qbf_dom_pre_inst                      false
% 4.21/1.01  --qbf_sk_in                             false
% 4.21/1.01  --qbf_pred_elim                         true
% 4.21/1.01  --qbf_split                             512
% 4.21/1.01  
% 4.21/1.01  ------ BMC1 Options
% 4.21/1.01  
% 4.21/1.01  --bmc1_incremental                      false
% 4.21/1.01  --bmc1_axioms                           reachable_all
% 4.21/1.01  --bmc1_min_bound                        0
% 4.21/1.01  --bmc1_max_bound                        -1
% 4.21/1.01  --bmc1_max_bound_default                -1
% 4.21/1.01  --bmc1_symbol_reachability              true
% 4.21/1.01  --bmc1_property_lemmas                  false
% 4.21/1.01  --bmc1_k_induction                      false
% 4.21/1.01  --bmc1_non_equiv_states                 false
% 4.21/1.01  --bmc1_deadlock                         false
% 4.21/1.01  --bmc1_ucm                              false
% 4.21/1.01  --bmc1_add_unsat_core                   none
% 4.21/1.01  --bmc1_unsat_core_children              false
% 4.21/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.21/1.01  --bmc1_out_stat                         full
% 4.21/1.01  --bmc1_ground_init                      false
% 4.21/1.01  --bmc1_pre_inst_next_state              false
% 4.21/1.01  --bmc1_pre_inst_state                   false
% 4.21/1.01  --bmc1_pre_inst_reach_state             false
% 4.21/1.01  --bmc1_out_unsat_core                   false
% 4.21/1.01  --bmc1_aig_witness_out                  false
% 4.21/1.01  --bmc1_verbose                          false
% 4.21/1.01  --bmc1_dump_clauses_tptp                false
% 4.21/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.21/1.01  --bmc1_dump_file                        -
% 4.21/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.21/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.21/1.01  --bmc1_ucm_extend_mode                  1
% 4.21/1.01  --bmc1_ucm_init_mode                    2
% 4.21/1.01  --bmc1_ucm_cone_mode                    none
% 4.21/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.21/1.01  --bmc1_ucm_relax_model                  4
% 4.21/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.21/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.21/1.01  --bmc1_ucm_layered_model                none
% 4.21/1.01  --bmc1_ucm_max_lemma_size               10
% 4.21/1.01  
% 4.21/1.01  ------ AIG Options
% 4.21/1.01  
% 4.21/1.01  --aig_mode                              false
% 4.21/1.01  
% 4.21/1.01  ------ Instantiation Options
% 4.21/1.01  
% 4.21/1.01  --instantiation_flag                    true
% 4.21/1.01  --inst_sos_flag                         false
% 4.21/1.01  --inst_sos_phase                        true
% 4.21/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.21/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.21/1.01  --inst_lit_sel_side                     num_symb
% 4.21/1.01  --inst_solver_per_active                1400
% 4.21/1.01  --inst_solver_calls_frac                1.
% 4.21/1.01  --inst_passive_queue_type               priority_queues
% 4.21/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.21/1.01  --inst_passive_queues_freq              [25;2]
% 4.21/1.01  --inst_dismatching                      true
% 4.21/1.01  --inst_eager_unprocessed_to_passive     true
% 4.21/1.01  --inst_prop_sim_given                   true
% 4.21/1.01  --inst_prop_sim_new                     false
% 4.21/1.01  --inst_subs_new                         false
% 4.21/1.01  --inst_eq_res_simp                      false
% 4.21/1.01  --inst_subs_given                       false
% 4.21/1.01  --inst_orphan_elimination               true
% 4.21/1.01  --inst_learning_loop_flag               true
% 4.21/1.01  --inst_learning_start                   3000
% 4.21/1.01  --inst_learning_factor                  2
% 4.21/1.01  --inst_start_prop_sim_after_learn       3
% 4.21/1.01  --inst_sel_renew                        solver
% 4.21/1.01  --inst_lit_activity_flag                true
% 4.21/1.01  --inst_restr_to_given                   false
% 4.21/1.01  --inst_activity_threshold               500
% 4.21/1.01  --inst_out_proof                        true
% 4.21/1.01  
% 4.21/1.01  ------ Resolution Options
% 4.21/1.01  
% 4.21/1.01  --resolution_flag                       true
% 4.21/1.01  --res_lit_sel                           adaptive
% 4.21/1.01  --res_lit_sel_side                      none
% 4.21/1.01  --res_ordering                          kbo
% 4.21/1.01  --res_to_prop_solver                    active
% 4.21/1.01  --res_prop_simpl_new                    false
% 4.21/1.01  --res_prop_simpl_given                  true
% 4.21/1.01  --res_passive_queue_type                priority_queues
% 4.21/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.21/1.01  --res_passive_queues_freq               [15;5]
% 4.21/1.01  --res_forward_subs                      full
% 4.21/1.01  --res_backward_subs                     full
% 4.21/1.01  --res_forward_subs_resolution           true
% 4.21/1.01  --res_backward_subs_resolution          true
% 4.21/1.01  --res_orphan_elimination                true
% 4.21/1.01  --res_time_limit                        2.
% 4.21/1.01  --res_out_proof                         true
% 4.21/1.01  
% 4.21/1.01  ------ Superposition Options
% 4.21/1.01  
% 4.21/1.01  --superposition_flag                    true
% 4.21/1.01  --sup_passive_queue_type                priority_queues
% 4.21/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.21/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.21/1.01  --demod_completeness_check              fast
% 4.21/1.01  --demod_use_ground                      true
% 4.21/1.01  --sup_to_prop_solver                    passive
% 4.21/1.01  --sup_prop_simpl_new                    true
% 4.21/1.01  --sup_prop_simpl_given                  true
% 4.21/1.01  --sup_fun_splitting                     false
% 4.21/1.01  --sup_smt_interval                      50000
% 4.21/1.01  
% 4.21/1.01  ------ Superposition Simplification Setup
% 4.21/1.01  
% 4.21/1.01  --sup_indices_passive                   []
% 4.21/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.21/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.21/1.01  --sup_full_bw                           [BwDemod]
% 4.21/1.01  --sup_immed_triv                        [TrivRules]
% 4.21/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.21/1.01  --sup_immed_bw_main                     []
% 4.21/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.21/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.21/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.21/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.21/1.01  
% 4.21/1.01  ------ Combination Options
% 4.21/1.01  
% 4.21/1.01  --comb_res_mult                         3
% 4.21/1.01  --comb_sup_mult                         2
% 4.21/1.01  --comb_inst_mult                        10
% 4.21/1.01  
% 4.21/1.01  ------ Debug Options
% 4.21/1.01  
% 4.21/1.01  --dbg_backtrace                         false
% 4.21/1.01  --dbg_dump_prop_clauses                 false
% 4.21/1.01  --dbg_dump_prop_clauses_file            -
% 4.21/1.01  --dbg_out_stat                          false
% 4.21/1.01  ------ Parsing...
% 4.21/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.21/1.01  
% 4.21/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 4.21/1.01  
% 4.21/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.21/1.01  
% 4.21/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.21/1.01  ------ Proving...
% 4.21/1.01  ------ Problem Properties 
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  clauses                                 18
% 4.21/1.01  conjectures                             4
% 4.21/1.01  EPR                                     0
% 4.21/1.01  Horn                                    18
% 4.21/1.01  unary                                   6
% 4.21/1.01  binary                                  7
% 4.21/1.01  lits                                    36
% 4.21/1.01  lits eq                                 7
% 4.21/1.01  fd_pure                                 0
% 4.21/1.01  fd_pseudo                               0
% 4.21/1.01  fd_cond                                 0
% 4.21/1.01  fd_pseudo_cond                          0
% 4.21/1.01  AC symbols                              0
% 4.21/1.01  
% 4.21/1.01  ------ Schedule dynamic 5 is on 
% 4.21/1.01  
% 4.21/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  ------ 
% 4.21/1.01  Current options:
% 4.21/1.01  ------ 
% 4.21/1.01  
% 4.21/1.01  ------ Input Options
% 4.21/1.01  
% 4.21/1.01  --out_options                           all
% 4.21/1.01  --tptp_safe_out                         true
% 4.21/1.01  --problem_path                          ""
% 4.21/1.01  --include_path                          ""
% 4.21/1.01  --clausifier                            res/vclausify_rel
% 4.21/1.01  --clausifier_options                    --mode clausify
% 4.21/1.01  --stdin                                 false
% 4.21/1.01  --stats_out                             all
% 4.21/1.01  
% 4.21/1.01  ------ General Options
% 4.21/1.01  
% 4.21/1.01  --fof                                   false
% 4.21/1.01  --time_out_real                         305.
% 4.21/1.01  --time_out_virtual                      -1.
% 4.21/1.01  --symbol_type_check                     false
% 4.21/1.01  --clausify_out                          false
% 4.21/1.01  --sig_cnt_out                           false
% 4.21/1.01  --trig_cnt_out                          false
% 4.21/1.01  --trig_cnt_out_tolerance                1.
% 4.21/1.01  --trig_cnt_out_sk_spl                   false
% 4.21/1.01  --abstr_cl_out                          false
% 4.21/1.01  
% 4.21/1.01  ------ Global Options
% 4.21/1.01  
% 4.21/1.01  --schedule                              default
% 4.21/1.01  --add_important_lit                     false
% 4.21/1.01  --prop_solver_per_cl                    1000
% 4.21/1.01  --min_unsat_core                        false
% 4.21/1.01  --soft_assumptions                      false
% 4.21/1.01  --soft_lemma_size                       3
% 4.21/1.01  --prop_impl_unit_size                   0
% 4.21/1.01  --prop_impl_unit                        []
% 4.21/1.01  --share_sel_clauses                     true
% 4.21/1.01  --reset_solvers                         false
% 4.21/1.01  --bc_imp_inh                            [conj_cone]
% 4.21/1.01  --conj_cone_tolerance                   3.
% 4.21/1.01  --extra_neg_conj                        none
% 4.21/1.01  --large_theory_mode                     true
% 4.21/1.01  --prolific_symb_bound                   200
% 4.21/1.01  --lt_threshold                          2000
% 4.21/1.01  --clause_weak_htbl                      true
% 4.21/1.01  --gc_record_bc_elim                     false
% 4.21/1.01  
% 4.21/1.01  ------ Preprocessing Options
% 4.21/1.01  
% 4.21/1.01  --preprocessing_flag                    true
% 4.21/1.01  --time_out_prep_mult                    0.1
% 4.21/1.01  --splitting_mode                        input
% 4.21/1.01  --splitting_grd                         true
% 4.21/1.01  --splitting_cvd                         false
% 4.21/1.01  --splitting_cvd_svl                     false
% 4.21/1.01  --splitting_nvd                         32
% 4.21/1.01  --sub_typing                            true
% 4.21/1.01  --prep_gs_sim                           true
% 4.21/1.01  --prep_unflatten                        true
% 4.21/1.01  --prep_res_sim                          true
% 4.21/1.01  --prep_upred                            true
% 4.21/1.01  --prep_sem_filter                       exhaustive
% 4.21/1.01  --prep_sem_filter_out                   false
% 4.21/1.01  --pred_elim                             true
% 4.21/1.01  --res_sim_input                         true
% 4.21/1.01  --eq_ax_congr_red                       true
% 4.21/1.01  --pure_diseq_elim                       true
% 4.21/1.01  --brand_transform                       false
% 4.21/1.01  --non_eq_to_eq                          false
% 4.21/1.01  --prep_def_merge                        true
% 4.21/1.01  --prep_def_merge_prop_impl              false
% 4.21/1.01  --prep_def_merge_mbd                    true
% 4.21/1.01  --prep_def_merge_tr_red                 false
% 4.21/1.01  --prep_def_merge_tr_cl                  false
% 4.21/1.01  --smt_preprocessing                     true
% 4.21/1.01  --smt_ac_axioms                         fast
% 4.21/1.01  --preprocessed_out                      false
% 4.21/1.01  --preprocessed_stats                    false
% 4.21/1.01  
% 4.21/1.01  ------ Abstraction refinement Options
% 4.21/1.01  
% 4.21/1.01  --abstr_ref                             []
% 4.21/1.01  --abstr_ref_prep                        false
% 4.21/1.01  --abstr_ref_until_sat                   false
% 4.21/1.01  --abstr_ref_sig_restrict                funpre
% 4.21/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.21/1.01  --abstr_ref_under                       []
% 4.21/1.01  
% 4.21/1.01  ------ SAT Options
% 4.21/1.01  
% 4.21/1.01  --sat_mode                              false
% 4.21/1.01  --sat_fm_restart_options                ""
% 4.21/1.01  --sat_gr_def                            false
% 4.21/1.01  --sat_epr_types                         true
% 4.21/1.01  --sat_non_cyclic_types                  false
% 4.21/1.01  --sat_finite_models                     false
% 4.21/1.01  --sat_fm_lemmas                         false
% 4.21/1.01  --sat_fm_prep                           false
% 4.21/1.01  --sat_fm_uc_incr                        true
% 4.21/1.01  --sat_out_model                         small
% 4.21/1.01  --sat_out_clauses                       false
% 4.21/1.01  
% 4.21/1.01  ------ QBF Options
% 4.21/1.01  
% 4.21/1.01  --qbf_mode                              false
% 4.21/1.01  --qbf_elim_univ                         false
% 4.21/1.01  --qbf_dom_inst                          none
% 4.21/1.01  --qbf_dom_pre_inst                      false
% 4.21/1.01  --qbf_sk_in                             false
% 4.21/1.01  --qbf_pred_elim                         true
% 4.21/1.01  --qbf_split                             512
% 4.21/1.01  
% 4.21/1.01  ------ BMC1 Options
% 4.21/1.01  
% 4.21/1.01  --bmc1_incremental                      false
% 4.21/1.01  --bmc1_axioms                           reachable_all
% 4.21/1.01  --bmc1_min_bound                        0
% 4.21/1.01  --bmc1_max_bound                        -1
% 4.21/1.01  --bmc1_max_bound_default                -1
% 4.21/1.01  --bmc1_symbol_reachability              true
% 4.21/1.01  --bmc1_property_lemmas                  false
% 4.21/1.01  --bmc1_k_induction                      false
% 4.21/1.01  --bmc1_non_equiv_states                 false
% 4.21/1.01  --bmc1_deadlock                         false
% 4.21/1.01  --bmc1_ucm                              false
% 4.21/1.01  --bmc1_add_unsat_core                   none
% 4.21/1.01  --bmc1_unsat_core_children              false
% 4.21/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.21/1.01  --bmc1_out_stat                         full
% 4.21/1.01  --bmc1_ground_init                      false
% 4.21/1.01  --bmc1_pre_inst_next_state              false
% 4.21/1.01  --bmc1_pre_inst_state                   false
% 4.21/1.01  --bmc1_pre_inst_reach_state             false
% 4.21/1.01  --bmc1_out_unsat_core                   false
% 4.21/1.01  --bmc1_aig_witness_out                  false
% 4.21/1.01  --bmc1_verbose                          false
% 4.21/1.01  --bmc1_dump_clauses_tptp                false
% 4.21/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.21/1.01  --bmc1_dump_file                        -
% 4.21/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.21/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.21/1.01  --bmc1_ucm_extend_mode                  1
% 4.21/1.01  --bmc1_ucm_init_mode                    2
% 4.21/1.01  --bmc1_ucm_cone_mode                    none
% 4.21/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.21/1.01  --bmc1_ucm_relax_model                  4
% 4.21/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.21/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.21/1.01  --bmc1_ucm_layered_model                none
% 4.21/1.01  --bmc1_ucm_max_lemma_size               10
% 4.21/1.01  
% 4.21/1.01  ------ AIG Options
% 4.21/1.01  
% 4.21/1.01  --aig_mode                              false
% 4.21/1.01  
% 4.21/1.01  ------ Instantiation Options
% 4.21/1.01  
% 4.21/1.01  --instantiation_flag                    true
% 4.21/1.01  --inst_sos_flag                         false
% 4.21/1.01  --inst_sos_phase                        true
% 4.21/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.21/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.21/1.01  --inst_lit_sel_side                     none
% 4.21/1.01  --inst_solver_per_active                1400
% 4.21/1.01  --inst_solver_calls_frac                1.
% 4.21/1.01  --inst_passive_queue_type               priority_queues
% 4.21/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.21/1.01  --inst_passive_queues_freq              [25;2]
% 4.21/1.01  --inst_dismatching                      true
% 4.21/1.01  --inst_eager_unprocessed_to_passive     true
% 4.21/1.01  --inst_prop_sim_given                   true
% 4.21/1.01  --inst_prop_sim_new                     false
% 4.21/1.01  --inst_subs_new                         false
% 4.21/1.01  --inst_eq_res_simp                      false
% 4.21/1.01  --inst_subs_given                       false
% 4.21/1.01  --inst_orphan_elimination               true
% 4.21/1.01  --inst_learning_loop_flag               true
% 4.21/1.01  --inst_learning_start                   3000
% 4.21/1.01  --inst_learning_factor                  2
% 4.21/1.01  --inst_start_prop_sim_after_learn       3
% 4.21/1.01  --inst_sel_renew                        solver
% 4.21/1.01  --inst_lit_activity_flag                true
% 4.21/1.01  --inst_restr_to_given                   false
% 4.21/1.01  --inst_activity_threshold               500
% 4.21/1.01  --inst_out_proof                        true
% 4.21/1.01  
% 4.21/1.01  ------ Resolution Options
% 4.21/1.01  
% 4.21/1.01  --resolution_flag                       false
% 4.21/1.01  --res_lit_sel                           adaptive
% 4.21/1.01  --res_lit_sel_side                      none
% 4.21/1.01  --res_ordering                          kbo
% 4.21/1.01  --res_to_prop_solver                    active
% 4.21/1.01  --res_prop_simpl_new                    false
% 4.21/1.01  --res_prop_simpl_given                  true
% 4.21/1.01  --res_passive_queue_type                priority_queues
% 4.21/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.21/1.01  --res_passive_queues_freq               [15;5]
% 4.21/1.01  --res_forward_subs                      full
% 4.21/1.01  --res_backward_subs                     full
% 4.21/1.01  --res_forward_subs_resolution           true
% 4.21/1.01  --res_backward_subs_resolution          true
% 4.21/1.01  --res_orphan_elimination                true
% 4.21/1.01  --res_time_limit                        2.
% 4.21/1.01  --res_out_proof                         true
% 4.21/1.01  
% 4.21/1.01  ------ Superposition Options
% 4.21/1.01  
% 4.21/1.01  --superposition_flag                    true
% 4.21/1.01  --sup_passive_queue_type                priority_queues
% 4.21/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.21/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.21/1.01  --demod_completeness_check              fast
% 4.21/1.01  --demod_use_ground                      true
% 4.21/1.01  --sup_to_prop_solver                    passive
% 4.21/1.01  --sup_prop_simpl_new                    true
% 4.21/1.01  --sup_prop_simpl_given                  true
% 4.21/1.01  --sup_fun_splitting                     false
% 4.21/1.01  --sup_smt_interval                      50000
% 4.21/1.01  
% 4.21/1.01  ------ Superposition Simplification Setup
% 4.21/1.01  
% 4.21/1.01  --sup_indices_passive                   []
% 4.21/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.21/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.21/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.21/1.01  --sup_full_bw                           [BwDemod]
% 4.21/1.01  --sup_immed_triv                        [TrivRules]
% 4.21/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.21/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.21/1.01  --sup_immed_bw_main                     []
% 4.21/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.21/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.21/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.21/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.21/1.01  
% 4.21/1.01  ------ Combination Options
% 4.21/1.01  
% 4.21/1.01  --comb_res_mult                         3
% 4.21/1.01  --comb_sup_mult                         2
% 4.21/1.01  --comb_inst_mult                        10
% 4.21/1.01  
% 4.21/1.01  ------ Debug Options
% 4.21/1.01  
% 4.21/1.01  --dbg_backtrace                         false
% 4.21/1.01  --dbg_dump_prop_clauses                 false
% 4.21/1.01  --dbg_dump_prop_clauses_file            -
% 4.21/1.01  --dbg_out_stat                          false
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  ------ Proving...
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  % SZS status Theorem for theBenchmark.p
% 4.21/1.01  
% 4.21/1.01   Resolution empty clause
% 4.21/1.01  
% 4.21/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.21/1.01  
% 4.21/1.01  fof(f7,axiom,(
% 4.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f23,plain,(
% 4.21/1.01    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 4.21/1.01    inference(ennf_transformation,[],[f7])).
% 4.21/1.01  
% 4.21/1.01  fof(f51,plain,(
% 4.21/1.01    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f23])).
% 4.21/1.01  
% 4.21/1.01  fof(f15,conjecture,(
% 4.21/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f16,negated_conjecture,(
% 4.21/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 4.21/1.01    inference(negated_conjecture,[],[f15])).
% 4.21/1.01  
% 4.21/1.01  fof(f35,plain,(
% 4.21/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.21/1.01    inference(ennf_transformation,[],[f16])).
% 4.21/1.01  
% 4.21/1.01  fof(f36,plain,(
% 4.21/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.21/1.01    inference(flattening,[],[f35])).
% 4.21/1.01  
% 4.21/1.01  fof(f42,plain,(
% 4.21/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4) & r1_tarski(sK4,u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 4.21/1.01    introduced(choice_axiom,[])).
% 4.21/1.01  
% 4.21/1.01  fof(f41,plain,(
% 4.21/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 4.21/1.01    introduced(choice_axiom,[])).
% 4.21/1.01  
% 4.21/1.01  fof(f40,plain,(
% 4.21/1.01    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 4.21/1.01    introduced(choice_axiom,[])).
% 4.21/1.01  
% 4.21/1.01  fof(f39,plain,(
% 4.21/1.01    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 4.21/1.01    introduced(choice_axiom,[])).
% 4.21/1.01  
% 4.21/1.01  fof(f38,plain,(
% 4.21/1.01    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 4.21/1.01    introduced(choice_axiom,[])).
% 4.21/1.01  
% 4.21/1.01  fof(f43,plain,(
% 4.21/1.01    ((((k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & r1_tarski(sK4,u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 4.21/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f36,f42,f41,f40,f39,f38])).
% 4.21/1.01  
% 4.21/1.01  fof(f69,plain,(
% 4.21/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f12,axiom,(
% 4.21/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f29,plain,(
% 4.21/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 4.21/1.01    inference(ennf_transformation,[],[f12])).
% 4.21/1.01  
% 4.21/1.01  fof(f30,plain,(
% 4.21/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 4.21/1.01    inference(flattening,[],[f29])).
% 4.21/1.01  
% 4.21/1.01  fof(f56,plain,(
% 4.21/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 4.21/1.01    inference(cnf_transformation,[],[f30])).
% 4.21/1.01  
% 4.21/1.01  fof(f9,axiom,(
% 4.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f17,plain,(
% 4.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.21/1.01    inference(pure_predicate_removal,[],[f9])).
% 4.21/1.01  
% 4.21/1.01  fof(f25,plain,(
% 4.21/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.21/1.01    inference(ennf_transformation,[],[f17])).
% 4.21/1.01  
% 4.21/1.01  fof(f53,plain,(
% 4.21/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.21/1.01    inference(cnf_transformation,[],[f25])).
% 4.21/1.01  
% 4.21/1.01  fof(f2,axiom,(
% 4.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f19,plain,(
% 4.21/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.21/1.01    inference(ennf_transformation,[],[f2])).
% 4.21/1.01  
% 4.21/1.01  fof(f37,plain,(
% 4.21/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.21/1.01    inference(nnf_transformation,[],[f19])).
% 4.21/1.01  
% 4.21/1.01  fof(f45,plain,(
% 4.21/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f37])).
% 4.21/1.01  
% 4.21/1.01  fof(f8,axiom,(
% 4.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f24,plain,(
% 4.21/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.21/1.01    inference(ennf_transformation,[],[f8])).
% 4.21/1.01  
% 4.21/1.01  fof(f52,plain,(
% 4.21/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.21/1.01    inference(cnf_transformation,[],[f24])).
% 4.21/1.01  
% 4.21/1.01  fof(f6,axiom,(
% 4.21/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f22,plain,(
% 4.21/1.01    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 4.21/1.01    inference(ennf_transformation,[],[f6])).
% 4.21/1.01  
% 4.21/1.01  fof(f50,plain,(
% 4.21/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f22])).
% 4.21/1.01  
% 4.21/1.01  fof(f11,axiom,(
% 4.21/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f27,plain,(
% 4.21/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 4.21/1.01    inference(ennf_transformation,[],[f11])).
% 4.21/1.01  
% 4.21/1.01  fof(f28,plain,(
% 4.21/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 4.21/1.01    inference(flattening,[],[f27])).
% 4.21/1.01  
% 4.21/1.01  fof(f55,plain,(
% 4.21/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f28])).
% 4.21/1.01  
% 4.21/1.01  fof(f10,axiom,(
% 4.21/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f26,plain,(
% 4.21/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.21/1.01    inference(ennf_transformation,[],[f10])).
% 4.21/1.01  
% 4.21/1.01  fof(f54,plain,(
% 4.21/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.21/1.01    inference(cnf_transformation,[],[f26])).
% 4.21/1.01  
% 4.21/1.01  fof(f3,axiom,(
% 4.21/1.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f20,plain,(
% 4.21/1.01    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.21/1.01    inference(ennf_transformation,[],[f3])).
% 4.21/1.01  
% 4.21/1.01  fof(f47,plain,(
% 4.21/1.01    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f20])).
% 4.21/1.01  
% 4.21/1.01  fof(f13,axiom,(
% 4.21/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f31,plain,(
% 4.21/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.21/1.01    inference(ennf_transformation,[],[f13])).
% 4.21/1.01  
% 4.21/1.01  fof(f32,plain,(
% 4.21/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.21/1.01    inference(flattening,[],[f31])).
% 4.21/1.01  
% 4.21/1.01  fof(f57,plain,(
% 4.21/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f32])).
% 4.21/1.01  
% 4.21/1.01  fof(f67,plain,(
% 4.21/1.01    v1_funct_1(sK3)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f68,plain,(
% 4.21/1.01    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f14,axiom,(
% 4.21/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f33,plain,(
% 4.21/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.21/1.01    inference(ennf_transformation,[],[f14])).
% 4.21/1.01  
% 4.21/1.01  fof(f34,plain,(
% 4.21/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.21/1.01    inference(flattening,[],[f33])).
% 4.21/1.01  
% 4.21/1.01  fof(f58,plain,(
% 4.21/1.01    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f34])).
% 4.21/1.01  
% 4.21/1.01  fof(f66,plain,(
% 4.21/1.01    m1_pre_topc(sK2,sK1)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f62,plain,(
% 4.21/1.01    ~v2_struct_0(sK1)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f63,plain,(
% 4.21/1.01    v2_pre_topc(sK1)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f64,plain,(
% 4.21/1.01    l1_pre_topc(sK1)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f61,plain,(
% 4.21/1.01    l1_pre_topc(sK0)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f59,plain,(
% 4.21/1.01    ~v2_struct_0(sK0)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f60,plain,(
% 4.21/1.01    v2_pre_topc(sK0)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f72,plain,(
% 4.21/1.01    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f1,axiom,(
% 4.21/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f18,plain,(
% 4.21/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.21/1.01    inference(ennf_transformation,[],[f1])).
% 4.21/1.01  
% 4.21/1.01  fof(f44,plain,(
% 4.21/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f18])).
% 4.21/1.01  
% 4.21/1.01  fof(f71,plain,(
% 4.21/1.01    r1_tarski(sK4,u1_struct_0(sK2))),
% 4.21/1.01    inference(cnf_transformation,[],[f43])).
% 4.21/1.01  
% 4.21/1.01  fof(f5,axiom,(
% 4.21/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 4.21/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.21/1.01  
% 4.21/1.01  fof(f21,plain,(
% 4.21/1.01    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 4.21/1.01    inference(ennf_transformation,[],[f5])).
% 4.21/1.01  
% 4.21/1.01  fof(f49,plain,(
% 4.21/1.01    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 4.21/1.01    inference(cnf_transformation,[],[f21])).
% 4.21/1.01  
% 4.21/1.01  cnf(c_7,plain,
% 4.21/1.01      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f51]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_581,plain,
% 4.21/1.01      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) | ~ v1_relat_1(X0_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_921,plain,
% 4.21/1.01      ( r1_tarski(k7_relat_1(X0_53,X1_53),X0_53) = iProver_top
% 4.21/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_18,negated_conjecture,
% 4.21/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 4.21/1.01      inference(cnf_transformation,[],[f69]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_573,negated_conjecture,
% 4.21/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_928,plain,
% 4.21/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_12,plain,
% 4.21/1.01      ( ~ r1_tarski(X0,X1)
% 4.21/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 4.21/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
% 4.21/1.01      inference(cnf_transformation,[],[f56]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_577,plain,
% 4.21/1.01      ( ~ r1_tarski(X0_53,X1_53)
% 4.21/1.01      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
% 4.21/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_925,plain,
% 4.21/1.01      ( r1_tarski(X0_53,X1_53) != iProver_top
% 4.21/1.01      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 4.21/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) = iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1650,plain,
% 4.21/1.01      ( r1_tarski(X0_53,sK3) != iProver_top
% 4.21/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_928,c_925]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_9,plain,
% 4.21/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.21/1.01      inference(cnf_transformation,[],[f53]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_2,plain,
% 4.21/1.01      ( r1_tarski(k2_relat_1(X0),X1) | ~ v5_relat_1(X0,X1) | ~ v1_relat_1(X0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f45]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_305,plain,
% 4.21/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 4.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.21/1.01      | ~ v1_relat_1(X0) ),
% 4.21/1.01      inference(resolution,[status(thm)],[c_9,c_2]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_8,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f52]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_315,plain,
% 4.21/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 4.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.21/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_305,c_8]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_572,plain,
% 4.21/1.01      ( r1_tarski(k2_relat_1(X0_53),X1_53)
% 4.21/1.01      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_315]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_929,plain,
% 4.21/1.01      ( r1_tarski(k2_relat_1(X0_53),X1_53) = iProver_top
% 4.21/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53))) != iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1825,plain,
% 4.21/1.01      ( r1_tarski(X0_53,sK3) != iProver_top
% 4.21/1.01      | r1_tarski(k2_relat_1(X0_53),u1_struct_0(sK0)) = iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_1650,c_929]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_6,plain,
% 4.21/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f50]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_582,plain,
% 4.21/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53)
% 4.21/1.01      | ~ v1_relat_1(X0_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_920,plain,
% 4.21/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0_53,X1_53)),X1_53) = iProver_top
% 4.21/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_11,plain,
% 4.21/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 4.21/1.01      | ~ r1_tarski(k2_relat_1(X0),X2)
% 4.21/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.01      | ~ v1_relat_1(X0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f55]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_578,plain,
% 4.21/1.01      ( ~ r1_tarski(k1_relat_1(X0_53),X1_53)
% 4.21/1.01      | ~ r1_tarski(k2_relat_1(X0_53),X2_53)
% 4.21/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 4.21/1.01      | ~ v1_relat_1(X0_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_924,plain,
% 4.21/1.01      ( r1_tarski(k1_relat_1(X0_53),X1_53) != iProver_top
% 4.21/1.01      | r1_tarski(k2_relat_1(X0_53),X2_53) != iProver_top
% 4.21/1.01      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) = iProver_top
% 4.21/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_10,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 4.21/1.01      inference(cnf_transformation,[],[f54]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_579,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 4.21/1.01      | k7_relset_1(X1_53,X2_53,X0_53,X3_53) = k9_relat_1(X0_53,X3_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_923,plain,
% 4.21/1.01      ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
% 4.21/1.01      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1662,plain,
% 4.21/1.01      ( k7_relset_1(X0_53,X1_53,X2_53,X3_53) = k9_relat_1(X2_53,X3_53)
% 4.21/1.01      | r1_tarski(k1_relat_1(X2_53),X0_53) != iProver_top
% 4.21/1.01      | r1_tarski(k2_relat_1(X2_53),X1_53) != iProver_top
% 4.21/1.01      | v1_relat_1(X2_53) != iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_924,c_923]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_3500,plain,
% 4.21/1.01      ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 4.21/1.01      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 4.21/1.01      | v1_relat_1(X2_53) != iProver_top
% 4.21/1.01      | v1_relat_1(k7_relat_1(X2_53,X0_53)) != iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_920,c_1662]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_3,plain,
% 4.21/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 4.21/1.01      inference(cnf_transformation,[],[f47]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_585,plain,
% 4.21/1.01      ( ~ v1_relat_1(X0_53) | v1_relat_1(k7_relat_1(X0_53,X1_53)) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_917,plain,
% 4.21/1.01      ( v1_relat_1(X0_53) != iProver_top
% 4.21/1.01      | v1_relat_1(k7_relat_1(X0_53,X1_53)) = iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_14437,plain,
% 4.21/1.01      ( k7_relset_1(X0_53,X1_53,k7_relat_1(X2_53,X0_53),X3_53) = k9_relat_1(k7_relat_1(X2_53,X0_53),X3_53)
% 4.21/1.01      | r1_tarski(k2_relat_1(k7_relat_1(X2_53,X0_53)),X1_53) != iProver_top
% 4.21/1.01      | v1_relat_1(X2_53) != iProver_top ),
% 4.21/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3500,c_917]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_14442,plain,
% 4.21/1.01      ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(X1_53,X0_53),X2_53) = k9_relat_1(k7_relat_1(X1_53,X0_53),X2_53)
% 4.21/1.01      | r1_tarski(k7_relat_1(X1_53,X0_53),sK3) != iProver_top
% 4.21/1.01      | v1_relat_1(X1_53) != iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_1825,c_14437]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_15459,plain,
% 4.21/1.01      ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53)
% 4.21/1.01      | v1_relat_1(sK3) != iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_921,c_14442]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_39,plain,
% 4.21/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_580,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 4.21/1.01      | v1_relat_1(X0_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1047,plain,
% 4.21/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 4.21/1.01      | v1_relat_1(sK3) ),
% 4.21/1.01      inference(instantiation,[status(thm)],[c_580]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1048,plain,
% 4.21/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 4.21/1.01      | v1_relat_1(sK3) = iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_16523,plain,
% 4.21/1.01      ( k7_relset_1(X0_53,u1_struct_0(sK0),k7_relat_1(sK3,X0_53),X1_53) = k9_relat_1(k7_relat_1(sK3,X0_53),X1_53) ),
% 4.21/1.01      inference(global_propositional_subsumption,
% 4.21/1.01                [status(thm)],
% 4.21/1.01                [c_15459,c_39,c_1048]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1571,plain,
% 4.21/1.01      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k9_relat_1(sK3,X0_53) ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_928,c_923]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_13,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.01      | ~ v1_funct_1(X0)
% 4.21/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 4.21/1.01      inference(cnf_transformation,[],[f57]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_20,negated_conjecture,
% 4.21/1.01      ( v1_funct_1(sK3) ),
% 4.21/1.01      inference(cnf_transformation,[],[f67]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_401,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.21/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 4.21/1.01      | sK3 != X0 ),
% 4.21/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_402,plain,
% 4.21/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.21/1.01      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 4.21/1.01      inference(unflattening,[status(thm)],[c_401]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_571,plain,
% 4.21/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 4.21/1.01      | k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_402]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_930,plain,
% 4.21/1.01      ( k2_partfun1(X0_53,X1_53,sK3,X2_53) = k7_relat_1(sK3,X2_53)
% 4.21/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1116,plain,
% 4.21/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_53) = k7_relat_1(sK3,X0_53) ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_928,c_930]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_19,negated_conjecture,
% 4.21/1.01      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 4.21/1.01      inference(cnf_transformation,[],[f68]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_14,plain,
% 4.21/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.21/1.01      | ~ m1_pre_topc(X3,X1)
% 4.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.21/1.01      | v2_struct_0(X1)
% 4.21/1.01      | v2_struct_0(X2)
% 4.21/1.01      | ~ v2_pre_topc(X2)
% 4.21/1.01      | ~ v2_pre_topc(X1)
% 4.21/1.01      | ~ l1_pre_topc(X2)
% 4.21/1.01      | ~ l1_pre_topc(X1)
% 4.21/1.01      | ~ v1_funct_1(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 4.21/1.01      inference(cnf_transformation,[],[f58]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_21,negated_conjecture,
% 4.21/1.01      ( m1_pre_topc(sK2,sK1) ),
% 4.21/1.01      inference(cnf_transformation,[],[f66]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_325,plain,
% 4.21/1.01      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 4.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 4.21/1.01      | v2_struct_0(X1)
% 4.21/1.01      | v2_struct_0(X2)
% 4.21/1.01      | ~ v2_pre_topc(X1)
% 4.21/1.01      | ~ v2_pre_topc(X2)
% 4.21/1.01      | ~ l1_pre_topc(X1)
% 4.21/1.01      | ~ l1_pre_topc(X2)
% 4.21/1.01      | ~ v1_funct_1(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 4.21/1.01      | sK2 != X3
% 4.21/1.01      | sK1 != X1 ),
% 4.21/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_326,plain,
% 4.21/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 4.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 4.21/1.01      | v2_struct_0(X1)
% 4.21/1.01      | v2_struct_0(sK1)
% 4.21/1.01      | ~ v2_pre_topc(X1)
% 4.21/1.01      | ~ v2_pre_topc(sK1)
% 4.21/1.01      | ~ l1_pre_topc(X1)
% 4.21/1.01      | ~ l1_pre_topc(sK1)
% 4.21/1.01      | ~ v1_funct_1(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 4.21/1.01      inference(unflattening,[status(thm)],[c_325]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_25,negated_conjecture,
% 4.21/1.01      ( ~ v2_struct_0(sK1) ),
% 4.21/1.01      inference(cnf_transformation,[],[f62]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_24,negated_conjecture,
% 4.21/1.01      ( v2_pre_topc(sK1) ),
% 4.21/1.01      inference(cnf_transformation,[],[f63]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_23,negated_conjecture,
% 4.21/1.01      ( l1_pre_topc(sK1) ),
% 4.21/1.01      inference(cnf_transformation,[],[f64]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_330,plain,
% 4.21/1.01      ( ~ l1_pre_topc(X1)
% 4.21/1.01      | v2_struct_0(X1)
% 4.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 4.21/1.01      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 4.21/1.01      | ~ v2_pre_topc(X1)
% 4.21/1.01      | ~ v1_funct_1(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 4.21/1.01      inference(global_propositional_subsumption,
% 4.21/1.01                [status(thm)],
% 4.21/1.01                [c_326,c_25,c_24,c_23]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_331,plain,
% 4.21/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 4.21/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 4.21/1.01      | v2_struct_0(X1)
% 4.21/1.01      | ~ v2_pre_topc(X1)
% 4.21/1.01      | ~ l1_pre_topc(X1)
% 4.21/1.01      | ~ v1_funct_1(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 4.21/1.01      inference(renaming,[status(thm)],[c_330]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_364,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 4.21/1.01      | v2_struct_0(X1)
% 4.21/1.01      | ~ v2_pre_topc(X1)
% 4.21/1.01      | ~ l1_pre_topc(X1)
% 4.21/1.01      | ~ v1_funct_1(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
% 4.21/1.01      | u1_struct_0(X1) != u1_struct_0(sK0)
% 4.21/1.01      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 4.21/1.01      | sK3 != X0 ),
% 4.21/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_331]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_365,plain,
% 4.21/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 4.21/1.01      | v2_struct_0(X0)
% 4.21/1.01      | ~ v2_pre_topc(X0)
% 4.21/1.01      | ~ l1_pre_topc(X0)
% 4.21/1.01      | ~ v1_funct_1(sK3)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 4.21/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 4.21/1.01      inference(unflattening,[status(thm)],[c_364]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_369,plain,
% 4.21/1.01      ( ~ l1_pre_topc(X0)
% 4.21/1.01      | ~ v2_pre_topc(X0)
% 4.21/1.01      | v2_struct_0(X0)
% 4.21/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 4.21/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 4.21/1.01      inference(global_propositional_subsumption,[status(thm)],[c_365,c_20]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_370,plain,
% 4.21/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 4.21/1.01      | v2_struct_0(X0)
% 4.21/1.01      | ~ v2_pre_topc(X0)
% 4.21/1.01      | ~ l1_pre_topc(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 4.21/1.01      | u1_struct_0(X0) != u1_struct_0(sK0) ),
% 4.21/1.01      inference(renaming,[status(thm)],[c_369]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_26,negated_conjecture,
% 4.21/1.01      ( l1_pre_topc(sK0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f61]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_433,plain,
% 4.21/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
% 4.21/1.01      | v2_struct_0(X0)
% 4.21/1.01      | ~ v2_pre_topc(X0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,X0,sK3,sK2)
% 4.21/1.01      | u1_struct_0(X0) != u1_struct_0(sK0)
% 4.21/1.01      | sK0 != X0 ),
% 4.21/1.01      inference(resolution_lifted,[status(thm)],[c_370,c_26]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_434,plain,
% 4.21/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 4.21/1.01      | v2_struct_0(sK0)
% 4.21/1.01      | ~ v2_pre_topc(sK0)
% 4.21/1.01      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
% 4.21/1.01      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 4.21/1.01      inference(unflattening,[status(thm)],[c_433]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_28,negated_conjecture,
% 4.21/1.01      ( ~ v2_struct_0(sK0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f59]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_27,negated_conjecture,
% 4.21/1.01      ( v2_pre_topc(sK0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f60]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_436,plain,
% 4.21/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2)
% 4.21/1.01      | u1_struct_0(sK0) != u1_struct_0(sK0) ),
% 4.21/1.01      inference(global_propositional_subsumption,
% 4.21/1.01                [status(thm)],
% 4.21/1.01                [c_434,c_28,c_27,c_18]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_466,plain,
% 4.21/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 4.21/1.01      inference(equality_resolution_simp,[status(thm)],[c_436]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_569,plain,
% 4.21/1.01      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_466]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1144,plain,
% 4.21/1.01      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 4.21/1.01      inference(demodulation,[status(thm)],[c_1116,c_569]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_15,negated_conjecture,
% 4.21/1.01      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
% 4.21/1.01      inference(cnf_transformation,[],[f72]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_576,negated_conjecture,
% 4.21/1.01      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1423,plain,
% 4.21/1.01      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) ),
% 4.21/1.01      inference(demodulation,[status(thm)],[c_1144,c_576]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1753,plain,
% 4.21/1.01      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 4.21/1.01      inference(demodulation,[status(thm)],[c_1571,c_1423]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_16527,plain,
% 4.21/1.01      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 4.21/1.01      inference(demodulation,[status(thm)],[c_16523,c_1753]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_0,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f44]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_586,plain,
% 4.21/1.01      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 4.21/1.01      | ~ v1_relat_1(X1_53)
% 4.21/1.01      | v1_relat_1(X0_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_916,plain,
% 4.21/1.01      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 4.21/1.01      | v1_relat_1(X1_53) != iProver_top
% 4.21/1.01      | v1_relat_1(X0_53) = iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1219,plain,
% 4.21/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 4.21/1.01      | v1_relat_1(sK3) = iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_928,c_916]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1417,plain,
% 4.21/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 4.21/1.01      inference(global_propositional_subsumption,
% 4.21/1.01                [status(thm)],
% 4.21/1.01                [c_1219,c_39,c_1048]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_16,negated_conjecture,
% 4.21/1.01      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 4.21/1.01      inference(cnf_transformation,[],[f71]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_575,negated_conjecture,
% 4.21/1.01      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_926,plain,
% 4.21/1.01      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_5,plain,
% 4.21/1.01      ( ~ r1_tarski(X0,X1)
% 4.21/1.01      | ~ v1_relat_1(X2)
% 4.21/1.01      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 4.21/1.01      inference(cnf_transformation,[],[f49]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_583,plain,
% 4.21/1.01      ( ~ r1_tarski(X0_53,X1_53)
% 4.21/1.01      | ~ v1_relat_1(X2_53)
% 4.21/1.01      | k9_relat_1(k7_relat_1(X2_53,X1_53),X0_53) = k9_relat_1(X2_53,X0_53) ),
% 4.21/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_919,plain,
% 4.21/1.01      ( k9_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k9_relat_1(X0_53,X2_53)
% 4.21/1.01      | r1_tarski(X2_53,X1_53) != iProver_top
% 4.21/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 4.21/1.01      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1577,plain,
% 4.21/1.01      ( k9_relat_1(k7_relat_1(X0_53,u1_struct_0(sK2)),sK4) = k9_relat_1(X0_53,sK4)
% 4.21/1.01      | v1_relat_1(X0_53) != iProver_top ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_926,c_919]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_1808,plain,
% 4.21/1.01      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
% 4.21/1.01      inference(superposition,[status(thm)],[c_1417,c_1577]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_16528,plain,
% 4.21/1.01      ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
% 4.21/1.01      inference(light_normalisation,[status(thm)],[c_16527,c_1808]) ).
% 4.21/1.01  
% 4.21/1.01  cnf(c_16529,plain,
% 4.21/1.01      ( $false ),
% 4.21/1.01      inference(equality_resolution_simp,[status(thm)],[c_16528]) ).
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.21/1.01  
% 4.21/1.01  ------                               Statistics
% 4.21/1.01  
% 4.21/1.01  ------ General
% 4.21/1.01  
% 4.21/1.01  abstr_ref_over_cycles:                  0
% 4.21/1.01  abstr_ref_under_cycles:                 0
% 4.21/1.01  gc_basic_clause_elim:                   0
% 4.21/1.01  forced_gc_time:                         0
% 4.21/1.01  parsing_time:                           0.009
% 4.21/1.01  unif_index_cands_time:                  0.
% 4.21/1.01  unif_index_add_time:                    0.
% 4.21/1.01  orderings_time:                         0.
% 4.21/1.01  out_proof_time:                         0.009
% 4.21/1.01  total_time:                             0.493
% 4.21/1.01  num_of_symbols:                         60
% 4.21/1.01  num_of_terms:                           13207
% 4.21/1.01  
% 4.21/1.01  ------ Preprocessing
% 4.21/1.01  
% 4.21/1.01  num_of_splits:                          0
% 4.21/1.01  num_of_split_atoms:                     0
% 4.21/1.01  num_of_reused_defs:                     0
% 4.21/1.01  num_eq_ax_congr_red:                    17
% 4.21/1.01  num_of_sem_filtered_clauses:            1
% 4.21/1.01  num_of_subtypes:                        4
% 4.21/1.01  monotx_restored_types:                  0
% 4.21/1.01  sat_num_of_epr_types:                   0
% 4.21/1.01  sat_num_of_non_cyclic_types:            0
% 4.21/1.01  sat_guarded_non_collapsed_types:        0
% 4.21/1.01  num_pure_diseq_elim:                    0
% 4.21/1.01  simp_replaced_by:                       0
% 4.21/1.01  res_preprocessed:                       116
% 4.21/1.01  prep_upred:                             0
% 4.21/1.01  prep_unflattend:                        6
% 4.21/1.01  smt_new_axioms:                         0
% 4.21/1.01  pred_elim_cands:                        3
% 4.21/1.01  pred_elim:                              7
% 4.21/1.01  pred_elim_cl:                           11
% 4.21/1.01  pred_elim_cycles:                       9
% 4.21/1.01  merged_defs:                            0
% 4.21/1.01  merged_defs_ncl:                        0
% 4.21/1.01  bin_hyper_res:                          0
% 4.21/1.01  prep_cycles:                            4
% 4.21/1.01  pred_elim_time:                         0.004
% 4.21/1.01  splitting_time:                         0.
% 4.21/1.01  sem_filter_time:                        0.
% 4.21/1.01  monotx_time:                            0.
% 4.21/1.01  subtype_inf_time:                       0.
% 4.21/1.01  
% 4.21/1.01  ------ Problem properties
% 4.21/1.01  
% 4.21/1.01  clauses:                                18
% 4.21/1.01  conjectures:                            4
% 4.21/1.01  epr:                                    0
% 4.21/1.01  horn:                                   18
% 4.21/1.01  ground:                                 6
% 4.21/1.01  unary:                                  6
% 4.21/1.01  binary:                                 7
% 4.21/1.01  lits:                                   36
% 4.21/1.01  lits_eq:                                7
% 4.21/1.01  fd_pure:                                0
% 4.21/1.01  fd_pseudo:                              0
% 4.21/1.01  fd_cond:                                0
% 4.21/1.01  fd_pseudo_cond:                         0
% 4.21/1.01  ac_symbols:                             0
% 4.21/1.01  
% 4.21/1.01  ------ Propositional Solver
% 4.21/1.01  
% 4.21/1.01  prop_solver_calls:                      33
% 4.21/1.01  prop_fast_solver_calls:                 965
% 4.21/1.01  smt_solver_calls:                       0
% 4.21/1.01  smt_fast_solver_calls:                  0
% 4.21/1.01  prop_num_of_clauses:                    4601
% 4.21/1.01  prop_preprocess_simplified:             10065
% 4.21/1.01  prop_fo_subsumed:                       16
% 4.21/1.01  prop_solver_time:                       0.
% 4.21/1.01  smt_solver_time:                        0.
% 4.21/1.01  smt_fast_solver_time:                   0.
% 4.21/1.01  prop_fast_solver_time:                  0.
% 4.21/1.01  prop_unsat_core_time:                   0.
% 4.21/1.01  
% 4.21/1.01  ------ QBF
% 4.21/1.01  
% 4.21/1.01  qbf_q_res:                              0
% 4.21/1.01  qbf_num_tautologies:                    0
% 4.21/1.01  qbf_prep_cycles:                        0
% 4.21/1.01  
% 4.21/1.01  ------ BMC1
% 4.21/1.01  
% 4.21/1.01  bmc1_current_bound:                     -1
% 4.21/1.01  bmc1_last_solved_bound:                 -1
% 4.21/1.01  bmc1_unsat_core_size:                   -1
% 4.21/1.01  bmc1_unsat_core_parents_size:           -1
% 4.21/1.01  bmc1_merge_next_fun:                    0
% 4.21/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.21/1.01  
% 4.21/1.01  ------ Instantiation
% 4.21/1.01  
% 4.21/1.01  inst_num_of_clauses:                    1670
% 4.21/1.01  inst_num_in_passive:                    289
% 4.21/1.01  inst_num_in_active:                     907
% 4.21/1.01  inst_num_in_unprocessed:                474
% 4.21/1.01  inst_num_of_loops:                      960
% 4.21/1.01  inst_num_of_learning_restarts:          0
% 4.21/1.01  inst_num_moves_active_passive:          47
% 4.21/1.01  inst_lit_activity:                      0
% 4.21/1.01  inst_lit_activity_moves:                0
% 4.21/1.01  inst_num_tautologies:                   0
% 4.21/1.01  inst_num_prop_implied:                  0
% 4.21/1.01  inst_num_existing_simplified:           0
% 4.21/1.01  inst_num_eq_res_simplified:             0
% 4.21/1.01  inst_num_child_elim:                    0
% 4.21/1.01  inst_num_of_dismatching_blockings:      2180
% 4.21/1.01  inst_num_of_non_proper_insts:           3224
% 4.21/1.01  inst_num_of_duplicates:                 0
% 4.21/1.01  inst_inst_num_from_inst_to_res:         0
% 4.21/1.01  inst_dismatching_checking_time:         0.
% 4.21/1.01  
% 4.21/1.01  ------ Resolution
% 4.21/1.01  
% 4.21/1.01  res_num_of_clauses:                     0
% 4.21/1.01  res_num_in_passive:                     0
% 4.21/1.01  res_num_in_active:                      0
% 4.21/1.01  res_num_of_loops:                       120
% 4.21/1.01  res_forward_subset_subsumed:            497
% 4.21/1.01  res_backward_subset_subsumed:           0
% 4.21/1.01  res_forward_subsumed:                   0
% 4.21/1.01  res_backward_subsumed:                  0
% 4.21/1.01  res_forward_subsumption_resolution:     1
% 4.21/1.01  res_backward_subsumption_resolution:    0
% 4.21/1.01  res_clause_to_clause_subsumption:       1619
% 4.21/1.01  res_orphan_elimination:                 0
% 4.21/1.01  res_tautology_del:                      377
% 4.21/1.01  res_num_eq_res_simplified:              1
% 4.21/1.01  res_num_sel_changes:                    0
% 4.21/1.01  res_moves_from_active_to_pass:          0
% 4.21/1.01  
% 4.21/1.01  ------ Superposition
% 4.21/1.01  
% 4.21/1.01  sup_time_total:                         0.
% 4.21/1.01  sup_time_generating:                    0.
% 4.21/1.01  sup_time_sim_full:                      0.
% 4.21/1.01  sup_time_sim_immed:                     0.
% 4.21/1.01  
% 4.21/1.01  sup_num_of_clauses:                     404
% 4.21/1.01  sup_num_in_active:                      186
% 4.21/1.01  sup_num_in_passive:                     218
% 4.21/1.01  sup_num_of_loops:                       190
% 4.21/1.01  sup_fw_superposition:                   249
% 4.21/1.01  sup_bw_superposition:                   179
% 4.21/1.01  sup_immediate_simplified:               28
% 4.21/1.01  sup_given_eliminated:                   0
% 4.21/1.01  comparisons_done:                       0
% 4.21/1.01  comparisons_avoided:                    0
% 4.21/1.01  
% 4.21/1.01  ------ Simplifications
% 4.21/1.01  
% 4.21/1.01  
% 4.21/1.01  sim_fw_subset_subsumed:                 9
% 4.21/1.01  sim_bw_subset_subsumed:                 6
% 4.21/1.01  sim_fw_subsumed:                        2
% 4.21/1.01  sim_bw_subsumed:                        12
% 4.21/1.01  sim_fw_subsumption_res:                 2
% 4.21/1.01  sim_bw_subsumption_res:                 0
% 4.21/1.01  sim_tautology_del:                      3
% 4.21/1.01  sim_eq_tautology_del:                   0
% 4.21/1.01  sim_eq_res_simp:                        0
% 4.21/1.01  sim_fw_demodulated:                     0
% 4.21/1.01  sim_bw_demodulated:                     4
% 4.21/1.01  sim_light_normalised:                   1
% 4.21/1.01  sim_joinable_taut:                      0
% 4.21/1.01  sim_joinable_simp:                      0
% 4.21/1.01  sim_ac_normalised:                      0
% 4.21/1.01  sim_smt_subsumption:                    0
% 4.21/1.01  
%------------------------------------------------------------------------------
