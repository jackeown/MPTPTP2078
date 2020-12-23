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
% DateTime   : Thu Dec  3 12:22:31 EST 2020

% Result     : Theorem 11.63s
% Output     : CNFRefutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :  205 (1053 expanded)
%              Number of clauses        :  129 ( 333 expanded)
%              Number of leaves         :   21 ( 347 expanded)
%              Depth                    :   23
%              Number of atoms          :  735 (9125 expanded)
%              Number of equality atoms :  254 (1193 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & r1_tarski(X4,u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4)
        & r1_tarski(sK4,u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f48,f47,f46,f45,f44])).

fof(f76,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          | ~ r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          | ~ r1_tarski(X1,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          | ~ v1_funct_2(X4,X0,X3)
          | ~ v1_funct_1(X4) )
      | v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          | ~ r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          | ~ r1_tarski(X1,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          | ~ v1_funct_2(X4,X0,X3)
          | ~ v1_funct_1(X4) )
      | v1_xboole_0(X3) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_2(X4,X0,X3)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_903,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1458,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_911,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(X1_56,X2_56)
    | ~ m1_pre_topc(X0_56,X2_56)
    | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ v2_pre_topc(X2_56)
    | ~ l1_pre_topc(X2_56) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1451,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(X1_56,X2_56) != iProver_top
    | m1_pre_topc(X0_56,X2_56) != iProver_top
    | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56)) = iProver_top
    | v2_pre_topc(X2_56) != iProver_top
    | l1_pre_topc(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_2212,plain,
    ( m1_pre_topc(X0_56,sK2) != iProver_top
    | m1_pre_topc(X0_56,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0_56),u1_struct_0(sK2)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1458,c_1451])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2386,plain,
    ( m1_pre_topc(X0_56,sK2) != iProver_top
    | m1_pre_topc(X0_56,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0_56),u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2212,c_37,c_38])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_908,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1453,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_912,plain,
    ( m1_pre_topc(X0_56,X0_56)
    | ~ l1_pre_topc(X0_56) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1450,plain,
    ( m1_pre_topc(X0_56,X0_56) = iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_2213,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56)) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1451])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_923,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ r1_tarski(X2_54,X0_54)
    | r1_tarski(X2_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1439,plain,
    ( r1_tarski(X0_54,X1_54) != iProver_top
    | r1_tarski(X2_54,X0_54) != iProver_top
    | r1_tarski(X2_54,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_4812,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X0_56)) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(X1_56)) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_2213,c_1439])).

cnf(c_6415,plain,
    ( m1_pre_topc(sK2,X0_56) != iProver_top
    | r1_tarski(sK4,u1_struct_0(X0_56)) = iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_4812])).

cnf(c_6481,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(sK2,X0_56) != iProver_top
    | r1_tarski(sK4,u1_struct_0(X1_56)) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_6415,c_4812])).

cnf(c_8147,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1458,c_6481])).

cnf(c_40,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_45,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_50,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_52,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_3836,plain,
    ( ~ r1_tarski(X0_54,u1_struct_0(X0_56))
    | r1_tarski(X0_54,u1_struct_0(X1_56))
    | ~ r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56)) ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_6287,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56))
    | r1_tarski(sK4,u1_struct_0(X0_56))
    | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3836])).

cnf(c_6288,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
    | r1_tarski(sK4,u1_struct_0(X0_56)) = iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6287])).

cnf(c_6290,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6288])).

cnf(c_6321,plain,
    ( ~ m1_pre_topc(X0_56,X1_56)
    | ~ m1_pre_topc(sK2,X1_56)
    | ~ m1_pre_topc(sK2,X0_56)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56))
    | ~ v2_pre_topc(X1_56)
    | ~ l1_pre_topc(X1_56) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_6322,plain,
    ( m1_pre_topc(X0_56,X1_56) != iProver_top
    | m1_pre_topc(sK2,X1_56) != iProver_top
    | m1_pre_topc(sK2,X0_56) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56)) = iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6321])).

cnf(c_6324,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6322])).

cnf(c_8255,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8147,c_37,c_38,c_40,c_45,c_52,c_6290,c_6324])).

cnf(c_8260,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X0_54,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8255,c_1439])).

cnf(c_8275,plain,
    ( r1_tarski(X0_54,X1_54) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK1)) = iProver_top
    | r1_tarski(X1_54,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8260,c_1439])).

cnf(c_8567,plain,
    ( m1_pre_topc(X0_56,sK2) != iProver_top
    | m1_pre_topc(X0_56,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0_56),u1_struct_0(sK1)) = iProver_top
    | r1_tarski(u1_struct_0(sK2),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_8275])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_906,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1455,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1443,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_1986,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_1443])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_922,plain,
    ( ~ v1_relat_1(X0_54)
    | k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1440,plain,
    ( k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_2048,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_54)) = k9_relat_1(sK3,X0_54) ),
    inference(superposition,[status(thm)],[c_1986,c_1440])).

cnf(c_5,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_920,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_54,X1_54)),k2_relat_1(X0_54))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1442,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_54,X1_54)),k2_relat_1(X0_54)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_2402,plain,
    ( r1_tarski(k9_relat_1(sK3,X0_54),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1442])).

cnf(c_3102,plain,
    ( r1_tarski(k9_relat_1(sK3,X0_54),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2402,c_1986])).

cnf(c_2,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_374,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_6])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_894,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | r1_tarski(k2_relat_1(X0_54),X2_54) ),
    inference(subtyping,[status(esa)],[c_375])).

cnf(c_1467,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | r1_tarski(k2_relat_1(X0_54),X2_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_3573,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_1467])).

cnf(c_3640,plain,
    ( r1_tarski(X0_54,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0_54,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3573,c_1439])).

cnf(c_3653,plain,
    ( r1_tarski(k9_relat_1(sK3,X0_54),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_3640])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1445,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_2207,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54) = k7_relat_1(sK3,X0_54)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_1445])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2334,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54) = k7_relat_1(sK3,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2207,c_41])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(k7_relset_1(X1,X2,X0,X3),X4)
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_916,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X3_54,X4_54)))
    | ~ r1_tarski(X3_54,X1_54)
    | ~ r1_tarski(k7_relset_1(X1_54,X2_54,X0_54,X3_54),X4_54)
    | v1_xboole_0(X2_54)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1446,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X3_54,X4_54))) = iProver_top
    | r1_tarski(X3_54,X1_54) != iProver_top
    | r1_tarski(k7_relset_1(X1_54,X2_54,X0_54,X3_54),X4_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_916])).

cnf(c_2537,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54),X1_54) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_1446])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k7_relset_1(X1_54,X2_54,X0_54,X3_54) = k9_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1444,plain,
    ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_2161,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54) = k9_relat_1(sK3,X0_54) ),
    inference(superposition,[status(thm)],[c_1455,c_1444])).

cnf(c_2541,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0_54),X1_54) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2537,c_2161])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_350,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_13,c_14])).

cnf(c_895,plain,
    ( v2_struct_0(X0_56)
    | ~ l1_pre_topc(X0_56)
    | ~ v1_xboole_0(u1_struct_0(X0_56)) ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_1511,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_1512,plain,
    ( v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1511])).

cnf(c_2922,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
    | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0_54),X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2541,c_33,c_35,c_41,c_42,c_43,c_1512])).

cnf(c_2931,plain,
    ( k7_relset_1(X0_54,X1_54,k7_relat_1(sK3,X0_54),X2_54) = k9_relat_1(k7_relat_1(sK3,X0_54),X2_54)
    | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(k9_relat_1(sK3,X0_54),X1_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_2922,c_1444])).

cnf(c_3997,plain,
    ( k7_relset_1(X0_54,u1_struct_0(sK0),k7_relat_1(sK3,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK3,X0_54),X1_54)
    | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3653,c_2931])).

cnf(c_18630,plain,
    ( k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54)
    | m1_pre_topc(X0_56,sK2) != iProver_top
    | m1_pre_topc(X0_56,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8567,c_3997])).

cnf(c_18627,plain,
    ( k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54)
    | m1_pre_topc(X0_56,sK1) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2213,c_3997])).

cnf(c_46352,plain,
    ( m1_pre_topc(X0_56,sK1) != iProver_top
    | k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18630,c_37,c_38,c_18627])).

cnf(c_46353,plain,
    ( k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54)
    | m1_pre_topc(X0_56,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_46352])).

cnf(c_46358,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X0_54) ),
    inference(superposition,[status(thm)],[c_1458,c_46353])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_913,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
    | ~ m1_pre_topc(X2_56,X0_56)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
    | ~ v2_pre_topc(X1_56)
    | ~ v2_pre_topc(X0_56)
    | v2_struct_0(X0_56)
    | v2_struct_0(X1_56)
    | ~ l1_pre_topc(X0_56)
    | ~ l1_pre_topc(X1_56)
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_54,X2_56) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1449,plain,
    ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_54,X2_56)
    | v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
    | m1_pre_topc(X2_56,X0_56) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
    | v2_pre_topc(X1_56) != iProver_top
    | v2_pre_topc(X0_56) != iProver_top
    | v2_struct_0(X0_56) = iProver_top
    | v2_struct_0(X1_56) = iProver_top
    | l1_pre_topc(X1_56) != iProver_top
    | l1_pre_topc(X0_56) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_2691,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0_56)) = k2_tmap_1(sK1,sK0,sK3,X0_56)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0_56,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_1449])).

cnf(c_2693,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0_56) = k7_relat_1(sK3,u1_struct_0(X0_56))
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
    | m1_pre_topc(X0_56,sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2691,c_2334])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2945,plain,
    ( m1_pre_topc(X0_56,sK1) != iProver_top
    | k2_tmap_1(sK1,sK0,sK3,X0_56) = k7_relat_1(sK3,u1_struct_0(X0_56)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2693,c_33,c_34,c_35,c_36,c_37,c_38,c_41,c_42])).

cnf(c_2946,plain,
    ( k2_tmap_1(sK1,sK0,sK3,X0_56) = k7_relat_1(sK3,u1_struct_0(X0_56))
    | m1_pre_topc(X0_56,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2945])).

cnf(c_2951,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_1458,c_2946])).

cnf(c_19,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_909,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2268,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2161,c_909])).

cnf(c_3028,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_2951,c_2268])).

cnf(c_46364,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_46358,c_3028])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_921,plain,
    ( ~ r1_tarski(X0_54,X1_54)
    | ~ v1_relat_1(X2_54)
    | k9_relat_1(k7_relat_1(X2_54,X1_54),X0_54) = k9_relat_1(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1441,plain,
    ( k9_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k9_relat_1(X0_54,X2_54)
    | r1_tarski(X2_54,X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_921])).

cnf(c_2051,plain,
    ( k9_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2)),sK4) = k9_relat_1(X0_54,sK4)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_1453,c_1441])).

cnf(c_2332,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1986,c_2051])).

cnf(c_46365,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_46364,c_2332])).

cnf(c_46366,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_46365])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:52:27 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 11.63/1.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.63/1.97  
% 11.63/1.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.63/1.97  
% 11.63/1.97  ------  iProver source info
% 11.63/1.97  
% 11.63/1.97  git: date: 2020-06-30 10:37:57 +0100
% 11.63/1.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.63/1.97  git: non_committed_changes: false
% 11.63/1.97  git: last_make_outside_of_git: false
% 11.63/1.97  
% 11.63/1.97  ------ 
% 11.63/1.97  
% 11.63/1.97  ------ Input Options
% 11.63/1.97  
% 11.63/1.97  --out_options                           all
% 11.63/1.97  --tptp_safe_out                         true
% 11.63/1.97  --problem_path                          ""
% 11.63/1.97  --include_path                          ""
% 11.63/1.97  --clausifier                            res/vclausify_rel
% 11.63/1.97  --clausifier_options                    ""
% 11.63/1.97  --stdin                                 false
% 11.63/1.97  --stats_out                             all
% 11.63/1.97  
% 11.63/1.97  ------ General Options
% 11.63/1.97  
% 11.63/1.97  --fof                                   false
% 11.63/1.97  --time_out_real                         305.
% 11.63/1.97  --time_out_virtual                      -1.
% 11.63/1.97  --symbol_type_check                     false
% 11.63/1.97  --clausify_out                          false
% 11.63/1.97  --sig_cnt_out                           false
% 11.63/1.97  --trig_cnt_out                          false
% 11.63/1.97  --trig_cnt_out_tolerance                1.
% 11.63/1.97  --trig_cnt_out_sk_spl                   false
% 11.63/1.97  --abstr_cl_out                          false
% 11.63/1.97  
% 11.63/1.97  ------ Global Options
% 11.63/1.97  
% 11.63/1.97  --schedule                              default
% 11.63/1.97  --add_important_lit                     false
% 11.63/1.97  --prop_solver_per_cl                    1000
% 11.63/1.97  --min_unsat_core                        false
% 11.63/1.97  --soft_assumptions                      false
% 11.63/1.97  --soft_lemma_size                       3
% 11.63/1.97  --prop_impl_unit_size                   0
% 11.63/1.97  --prop_impl_unit                        []
% 11.63/1.97  --share_sel_clauses                     true
% 11.63/1.97  --reset_solvers                         false
% 11.63/1.97  --bc_imp_inh                            [conj_cone]
% 11.63/1.97  --conj_cone_tolerance                   3.
% 11.63/1.97  --extra_neg_conj                        none
% 11.63/1.97  --large_theory_mode                     true
% 11.63/1.97  --prolific_symb_bound                   200
% 11.63/1.97  --lt_threshold                          2000
% 11.63/1.97  --clause_weak_htbl                      true
% 11.63/1.97  --gc_record_bc_elim                     false
% 11.63/1.97  
% 11.63/1.97  ------ Preprocessing Options
% 11.63/1.97  
% 11.63/1.97  --preprocessing_flag                    true
% 11.63/1.97  --time_out_prep_mult                    0.1
% 11.63/1.97  --splitting_mode                        input
% 11.63/1.97  --splitting_grd                         true
% 11.63/1.97  --splitting_cvd                         false
% 11.63/1.97  --splitting_cvd_svl                     false
% 11.63/1.97  --splitting_nvd                         32
% 11.63/1.97  --sub_typing                            true
% 11.63/1.97  --prep_gs_sim                           true
% 11.63/1.97  --prep_unflatten                        true
% 11.63/1.97  --prep_res_sim                          true
% 11.63/1.97  --prep_upred                            true
% 11.63/1.97  --prep_sem_filter                       exhaustive
% 11.63/1.97  --prep_sem_filter_out                   false
% 11.63/1.97  --pred_elim                             true
% 11.63/1.97  --res_sim_input                         true
% 11.63/1.97  --eq_ax_congr_red                       true
% 11.63/1.97  --pure_diseq_elim                       true
% 11.63/1.97  --brand_transform                       false
% 11.63/1.97  --non_eq_to_eq                          false
% 11.63/1.97  --prep_def_merge                        true
% 11.63/1.97  --prep_def_merge_prop_impl              false
% 11.63/1.97  --prep_def_merge_mbd                    true
% 11.63/1.97  --prep_def_merge_tr_red                 false
% 11.63/1.97  --prep_def_merge_tr_cl                  false
% 11.63/1.97  --smt_preprocessing                     true
% 11.63/1.97  --smt_ac_axioms                         fast
% 11.63/1.97  --preprocessed_out                      false
% 11.63/1.97  --preprocessed_stats                    false
% 11.63/1.97  
% 11.63/1.97  ------ Abstraction refinement Options
% 11.63/1.97  
% 11.63/1.97  --abstr_ref                             []
% 11.63/1.97  --abstr_ref_prep                        false
% 11.63/1.97  --abstr_ref_until_sat                   false
% 11.63/1.97  --abstr_ref_sig_restrict                funpre
% 11.63/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/1.97  --abstr_ref_under                       []
% 11.63/1.97  
% 11.63/1.97  ------ SAT Options
% 11.63/1.97  
% 11.63/1.97  --sat_mode                              false
% 11.63/1.97  --sat_fm_restart_options                ""
% 11.63/1.97  --sat_gr_def                            false
% 11.63/1.97  --sat_epr_types                         true
% 11.63/1.97  --sat_non_cyclic_types                  false
% 11.63/1.97  --sat_finite_models                     false
% 11.63/1.97  --sat_fm_lemmas                         false
% 11.63/1.97  --sat_fm_prep                           false
% 11.63/1.97  --sat_fm_uc_incr                        true
% 11.63/1.97  --sat_out_model                         small
% 11.63/1.97  --sat_out_clauses                       false
% 11.63/1.97  
% 11.63/1.97  ------ QBF Options
% 11.63/1.97  
% 11.63/1.97  --qbf_mode                              false
% 11.63/1.97  --qbf_elim_univ                         false
% 11.63/1.97  --qbf_dom_inst                          none
% 11.63/1.97  --qbf_dom_pre_inst                      false
% 11.63/1.97  --qbf_sk_in                             false
% 11.63/1.97  --qbf_pred_elim                         true
% 11.63/1.97  --qbf_split                             512
% 11.63/1.97  
% 11.63/1.97  ------ BMC1 Options
% 11.63/1.97  
% 11.63/1.97  --bmc1_incremental                      false
% 11.63/1.97  --bmc1_axioms                           reachable_all
% 11.63/1.97  --bmc1_min_bound                        0
% 11.63/1.97  --bmc1_max_bound                        -1
% 11.63/1.97  --bmc1_max_bound_default                -1
% 11.63/1.97  --bmc1_symbol_reachability              true
% 11.63/1.97  --bmc1_property_lemmas                  false
% 11.63/1.97  --bmc1_k_induction                      false
% 11.63/1.97  --bmc1_non_equiv_states                 false
% 11.63/1.97  --bmc1_deadlock                         false
% 11.63/1.97  --bmc1_ucm                              false
% 11.63/1.97  --bmc1_add_unsat_core                   none
% 11.63/1.97  --bmc1_unsat_core_children              false
% 11.63/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/1.97  --bmc1_out_stat                         full
% 11.63/1.97  --bmc1_ground_init                      false
% 11.63/1.97  --bmc1_pre_inst_next_state              false
% 11.63/1.97  --bmc1_pre_inst_state                   false
% 11.63/1.97  --bmc1_pre_inst_reach_state             false
% 11.63/1.97  --bmc1_out_unsat_core                   false
% 11.63/1.97  --bmc1_aig_witness_out                  false
% 11.63/1.97  --bmc1_verbose                          false
% 11.63/1.97  --bmc1_dump_clauses_tptp                false
% 11.63/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.63/1.97  --bmc1_dump_file                        -
% 11.63/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.63/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.63/1.97  --bmc1_ucm_extend_mode                  1
% 11.63/1.97  --bmc1_ucm_init_mode                    2
% 11.63/1.97  --bmc1_ucm_cone_mode                    none
% 11.63/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.63/1.97  --bmc1_ucm_relax_model                  4
% 11.63/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.63/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/1.97  --bmc1_ucm_layered_model                none
% 11.63/1.97  --bmc1_ucm_max_lemma_size               10
% 11.63/1.97  
% 11.63/1.97  ------ AIG Options
% 11.63/1.97  
% 11.63/1.97  --aig_mode                              false
% 11.63/1.97  
% 11.63/1.97  ------ Instantiation Options
% 11.63/1.97  
% 11.63/1.97  --instantiation_flag                    true
% 11.63/1.97  --inst_sos_flag                         true
% 11.63/1.97  --inst_sos_phase                        true
% 11.63/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/1.97  --inst_lit_sel_side                     num_symb
% 11.63/1.97  --inst_solver_per_active                1400
% 11.63/1.97  --inst_solver_calls_frac                1.
% 11.63/1.97  --inst_passive_queue_type               priority_queues
% 11.63/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/1.97  --inst_passive_queues_freq              [25;2]
% 11.63/1.97  --inst_dismatching                      true
% 11.63/1.97  --inst_eager_unprocessed_to_passive     true
% 11.63/1.97  --inst_prop_sim_given                   true
% 11.63/1.97  --inst_prop_sim_new                     false
% 11.63/1.97  --inst_subs_new                         false
% 11.63/1.97  --inst_eq_res_simp                      false
% 11.63/1.97  --inst_subs_given                       false
% 11.63/1.97  --inst_orphan_elimination               true
% 11.63/1.97  --inst_learning_loop_flag               true
% 11.63/1.97  --inst_learning_start                   3000
% 11.63/1.97  --inst_learning_factor                  2
% 11.63/1.97  --inst_start_prop_sim_after_learn       3
% 11.63/1.97  --inst_sel_renew                        solver
% 11.63/1.97  --inst_lit_activity_flag                true
% 11.63/1.97  --inst_restr_to_given                   false
% 11.63/1.97  --inst_activity_threshold               500
% 11.63/1.97  --inst_out_proof                        true
% 11.63/1.97  
% 11.63/1.97  ------ Resolution Options
% 11.63/1.97  
% 11.63/1.97  --resolution_flag                       true
% 11.63/1.97  --res_lit_sel                           adaptive
% 11.63/1.97  --res_lit_sel_side                      none
% 11.63/1.97  --res_ordering                          kbo
% 11.63/1.97  --res_to_prop_solver                    active
% 11.63/1.97  --res_prop_simpl_new                    false
% 11.63/1.97  --res_prop_simpl_given                  true
% 11.63/1.97  --res_passive_queue_type                priority_queues
% 11.63/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/1.97  --res_passive_queues_freq               [15;5]
% 11.63/1.97  --res_forward_subs                      full
% 11.63/1.97  --res_backward_subs                     full
% 11.63/1.97  --res_forward_subs_resolution           true
% 11.63/1.97  --res_backward_subs_resolution          true
% 11.63/1.97  --res_orphan_elimination                true
% 11.63/1.97  --res_time_limit                        2.
% 11.63/1.97  --res_out_proof                         true
% 11.63/1.97  
% 11.63/1.97  ------ Superposition Options
% 11.63/1.97  
% 11.63/1.97  --superposition_flag                    true
% 11.63/1.97  --sup_passive_queue_type                priority_queues
% 11.63/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.63/1.97  --demod_completeness_check              fast
% 11.63/1.97  --demod_use_ground                      true
% 11.63/1.97  --sup_to_prop_solver                    passive
% 11.63/1.97  --sup_prop_simpl_new                    true
% 11.63/1.97  --sup_prop_simpl_given                  true
% 11.63/1.97  --sup_fun_splitting                     true
% 11.63/1.97  --sup_smt_interval                      50000
% 11.63/1.97  
% 11.63/1.97  ------ Superposition Simplification Setup
% 11.63/1.97  
% 11.63/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.63/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.63/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.63/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.63/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.63/1.97  --sup_immed_triv                        [TrivRules]
% 11.63/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.97  --sup_immed_bw_main                     []
% 11.63/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.63/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.97  --sup_input_bw                          []
% 11.63/1.97  
% 11.63/1.97  ------ Combination Options
% 11.63/1.97  
% 11.63/1.97  --comb_res_mult                         3
% 11.63/1.97  --comb_sup_mult                         2
% 11.63/1.97  --comb_inst_mult                        10
% 11.63/1.97  
% 11.63/1.97  ------ Debug Options
% 11.63/1.97  
% 11.63/1.97  --dbg_backtrace                         false
% 11.63/1.97  --dbg_dump_prop_clauses                 false
% 11.63/1.97  --dbg_dump_prop_clauses_file            -
% 11.63/1.97  --dbg_out_stat                          false
% 11.63/1.97  ------ Parsing...
% 11.63/1.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.63/1.97  
% 11.63/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.63/1.97  
% 11.63/1.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.63/1.97  
% 11.63/1.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.63/1.97  ------ Proving...
% 11.63/1.97  ------ Problem Properties 
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  clauses                                 30
% 11.63/1.97  conjectures                             14
% 11.63/1.97  EPR                                     11
% 11.63/1.97  Horn                                    26
% 11.63/1.97  unary                                   14
% 11.63/1.97  binary                                  6
% 11.63/1.97  lits                                    82
% 11.63/1.97  lits eq                                 6
% 11.63/1.97  fd_pure                                 0
% 11.63/1.97  fd_pseudo                               0
% 11.63/1.97  fd_cond                                 0
% 11.63/1.97  fd_pseudo_cond                          0
% 11.63/1.97  AC symbols                              0
% 11.63/1.97  
% 11.63/1.97  ------ Schedule dynamic 5 is on 
% 11.63/1.97  
% 11.63/1.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  ------ 
% 11.63/1.97  Current options:
% 11.63/1.97  ------ 
% 11.63/1.97  
% 11.63/1.97  ------ Input Options
% 11.63/1.97  
% 11.63/1.97  --out_options                           all
% 11.63/1.97  --tptp_safe_out                         true
% 11.63/1.97  --problem_path                          ""
% 11.63/1.97  --include_path                          ""
% 11.63/1.97  --clausifier                            res/vclausify_rel
% 11.63/1.97  --clausifier_options                    ""
% 11.63/1.97  --stdin                                 false
% 11.63/1.97  --stats_out                             all
% 11.63/1.97  
% 11.63/1.97  ------ General Options
% 11.63/1.97  
% 11.63/1.97  --fof                                   false
% 11.63/1.97  --time_out_real                         305.
% 11.63/1.97  --time_out_virtual                      -1.
% 11.63/1.97  --symbol_type_check                     false
% 11.63/1.97  --clausify_out                          false
% 11.63/1.97  --sig_cnt_out                           false
% 11.63/1.97  --trig_cnt_out                          false
% 11.63/1.97  --trig_cnt_out_tolerance                1.
% 11.63/1.97  --trig_cnt_out_sk_spl                   false
% 11.63/1.97  --abstr_cl_out                          false
% 11.63/1.97  
% 11.63/1.97  ------ Global Options
% 11.63/1.97  
% 11.63/1.97  --schedule                              default
% 11.63/1.97  --add_important_lit                     false
% 11.63/1.97  --prop_solver_per_cl                    1000
% 11.63/1.97  --min_unsat_core                        false
% 11.63/1.97  --soft_assumptions                      false
% 11.63/1.97  --soft_lemma_size                       3
% 11.63/1.97  --prop_impl_unit_size                   0
% 11.63/1.97  --prop_impl_unit                        []
% 11.63/1.97  --share_sel_clauses                     true
% 11.63/1.97  --reset_solvers                         false
% 11.63/1.97  --bc_imp_inh                            [conj_cone]
% 11.63/1.97  --conj_cone_tolerance                   3.
% 11.63/1.97  --extra_neg_conj                        none
% 11.63/1.97  --large_theory_mode                     true
% 11.63/1.97  --prolific_symb_bound                   200
% 11.63/1.97  --lt_threshold                          2000
% 11.63/1.97  --clause_weak_htbl                      true
% 11.63/1.97  --gc_record_bc_elim                     false
% 11.63/1.97  
% 11.63/1.97  ------ Preprocessing Options
% 11.63/1.97  
% 11.63/1.97  --preprocessing_flag                    true
% 11.63/1.97  --time_out_prep_mult                    0.1
% 11.63/1.97  --splitting_mode                        input
% 11.63/1.97  --splitting_grd                         true
% 11.63/1.97  --splitting_cvd                         false
% 11.63/1.97  --splitting_cvd_svl                     false
% 11.63/1.97  --splitting_nvd                         32
% 11.63/1.97  --sub_typing                            true
% 11.63/1.97  --prep_gs_sim                           true
% 11.63/1.97  --prep_unflatten                        true
% 11.63/1.97  --prep_res_sim                          true
% 11.63/1.97  --prep_upred                            true
% 11.63/1.97  --prep_sem_filter                       exhaustive
% 11.63/1.97  --prep_sem_filter_out                   false
% 11.63/1.97  --pred_elim                             true
% 11.63/1.97  --res_sim_input                         true
% 11.63/1.97  --eq_ax_congr_red                       true
% 11.63/1.97  --pure_diseq_elim                       true
% 11.63/1.97  --brand_transform                       false
% 11.63/1.97  --non_eq_to_eq                          false
% 11.63/1.97  --prep_def_merge                        true
% 11.63/1.97  --prep_def_merge_prop_impl              false
% 11.63/1.97  --prep_def_merge_mbd                    true
% 11.63/1.97  --prep_def_merge_tr_red                 false
% 11.63/1.97  --prep_def_merge_tr_cl                  false
% 11.63/1.97  --smt_preprocessing                     true
% 11.63/1.97  --smt_ac_axioms                         fast
% 11.63/1.97  --preprocessed_out                      false
% 11.63/1.97  --preprocessed_stats                    false
% 11.63/1.97  
% 11.63/1.97  ------ Abstraction refinement Options
% 11.63/1.97  
% 11.63/1.97  --abstr_ref                             []
% 11.63/1.97  --abstr_ref_prep                        false
% 11.63/1.97  --abstr_ref_until_sat                   false
% 11.63/1.97  --abstr_ref_sig_restrict                funpre
% 11.63/1.97  --abstr_ref_af_restrict_to_split_sk     false
% 11.63/1.97  --abstr_ref_under                       []
% 11.63/1.97  
% 11.63/1.97  ------ SAT Options
% 11.63/1.97  
% 11.63/1.97  --sat_mode                              false
% 11.63/1.97  --sat_fm_restart_options                ""
% 11.63/1.97  --sat_gr_def                            false
% 11.63/1.97  --sat_epr_types                         true
% 11.63/1.97  --sat_non_cyclic_types                  false
% 11.63/1.97  --sat_finite_models                     false
% 11.63/1.97  --sat_fm_lemmas                         false
% 11.63/1.97  --sat_fm_prep                           false
% 11.63/1.97  --sat_fm_uc_incr                        true
% 11.63/1.97  --sat_out_model                         small
% 11.63/1.97  --sat_out_clauses                       false
% 11.63/1.97  
% 11.63/1.97  ------ QBF Options
% 11.63/1.97  
% 11.63/1.97  --qbf_mode                              false
% 11.63/1.97  --qbf_elim_univ                         false
% 11.63/1.97  --qbf_dom_inst                          none
% 11.63/1.97  --qbf_dom_pre_inst                      false
% 11.63/1.97  --qbf_sk_in                             false
% 11.63/1.97  --qbf_pred_elim                         true
% 11.63/1.97  --qbf_split                             512
% 11.63/1.97  
% 11.63/1.97  ------ BMC1 Options
% 11.63/1.97  
% 11.63/1.97  --bmc1_incremental                      false
% 11.63/1.97  --bmc1_axioms                           reachable_all
% 11.63/1.97  --bmc1_min_bound                        0
% 11.63/1.97  --bmc1_max_bound                        -1
% 11.63/1.97  --bmc1_max_bound_default                -1
% 11.63/1.97  --bmc1_symbol_reachability              true
% 11.63/1.97  --bmc1_property_lemmas                  false
% 11.63/1.97  --bmc1_k_induction                      false
% 11.63/1.97  --bmc1_non_equiv_states                 false
% 11.63/1.97  --bmc1_deadlock                         false
% 11.63/1.97  --bmc1_ucm                              false
% 11.63/1.97  --bmc1_add_unsat_core                   none
% 11.63/1.97  --bmc1_unsat_core_children              false
% 11.63/1.97  --bmc1_unsat_core_extrapolate_axioms    false
% 11.63/1.97  --bmc1_out_stat                         full
% 11.63/1.97  --bmc1_ground_init                      false
% 11.63/1.97  --bmc1_pre_inst_next_state              false
% 11.63/1.97  --bmc1_pre_inst_state                   false
% 11.63/1.97  --bmc1_pre_inst_reach_state             false
% 11.63/1.97  --bmc1_out_unsat_core                   false
% 11.63/1.97  --bmc1_aig_witness_out                  false
% 11.63/1.97  --bmc1_verbose                          false
% 11.63/1.97  --bmc1_dump_clauses_tptp                false
% 11.63/1.97  --bmc1_dump_unsat_core_tptp             false
% 11.63/1.97  --bmc1_dump_file                        -
% 11.63/1.97  --bmc1_ucm_expand_uc_limit              128
% 11.63/1.97  --bmc1_ucm_n_expand_iterations          6
% 11.63/1.97  --bmc1_ucm_extend_mode                  1
% 11.63/1.97  --bmc1_ucm_init_mode                    2
% 11.63/1.97  --bmc1_ucm_cone_mode                    none
% 11.63/1.97  --bmc1_ucm_reduced_relation_type        0
% 11.63/1.97  --bmc1_ucm_relax_model                  4
% 11.63/1.97  --bmc1_ucm_full_tr_after_sat            true
% 11.63/1.97  --bmc1_ucm_expand_neg_assumptions       false
% 11.63/1.97  --bmc1_ucm_layered_model                none
% 11.63/1.97  --bmc1_ucm_max_lemma_size               10
% 11.63/1.97  
% 11.63/1.97  ------ AIG Options
% 11.63/1.97  
% 11.63/1.97  --aig_mode                              false
% 11.63/1.97  
% 11.63/1.97  ------ Instantiation Options
% 11.63/1.97  
% 11.63/1.97  --instantiation_flag                    true
% 11.63/1.97  --inst_sos_flag                         true
% 11.63/1.97  --inst_sos_phase                        true
% 11.63/1.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.63/1.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.63/1.97  --inst_lit_sel_side                     none
% 11.63/1.97  --inst_solver_per_active                1400
% 11.63/1.97  --inst_solver_calls_frac                1.
% 11.63/1.97  --inst_passive_queue_type               priority_queues
% 11.63/1.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.63/1.97  --inst_passive_queues_freq              [25;2]
% 11.63/1.97  --inst_dismatching                      true
% 11.63/1.97  --inst_eager_unprocessed_to_passive     true
% 11.63/1.97  --inst_prop_sim_given                   true
% 11.63/1.97  --inst_prop_sim_new                     false
% 11.63/1.97  --inst_subs_new                         false
% 11.63/1.97  --inst_eq_res_simp                      false
% 11.63/1.97  --inst_subs_given                       false
% 11.63/1.97  --inst_orphan_elimination               true
% 11.63/1.97  --inst_learning_loop_flag               true
% 11.63/1.97  --inst_learning_start                   3000
% 11.63/1.97  --inst_learning_factor                  2
% 11.63/1.97  --inst_start_prop_sim_after_learn       3
% 11.63/1.97  --inst_sel_renew                        solver
% 11.63/1.97  --inst_lit_activity_flag                true
% 11.63/1.97  --inst_restr_to_given                   false
% 11.63/1.97  --inst_activity_threshold               500
% 11.63/1.97  --inst_out_proof                        true
% 11.63/1.97  
% 11.63/1.97  ------ Resolution Options
% 11.63/1.97  
% 11.63/1.97  --resolution_flag                       false
% 11.63/1.97  --res_lit_sel                           adaptive
% 11.63/1.97  --res_lit_sel_side                      none
% 11.63/1.97  --res_ordering                          kbo
% 11.63/1.97  --res_to_prop_solver                    active
% 11.63/1.97  --res_prop_simpl_new                    false
% 11.63/1.97  --res_prop_simpl_given                  true
% 11.63/1.97  --res_passive_queue_type                priority_queues
% 11.63/1.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.63/1.97  --res_passive_queues_freq               [15;5]
% 11.63/1.97  --res_forward_subs                      full
% 11.63/1.97  --res_backward_subs                     full
% 11.63/1.97  --res_forward_subs_resolution           true
% 11.63/1.97  --res_backward_subs_resolution          true
% 11.63/1.97  --res_orphan_elimination                true
% 11.63/1.97  --res_time_limit                        2.
% 11.63/1.97  --res_out_proof                         true
% 11.63/1.97  
% 11.63/1.97  ------ Superposition Options
% 11.63/1.97  
% 11.63/1.97  --superposition_flag                    true
% 11.63/1.97  --sup_passive_queue_type                priority_queues
% 11.63/1.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.63/1.97  --sup_passive_queues_freq               [8;1;4]
% 11.63/1.97  --demod_completeness_check              fast
% 11.63/1.97  --demod_use_ground                      true
% 11.63/1.97  --sup_to_prop_solver                    passive
% 11.63/1.97  --sup_prop_simpl_new                    true
% 11.63/1.97  --sup_prop_simpl_given                  true
% 11.63/1.97  --sup_fun_splitting                     true
% 11.63/1.97  --sup_smt_interval                      50000
% 11.63/1.97  
% 11.63/1.97  ------ Superposition Simplification Setup
% 11.63/1.97  
% 11.63/1.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.63/1.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.63/1.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.63/1.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.63/1.97  --sup_full_triv                         [TrivRules;PropSubs]
% 11.63/1.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.63/1.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.63/1.97  --sup_immed_triv                        [TrivRules]
% 11.63/1.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.97  --sup_immed_bw_main                     []
% 11.63/1.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.63/1.97  --sup_input_triv                        [Unflattening;TrivRules]
% 11.63/1.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.63/1.97  --sup_input_bw                          []
% 11.63/1.97  
% 11.63/1.97  ------ Combination Options
% 11.63/1.97  
% 11.63/1.97  --comb_res_mult                         3
% 11.63/1.97  --comb_sup_mult                         2
% 11.63/1.97  --comb_inst_mult                        10
% 11.63/1.97  
% 11.63/1.97  ------ Debug Options
% 11.63/1.97  
% 11.63/1.97  --dbg_backtrace                         false
% 11.63/1.97  --dbg_dump_prop_clauses                 false
% 11.63/1.97  --dbg_dump_prop_clauses_file            -
% 11.63/1.97  --dbg_out_stat                          false
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  ------ Proving...
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  % SZS status Theorem for theBenchmark.p
% 11.63/1.97  
% 11.63/1.97   Resolution empty clause
% 11.63/1.97  
% 11.63/1.97  % SZS output start CNFRefutation for theBenchmark.p
% 11.63/1.97  
% 11.63/1.97  fof(f16,conjecture,(
% 11.63/1.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f17,negated_conjecture,(
% 11.63/1.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 11.63/1.97    inference(negated_conjecture,[],[f16])).
% 11.63/1.97  
% 11.63/1.97  fof(f40,plain,(
% 11.63/1.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 11.63/1.97    inference(ennf_transformation,[],[f17])).
% 11.63/1.97  
% 11.63/1.97  fof(f41,plain,(
% 11.63/1.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 11.63/1.97    inference(flattening,[],[f40])).
% 11.63/1.97  
% 11.63/1.97  fof(f48,plain,(
% 11.63/1.97    ( ! [X2,X0,X3,X1] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4) & r1_tarski(sK4,u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 11.63/1.97    introduced(choice_axiom,[])).
% 11.63/1.97  
% 11.63/1.97  fof(f47,plain,(
% 11.63/1.97    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 11.63/1.97    introduced(choice_axiom,[])).
% 11.63/1.97  
% 11.63/1.97  fof(f46,plain,(
% 11.63/1.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 11.63/1.97    introduced(choice_axiom,[])).
% 11.63/1.97  
% 11.63/1.97  fof(f45,plain,(
% 11.63/1.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 11.63/1.97    introduced(choice_axiom,[])).
% 11.63/1.97  
% 11.63/1.97  fof(f44,plain,(
% 11.63/1.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 11.63/1.97    introduced(choice_axiom,[])).
% 11.63/1.97  
% 11.63/1.97  fof(f49,plain,(
% 11.63/1.97    ((((k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & r1_tarski(sK4,u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 11.63/1.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f48,f47,f46,f45,f44])).
% 11.63/1.97  
% 11.63/1.97  fof(f76,plain,(
% 11.63/1.97    m1_pre_topc(sK2,sK1)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f15,axiom,(
% 11.63/1.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f38,plain,(
% 11.63/1.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.63/1.97    inference(ennf_transformation,[],[f15])).
% 11.63/1.97  
% 11.63/1.97  fof(f39,plain,(
% 11.63/1.97    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.63/1.97    inference(flattening,[],[f38])).
% 11.63/1.97  
% 11.63/1.97  fof(f43,plain,(
% 11.63/1.97    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.63/1.97    inference(nnf_transformation,[],[f39])).
% 11.63/1.97  
% 11.63/1.97  fof(f68,plain,(
% 11.63/1.97    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f43])).
% 11.63/1.97  
% 11.63/1.97  fof(f73,plain,(
% 11.63/1.97    v2_pre_topc(sK1)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f74,plain,(
% 11.63/1.97    l1_pre_topc(sK1)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f81,plain,(
% 11.63/1.97    r1_tarski(sK4,u1_struct_0(sK2))),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f14,axiom,(
% 11.63/1.97    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f37,plain,(
% 11.63/1.97    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 11.63/1.97    inference(ennf_transformation,[],[f14])).
% 11.63/1.97  
% 11.63/1.97  fof(f66,plain,(
% 11.63/1.97    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f37])).
% 11.63/1.97  
% 11.63/1.97  fof(f1,axiom,(
% 11.63/1.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f19,plain,(
% 11.63/1.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.63/1.97    inference(ennf_transformation,[],[f1])).
% 11.63/1.97  
% 11.63/1.97  fof(f20,plain,(
% 11.63/1.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.63/1.97    inference(flattening,[],[f19])).
% 11.63/1.97  
% 11.63/1.97  fof(f50,plain,(
% 11.63/1.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f20])).
% 11.63/1.97  
% 11.63/1.97  fof(f79,plain,(
% 11.63/1.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f6,axiom,(
% 11.63/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f25,plain,(
% 11.63/1.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/1.97    inference(ennf_transformation,[],[f6])).
% 11.63/1.97  
% 11.63/1.97  fof(f56,plain,(
% 11.63/1.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/1.97    inference(cnf_transformation,[],[f25])).
% 11.63/1.97  
% 11.63/1.97  fof(f3,axiom,(
% 11.63/1.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f22,plain,(
% 11.63/1.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.63/1.97    inference(ennf_transformation,[],[f3])).
% 11.63/1.97  
% 11.63/1.97  fof(f53,plain,(
% 11.63/1.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f22])).
% 11.63/1.97  
% 11.63/1.97  fof(f5,axiom,(
% 11.63/1.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f24,plain,(
% 11.63/1.97    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.63/1.97    inference(ennf_transformation,[],[f5])).
% 11.63/1.97  
% 11.63/1.97  fof(f55,plain,(
% 11.63/1.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f24])).
% 11.63/1.97  
% 11.63/1.97  fof(f2,axiom,(
% 11.63/1.97    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f21,plain,(
% 11.63/1.97    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.63/1.97    inference(ennf_transformation,[],[f2])).
% 11.63/1.97  
% 11.63/1.97  fof(f42,plain,(
% 11.63/1.97    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.63/1.97    inference(nnf_transformation,[],[f21])).
% 11.63/1.97  
% 11.63/1.97  fof(f51,plain,(
% 11.63/1.97    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f42])).
% 11.63/1.97  
% 11.63/1.97  fof(f7,axiom,(
% 11.63/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f18,plain,(
% 11.63/1.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 11.63/1.97    inference(pure_predicate_removal,[],[f7])).
% 11.63/1.97  
% 11.63/1.97  fof(f26,plain,(
% 11.63/1.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/1.97    inference(ennf_transformation,[],[f18])).
% 11.63/1.97  
% 11.63/1.97  fof(f57,plain,(
% 11.63/1.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/1.97    inference(cnf_transformation,[],[f26])).
% 11.63/1.97  
% 11.63/1.97  fof(f9,axiom,(
% 11.63/1.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f28,plain,(
% 11.63/1.97    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.63/1.97    inference(ennf_transformation,[],[f9])).
% 11.63/1.97  
% 11.63/1.97  fof(f29,plain,(
% 11.63/1.97    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.63/1.97    inference(flattening,[],[f28])).
% 11.63/1.97  
% 11.63/1.97  fof(f59,plain,(
% 11.63/1.97    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f29])).
% 11.63/1.97  
% 11.63/1.97  fof(f77,plain,(
% 11.63/1.97    v1_funct_1(sK3)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f10,axiom,(
% 11.63/1.97    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f30,plain,(
% 11.63/1.97    ! [X0,X1,X2,X3] : (! [X4] : (((m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))) | (~r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) | ~r1_tarski(X1,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_2(X4,X0,X3) | ~v1_funct_1(X4))) | v1_xboole_0(X3))),
% 11.63/1.97    inference(ennf_transformation,[],[f10])).
% 11.63/1.97  
% 11.63/1.97  fof(f31,plain,(
% 11.63/1.97    ! [X0,X1,X2,X3] : (! [X4] : ((m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))) | ~r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) | ~r1_tarski(X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_2(X4,X0,X3) | ~v1_funct_1(X4)) | v1_xboole_0(X3))),
% 11.63/1.97    inference(flattening,[],[f30])).
% 11.63/1.97  
% 11.63/1.97  fof(f62,plain,(
% 11.63/1.97    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) | ~r1_tarski(X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_2(X4,X0,X3) | ~v1_funct_1(X4) | v1_xboole_0(X3)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f31])).
% 11.63/1.97  
% 11.63/1.97  fof(f8,axiom,(
% 11.63/1.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f27,plain,(
% 11.63/1.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.63/1.97    inference(ennf_transformation,[],[f8])).
% 11.63/1.97  
% 11.63/1.97  fof(f58,plain,(
% 11.63/1.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.63/1.97    inference(cnf_transformation,[],[f27])).
% 11.63/1.97  
% 11.63/1.97  fof(f69,plain,(
% 11.63/1.97    ~v2_struct_0(sK0)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f71,plain,(
% 11.63/1.97    l1_pre_topc(sK0)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f78,plain,(
% 11.63/1.97    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f11,axiom,(
% 11.63/1.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f32,plain,(
% 11.63/1.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.63/1.97    inference(ennf_transformation,[],[f11])).
% 11.63/1.97  
% 11.63/1.97  fof(f63,plain,(
% 11.63/1.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f32])).
% 11.63/1.97  
% 11.63/1.97  fof(f12,axiom,(
% 11.63/1.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f33,plain,(
% 11.63/1.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.63/1.97    inference(ennf_transformation,[],[f12])).
% 11.63/1.97  
% 11.63/1.97  fof(f34,plain,(
% 11.63/1.97    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.63/1.97    inference(flattening,[],[f33])).
% 11.63/1.97  
% 11.63/1.97  fof(f64,plain,(
% 11.63/1.97    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f34])).
% 11.63/1.97  
% 11.63/1.97  fof(f13,axiom,(
% 11.63/1.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f35,plain,(
% 11.63/1.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 11.63/1.97    inference(ennf_transformation,[],[f13])).
% 11.63/1.97  
% 11.63/1.97  fof(f36,plain,(
% 11.63/1.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 11.63/1.97    inference(flattening,[],[f35])).
% 11.63/1.97  
% 11.63/1.97  fof(f65,plain,(
% 11.63/1.97    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f36])).
% 11.63/1.97  
% 11.63/1.97  fof(f70,plain,(
% 11.63/1.97    v2_pre_topc(sK0)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f72,plain,(
% 11.63/1.97    ~v2_struct_0(sK1)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f82,plain,(
% 11.63/1.97    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 11.63/1.97    inference(cnf_transformation,[],[f49])).
% 11.63/1.97  
% 11.63/1.97  fof(f4,axiom,(
% 11.63/1.97    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 11.63/1.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.63/1.97  
% 11.63/1.97  fof(f23,plain,(
% 11.63/1.97    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 11.63/1.97    inference(ennf_transformation,[],[f4])).
% 11.63/1.97  
% 11.63/1.97  fof(f54,plain,(
% 11.63/1.97    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 11.63/1.97    inference(cnf_transformation,[],[f23])).
% 11.63/1.97  
% 11.63/1.97  cnf(c_25,negated_conjecture,
% 11.63/1.97      ( m1_pre_topc(sK2,sK1) ),
% 11.63/1.97      inference(cnf_transformation,[],[f76]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_903,negated_conjecture,
% 11.63/1.97      ( m1_pre_topc(sK2,sK1) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_25]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1458,plain,
% 11.63/1.97      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_17,plain,
% 11.63/1.97      ( ~ m1_pre_topc(X0,X1)
% 11.63/1.97      | ~ m1_pre_topc(X1,X2)
% 11.63/1.97      | ~ m1_pre_topc(X0,X2)
% 11.63/1.97      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 11.63/1.97      | ~ v2_pre_topc(X2)
% 11.63/1.97      | ~ l1_pre_topc(X2) ),
% 11.63/1.97      inference(cnf_transformation,[],[f68]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_911,plain,
% 11.63/1.97      ( ~ m1_pre_topc(X0_56,X1_56)
% 11.63/1.97      | ~ m1_pre_topc(X1_56,X2_56)
% 11.63/1.97      | ~ m1_pre_topc(X0_56,X2_56)
% 11.63/1.97      | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56))
% 11.63/1.97      | ~ v2_pre_topc(X2_56)
% 11.63/1.97      | ~ l1_pre_topc(X2_56) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_17]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1451,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 11.63/1.97      | m1_pre_topc(X1_56,X2_56) != iProver_top
% 11.63/1.97      | m1_pre_topc(X0_56,X2_56) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56)) = iProver_top
% 11.63/1.97      | v2_pre_topc(X2_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X2_56) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2212,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,sK2) != iProver_top
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(X0_56),u1_struct_0(sK2)) = iProver_top
% 11.63/1.97      | v2_pre_topc(sK1) != iProver_top
% 11.63/1.97      | l1_pre_topc(sK1) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1458,c_1451]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_28,negated_conjecture,
% 11.63/1.97      ( v2_pre_topc(sK1) ),
% 11.63/1.97      inference(cnf_transformation,[],[f73]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_37,plain,
% 11.63/1.97      ( v2_pre_topc(sK1) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_27,negated_conjecture,
% 11.63/1.97      ( l1_pre_topc(sK1) ),
% 11.63/1.97      inference(cnf_transformation,[],[f74]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_38,plain,
% 11.63/1.97      ( l1_pre_topc(sK1) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2386,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,sK2) != iProver_top
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(X0_56),u1_struct_0(sK2)) = iProver_top ),
% 11.63/1.97      inference(global_propositional_subsumption,
% 11.63/1.97                [status(thm)],
% 11.63/1.97                [c_2212,c_37,c_38]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_20,negated_conjecture,
% 11.63/1.97      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 11.63/1.97      inference(cnf_transformation,[],[f81]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_908,negated_conjecture,
% 11.63/1.97      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_20]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1453,plain,
% 11.63/1.97      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_16,plain,
% 11.63/1.97      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f66]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_912,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,X0_56) | ~ l1_pre_topc(X0_56) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_16]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1450,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,X0_56) = iProver_top
% 11.63/1.97      | l1_pre_topc(X0_56) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2213,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56)) = iProver_top
% 11.63/1.97      | v2_pre_topc(X1_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X1_56) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1450,c_1451]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_0,plain,
% 11.63/1.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 11.63/1.97      inference(cnf_transformation,[],[f50]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_923,plain,
% 11.63/1.97      ( ~ r1_tarski(X0_54,X1_54)
% 11.63/1.97      | ~ r1_tarski(X2_54,X0_54)
% 11.63/1.97      | r1_tarski(X2_54,X1_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_0]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1439,plain,
% 11.63/1.97      ( r1_tarski(X0_54,X1_54) != iProver_top
% 11.63/1.97      | r1_tarski(X2_54,X0_54) != iProver_top
% 11.63/1.97      | r1_tarski(X2_54,X1_54) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_923]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_4812,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(X0_56)) != iProver_top
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(X1_56)) = iProver_top
% 11.63/1.97      | v2_pre_topc(X1_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X1_56) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_2213,c_1439]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6415,plain,
% 11.63/1.97      ( m1_pre_topc(sK2,X0_56) != iProver_top
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(X0_56)) = iProver_top
% 11.63/1.97      | v2_pre_topc(X0_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X0_56) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1453,c_4812]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6481,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 11.63/1.97      | m1_pre_topc(sK2,X0_56) != iProver_top
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(X1_56)) = iProver_top
% 11.63/1.97      | v2_pre_topc(X1_56) != iProver_top
% 11.63/1.97      | v2_pre_topc(X0_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X1_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X0_56) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_6415,c_4812]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_8147,plain,
% 11.63/1.97      ( m1_pre_topc(sK2,sK2) != iProver_top
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top
% 11.63/1.97      | v2_pre_topc(sK2) != iProver_top
% 11.63/1.97      | v2_pre_topc(sK1) != iProver_top
% 11.63/1.97      | l1_pre_topc(sK2) != iProver_top
% 11.63/1.97      | l1_pre_topc(sK1) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1458,c_6481]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_40,plain,
% 11.63/1.97      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_45,plain,
% 11.63/1.97      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_50,plain,
% 11.63/1.97      ( m1_pre_topc(X0,X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_52,plain,
% 11.63/1.97      ( m1_pre_topc(sK1,sK1) = iProver_top | l1_pre_topc(sK1) != iProver_top ),
% 11.63/1.97      inference(instantiation,[status(thm)],[c_50]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3836,plain,
% 11.63/1.97      ( ~ r1_tarski(X0_54,u1_struct_0(X0_56))
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(X1_56))
% 11.63/1.97      | ~ r1_tarski(u1_struct_0(X0_56),u1_struct_0(X1_56)) ),
% 11.63/1.97      inference(instantiation,[status(thm)],[c_923]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6287,plain,
% 11.63/1.97      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56))
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(X0_56))
% 11.63/1.97      | ~ r1_tarski(sK4,u1_struct_0(sK2)) ),
% 11.63/1.97      inference(instantiation,[status(thm)],[c_3836]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6288,plain,
% 11.63/1.97      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56)) != iProver_top
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(X0_56)) = iProver_top
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_6287]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6290,plain,
% 11.63/1.97      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top
% 11.63/1.97      | r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
% 11.63/1.97      inference(instantiation,[status(thm)],[c_6288]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6321,plain,
% 11.63/1.97      ( ~ m1_pre_topc(X0_56,X1_56)
% 11.63/1.97      | ~ m1_pre_topc(sK2,X1_56)
% 11.63/1.97      | ~ m1_pre_topc(sK2,X0_56)
% 11.63/1.97      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56))
% 11.63/1.97      | ~ v2_pre_topc(X1_56)
% 11.63/1.97      | ~ l1_pre_topc(X1_56) ),
% 11.63/1.97      inference(instantiation,[status(thm)],[c_911]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6322,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,X1_56) != iProver_top
% 11.63/1.97      | m1_pre_topc(sK2,X1_56) != iProver_top
% 11.63/1.97      | m1_pre_topc(sK2,X0_56) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(sK2),u1_struct_0(X0_56)) = iProver_top
% 11.63/1.97      | v2_pre_topc(X1_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X1_56) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_6321]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6324,plain,
% 11.63/1.97      ( m1_pre_topc(sK2,sK1) != iProver_top
% 11.63/1.97      | m1_pre_topc(sK1,sK1) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 11.63/1.97      | v2_pre_topc(sK1) != iProver_top
% 11.63/1.97      | l1_pre_topc(sK1) != iProver_top ),
% 11.63/1.97      inference(instantiation,[status(thm)],[c_6322]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_8255,plain,
% 11.63/1.97      ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
% 11.63/1.97      inference(global_propositional_subsumption,
% 11.63/1.97                [status(thm)],
% 11.63/1.97                [c_8147,c_37,c_38,c_40,c_45,c_52,c_6290,c_6324]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_8260,plain,
% 11.63/1.97      ( r1_tarski(X0_54,u1_struct_0(sK1)) = iProver_top
% 11.63/1.97      | r1_tarski(X0_54,sK4) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_8255,c_1439]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_8275,plain,
% 11.63/1.97      ( r1_tarski(X0_54,X1_54) != iProver_top
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(sK1)) = iProver_top
% 11.63/1.97      | r1_tarski(X1_54,sK4) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_8260,c_1439]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_8567,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,sK2) != iProver_top
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(X0_56),u1_struct_0(sK1)) = iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(sK2),sK4) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_2386,c_8275]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_22,negated_conjecture,
% 11.63/1.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 11.63/1.97      inference(cnf_transformation,[],[f79]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_906,negated_conjecture,
% 11.63/1.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_22]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1455,plain,
% 11.63/1.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_6,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f56]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_919,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.63/1.97      | v1_relat_1(X0_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_6]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1443,plain,
% 11.63/1.97      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 11.63/1.97      | v1_relat_1(X0_54) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1986,plain,
% 11.63/1.97      ( v1_relat_1(sK3) = iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1455,c_1443]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3,plain,
% 11.63/1.97      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.63/1.97      inference(cnf_transformation,[],[f53]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_922,plain,
% 11.63/1.97      ( ~ v1_relat_1(X0_54)
% 11.63/1.97      | k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_3]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1440,plain,
% 11.63/1.97      ( k2_relat_1(k7_relat_1(X0_54,X1_54)) = k9_relat_1(X0_54,X1_54)
% 11.63/1.97      | v1_relat_1(X0_54) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_922]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2048,plain,
% 11.63/1.97      ( k2_relat_1(k7_relat_1(sK3,X0_54)) = k9_relat_1(sK3,X0_54) ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1986,c_1440]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_5,plain,
% 11.63/1.97      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 11.63/1.97      | ~ v1_relat_1(X0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f55]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_920,plain,
% 11.63/1.97      ( r1_tarski(k2_relat_1(k7_relat_1(X0_54,X1_54)),k2_relat_1(X0_54))
% 11.63/1.97      | ~ v1_relat_1(X0_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_5]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1442,plain,
% 11.63/1.97      ( r1_tarski(k2_relat_1(k7_relat_1(X0_54,X1_54)),k2_relat_1(X0_54)) = iProver_top
% 11.63/1.97      | v1_relat_1(X0_54) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2402,plain,
% 11.63/1.97      ( r1_tarski(k9_relat_1(sK3,X0_54),k2_relat_1(sK3)) = iProver_top
% 11.63/1.97      | v1_relat_1(sK3) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_2048,c_1442]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3102,plain,
% 11.63/1.97      ( r1_tarski(k9_relat_1(sK3,X0_54),k2_relat_1(sK3)) = iProver_top ),
% 11.63/1.97      inference(global_propositional_subsumption,[status(thm)],[c_2402,c_1986]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2,plain,
% 11.63/1.97      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f51]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_7,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v5_relat_1(X0,X2) ),
% 11.63/1.97      inference(cnf_transformation,[],[f57]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_369,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/1.97      | r1_tarski(k2_relat_1(X3),X4)
% 11.63/1.97      | ~ v1_relat_1(X3)
% 11.63/1.97      | X0 != X3
% 11.63/1.97      | X2 != X4 ),
% 11.63/1.97      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_370,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/1.97      | r1_tarski(k2_relat_1(X0),X2)
% 11.63/1.97      | ~ v1_relat_1(X0) ),
% 11.63/1.97      inference(unflattening,[status(thm)],[c_369]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_374,plain,
% 11.63/1.97      ( r1_tarski(k2_relat_1(X0),X2)
% 11.63/1.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.63/1.97      inference(global_propositional_subsumption,[status(thm)],[c_370,c_6]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_375,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/1.97      | r1_tarski(k2_relat_1(X0),X2) ),
% 11.63/1.97      inference(renaming,[status(thm)],[c_374]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_894,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.63/1.97      | r1_tarski(k2_relat_1(X0_54),X2_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_375]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1467,plain,
% 11.63/1.97      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 11.63/1.97      | r1_tarski(k2_relat_1(X0_54),X2_54) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3573,plain,
% 11.63/1.97      ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK0)) = iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1455,c_1467]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3640,plain,
% 11.63/1.97      ( r1_tarski(X0_54,u1_struct_0(sK0)) = iProver_top
% 11.63/1.97      | r1_tarski(X0_54,k2_relat_1(sK3)) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_3573,c_1439]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3653,plain,
% 11.63/1.97      ( r1_tarski(k9_relat_1(sK3,X0_54),u1_struct_0(sK0)) = iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_3102,c_3640]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_9,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/1.97      | ~ v1_funct_1(X0)
% 11.63/1.97      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.63/1.97      inference(cnf_transformation,[],[f59]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_917,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.63/1.97      | ~ v1_funct_1(X0_54)
% 11.63/1.97      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_9]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1445,plain,
% 11.63/1.97      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 11.63/1.97      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 11.63/1.97      | v1_funct_1(X2_54) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2207,plain,
% 11.63/1.97      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54) = k7_relat_1(sK3,X0_54)
% 11.63/1.97      | v1_funct_1(sK3) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1455,c_1445]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_24,negated_conjecture,
% 11.63/1.97      ( v1_funct_1(sK3) ),
% 11.63/1.97      inference(cnf_transformation,[],[f77]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_41,plain,
% 11.63/1.97      ( v1_funct_1(sK3) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2334,plain,
% 11.63/1.97      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54) = k7_relat_1(sK3,X0_54) ),
% 11.63/1.97      inference(global_propositional_subsumption,[status(thm)],[c_2207,c_41]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_10,plain,
% 11.63/1.97      ( ~ v1_funct_2(X0,X1,X2)
% 11.63/1.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/1.97      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 11.63/1.97      | ~ r1_tarski(X3,X1)
% 11.63/1.97      | ~ r1_tarski(k7_relset_1(X1,X2,X0,X3),X4)
% 11.63/1.97      | v1_xboole_0(X2)
% 11.63/1.97      | ~ v1_funct_1(X0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f62]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_916,plain,
% 11.63/1.97      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 11.63/1.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.63/1.97      | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X3_54,X4_54)))
% 11.63/1.97      | ~ r1_tarski(X3_54,X1_54)
% 11.63/1.97      | ~ r1_tarski(k7_relset_1(X1_54,X2_54,X0_54,X3_54),X4_54)
% 11.63/1.97      | v1_xboole_0(X2_54)
% 11.63/1.97      | ~ v1_funct_1(X0_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_10]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1446,plain,
% 11.63/1.97      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 11.63/1.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 11.63/1.97      | m1_subset_1(k2_partfun1(X1_54,X2_54,X0_54,X3_54),k1_zfmisc_1(k2_zfmisc_1(X3_54,X4_54))) = iProver_top
% 11.63/1.97      | r1_tarski(X3_54,X1_54) != iProver_top
% 11.63/1.97      | r1_tarski(k7_relset_1(X1_54,X2_54,X0_54,X3_54),X4_54) != iProver_top
% 11.63/1.97      | v1_xboole_0(X2_54) = iProver_top
% 11.63/1.97      | v1_funct_1(X0_54) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_916]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2537,plain,
% 11.63/1.97      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 11.63/1.97      | m1_subset_1(k7_relat_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
% 11.63/1.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
% 11.63/1.97      | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54),X1_54) != iProver_top
% 11.63/1.97      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 11.63/1.97      | v1_funct_1(sK3) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_2334,c_1446]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_8,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.63/1.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.63/1.97      inference(cnf_transformation,[],[f58]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_918,plain,
% 11.63/1.97      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 11.63/1.97      | k7_relset_1(X1_54,X2_54,X0_54,X3_54) = k9_relat_1(X0_54,X3_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_8]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1444,plain,
% 11.63/1.97      ( k7_relset_1(X0_54,X1_54,X2_54,X3_54) = k9_relat_1(X2_54,X3_54)
% 11.63/1.97      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2161,plain,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0_54) = k9_relat_1(sK3,X0_54) ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1455,c_1444]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2541,plain,
% 11.63/1.97      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 11.63/1.97      | m1_subset_1(k7_relat_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
% 11.63/1.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
% 11.63/1.97      | r1_tarski(k9_relat_1(sK3,X0_54),X1_54) != iProver_top
% 11.63/1.97      | v1_xboole_0(u1_struct_0(sK0)) = iProver_top
% 11.63/1.97      | v1_funct_1(sK3) != iProver_top ),
% 11.63/1.97      inference(light_normalisation,[status(thm)],[c_2537,c_2161]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_32,negated_conjecture,
% 11.63/1.97      ( ~ v2_struct_0(sK0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f69]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_33,plain,
% 11.63/1.97      ( v2_struct_0(sK0) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_30,negated_conjecture,
% 11.63/1.97      ( l1_pre_topc(sK0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f71]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_35,plain,
% 11.63/1.97      ( l1_pre_topc(sK0) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_23,negated_conjecture,
% 11.63/1.97      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 11.63/1.97      inference(cnf_transformation,[],[f78]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_42,plain,
% 11.63/1.97      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_43,plain,
% 11.63/1.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_13,plain,
% 11.63/1.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f63]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_14,plain,
% 11.63/1.97      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 11.63/1.97      inference(cnf_transformation,[],[f64]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_350,plain,
% 11.63/1.97      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 11.63/1.97      inference(resolution,[status(thm)],[c_13,c_14]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_895,plain,
% 11.63/1.97      ( v2_struct_0(X0_56)
% 11.63/1.97      | ~ l1_pre_topc(X0_56)
% 11.63/1.97      | ~ v1_xboole_0(u1_struct_0(X0_56)) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_350]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1511,plain,
% 11.63/1.97      ( v2_struct_0(sK0)
% 11.63/1.97      | ~ l1_pre_topc(sK0)
% 11.63/1.97      | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 11.63/1.97      inference(instantiation,[status(thm)],[c_895]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1512,plain,
% 11.63/1.97      ( v2_struct_0(sK0) = iProver_top
% 11.63/1.97      | l1_pre_topc(sK0) != iProver_top
% 11.63/1.97      | v1_xboole_0(u1_struct_0(sK0)) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_1511]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2922,plain,
% 11.63/1.97      ( m1_subset_1(k7_relat_1(sK3,X0_54),k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) = iProver_top
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
% 11.63/1.97      | r1_tarski(k9_relat_1(sK3,X0_54),X1_54) != iProver_top ),
% 11.63/1.97      inference(global_propositional_subsumption,
% 11.63/1.97                [status(thm)],
% 11.63/1.97                [c_2541,c_33,c_35,c_41,c_42,c_43,c_1512]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2931,plain,
% 11.63/1.97      ( k7_relset_1(X0_54,X1_54,k7_relat_1(sK3,X0_54),X2_54) = k9_relat_1(k7_relat_1(sK3,X0_54),X2_54)
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top
% 11.63/1.97      | r1_tarski(k9_relat_1(sK3,X0_54),X1_54) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_2922,c_1444]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3997,plain,
% 11.63/1.97      ( k7_relset_1(X0_54,u1_struct_0(sK0),k7_relat_1(sK3,X0_54),X1_54) = k9_relat_1(k7_relat_1(sK3,X0_54),X1_54)
% 11.63/1.97      | r1_tarski(X0_54,u1_struct_0(sK1)) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_3653,c_2931]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_18630,plain,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54)
% 11.63/1.97      | m1_pre_topc(X0_56,sK2) != iProver_top
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | r1_tarski(u1_struct_0(sK2),sK4) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_8567,c_3997]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_18627,plain,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54)
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | v2_pre_topc(sK1) != iProver_top
% 11.63/1.97      | l1_pre_topc(sK1) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_2213,c_3997]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_46352,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) ),
% 11.63/1.97      inference(global_propositional_subsumption,
% 11.63/1.97                [status(thm)],
% 11.63/1.97                [c_18630,c_37,c_38,c_18627]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_46353,plain,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(X0_56),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(X0_56)),X0_54)
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top ),
% 11.63/1.97      inference(renaming,[status(thm)],[c_46352]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_46358,plain,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X0_54) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X0_54) ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1458,c_46353]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_15,plain,
% 11.63/1.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 11.63/1.97      | ~ m1_pre_topc(X3,X1)
% 11.63/1.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 11.63/1.97      | ~ v2_pre_topc(X2)
% 11.63/1.97      | ~ v2_pre_topc(X1)
% 11.63/1.97      | v2_struct_0(X1)
% 11.63/1.97      | v2_struct_0(X2)
% 11.63/1.97      | ~ l1_pre_topc(X1)
% 11.63/1.97      | ~ l1_pre_topc(X2)
% 11.63/1.97      | ~ v1_funct_1(X0)
% 11.63/1.97      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 11.63/1.97      inference(cnf_transformation,[],[f65]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_913,plain,
% 11.63/1.97      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56))
% 11.63/1.97      | ~ m1_pre_topc(X2_56,X0_56)
% 11.63/1.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56))))
% 11.63/1.97      | ~ v2_pre_topc(X1_56)
% 11.63/1.97      | ~ v2_pre_topc(X0_56)
% 11.63/1.97      | v2_struct_0(X0_56)
% 11.63/1.97      | v2_struct_0(X1_56)
% 11.63/1.97      | ~ l1_pre_topc(X0_56)
% 11.63/1.97      | ~ l1_pre_topc(X1_56)
% 11.63/1.97      | ~ v1_funct_1(X0_54)
% 11.63/1.97      | k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_54,X2_56) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_15]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1449,plain,
% 11.63/1.97      ( k2_partfun1(u1_struct_0(X0_56),u1_struct_0(X1_56),X0_54,u1_struct_0(X2_56)) = k2_tmap_1(X0_56,X1_56,X0_54,X2_56)
% 11.63/1.97      | v1_funct_2(X0_54,u1_struct_0(X0_56),u1_struct_0(X1_56)) != iProver_top
% 11.63/1.97      | m1_pre_topc(X2_56,X0_56) != iProver_top
% 11.63/1.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_56),u1_struct_0(X1_56)))) != iProver_top
% 11.63/1.97      | v2_pre_topc(X1_56) != iProver_top
% 11.63/1.97      | v2_pre_topc(X0_56) != iProver_top
% 11.63/1.97      | v2_struct_0(X0_56) = iProver_top
% 11.63/1.97      | v2_struct_0(X1_56) = iProver_top
% 11.63/1.97      | l1_pre_topc(X1_56) != iProver_top
% 11.63/1.97      | l1_pre_topc(X0_56) != iProver_top
% 11.63/1.97      | v1_funct_1(X0_54) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_913]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2691,plain,
% 11.63/1.97      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(X0_56)) = k2_tmap_1(sK1,sK0,sK3,X0_56)
% 11.63/1.97      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | v2_pre_topc(sK0) != iProver_top
% 11.63/1.97      | v2_pre_topc(sK1) != iProver_top
% 11.63/1.97      | v2_struct_0(sK0) = iProver_top
% 11.63/1.97      | v2_struct_0(sK1) = iProver_top
% 11.63/1.97      | l1_pre_topc(sK0) != iProver_top
% 11.63/1.97      | l1_pre_topc(sK1) != iProver_top
% 11.63/1.97      | v1_funct_1(sK3) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1455,c_1449]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2693,plain,
% 11.63/1.97      ( k2_tmap_1(sK1,sK0,sK3,X0_56) = k7_relat_1(sK3,u1_struct_0(X0_56))
% 11.63/1.97      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) != iProver_top
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | v2_pre_topc(sK0) != iProver_top
% 11.63/1.97      | v2_pre_topc(sK1) != iProver_top
% 11.63/1.97      | v2_struct_0(sK0) = iProver_top
% 11.63/1.97      | v2_struct_0(sK1) = iProver_top
% 11.63/1.97      | l1_pre_topc(sK0) != iProver_top
% 11.63/1.97      | l1_pre_topc(sK1) != iProver_top
% 11.63/1.97      | v1_funct_1(sK3) != iProver_top ),
% 11.63/1.97      inference(demodulation,[status(thm)],[c_2691,c_2334]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_31,negated_conjecture,
% 11.63/1.97      ( v2_pre_topc(sK0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f70]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_34,plain,
% 11.63/1.97      ( v2_pre_topc(sK0) = iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_29,negated_conjecture,
% 11.63/1.97      ( ~ v2_struct_0(sK1) ),
% 11.63/1.97      inference(cnf_transformation,[],[f72]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_36,plain,
% 11.63/1.97      ( v2_struct_0(sK1) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2945,plain,
% 11.63/1.97      ( m1_pre_topc(X0_56,sK1) != iProver_top
% 11.63/1.97      | k2_tmap_1(sK1,sK0,sK3,X0_56) = k7_relat_1(sK3,u1_struct_0(X0_56)) ),
% 11.63/1.97      inference(global_propositional_subsumption,
% 11.63/1.97                [status(thm)],
% 11.63/1.97                [c_2693,c_33,c_34,c_35,c_36,c_37,c_38,c_41,c_42]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2946,plain,
% 11.63/1.97      ( k2_tmap_1(sK1,sK0,sK3,X0_56) = k7_relat_1(sK3,u1_struct_0(X0_56))
% 11.63/1.97      | m1_pre_topc(X0_56,sK1) != iProver_top ),
% 11.63/1.97      inference(renaming,[status(thm)],[c_2945]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2951,plain,
% 11.63/1.97      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1458,c_2946]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_19,negated_conjecture,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
% 11.63/1.97      inference(cnf_transformation,[],[f82]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_909,negated_conjecture,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_19]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2268,plain,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) ),
% 11.63/1.97      inference(demodulation,[status(thm)],[c_2161,c_909]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_3028,plain,
% 11.63/1.97      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 11.63/1.97      inference(demodulation,[status(thm)],[c_2951,c_2268]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_46364,plain,
% 11.63/1.97      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 11.63/1.97      inference(demodulation,[status(thm)],[c_46358,c_3028]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_4,plain,
% 11.63/1.97      ( ~ r1_tarski(X0,X1)
% 11.63/1.97      | ~ v1_relat_1(X2)
% 11.63/1.97      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 11.63/1.97      inference(cnf_transformation,[],[f54]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_921,plain,
% 11.63/1.97      ( ~ r1_tarski(X0_54,X1_54)
% 11.63/1.97      | ~ v1_relat_1(X2_54)
% 11.63/1.97      | k9_relat_1(k7_relat_1(X2_54,X1_54),X0_54) = k9_relat_1(X2_54,X0_54) ),
% 11.63/1.97      inference(subtyping,[status(esa)],[c_4]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_1441,plain,
% 11.63/1.97      ( k9_relat_1(k7_relat_1(X0_54,X1_54),X2_54) = k9_relat_1(X0_54,X2_54)
% 11.63/1.97      | r1_tarski(X2_54,X1_54) != iProver_top
% 11.63/1.97      | v1_relat_1(X0_54) != iProver_top ),
% 11.63/1.97      inference(predicate_to_equality,[status(thm)],[c_921]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2051,plain,
% 11.63/1.97      ( k9_relat_1(k7_relat_1(X0_54,u1_struct_0(sK2)),sK4) = k9_relat_1(X0_54,sK4)
% 11.63/1.97      | v1_relat_1(X0_54) != iProver_top ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1453,c_1441]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_2332,plain,
% 11.63/1.97      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
% 11.63/1.97      inference(superposition,[status(thm)],[c_1986,c_2051]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_46365,plain,
% 11.63/1.97      ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
% 11.63/1.97      inference(light_normalisation,[status(thm)],[c_46364,c_2332]) ).
% 11.63/1.97  
% 11.63/1.97  cnf(c_46366,plain,
% 11.63/1.97      ( $false ),
% 11.63/1.97      inference(equality_resolution_simp,[status(thm)],[c_46365]) ).
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  % SZS output end CNFRefutation for theBenchmark.p
% 11.63/1.97  
% 11.63/1.97  ------                               Statistics
% 11.63/1.97  
% 11.63/1.97  ------ General
% 11.63/1.97  
% 11.63/1.97  abstr_ref_over_cycles:                  0
% 11.63/1.97  abstr_ref_under_cycles:                 0
% 11.63/1.97  gc_basic_clause_elim:                   0
% 11.63/1.97  forced_gc_time:                         0
% 11.63/1.97  parsing_time:                           0.009
% 11.63/1.97  unif_index_cands_time:                  0.
% 11.63/1.97  unif_index_add_time:                    0.
% 11.63/1.97  orderings_time:                         0.
% 11.63/1.97  out_proof_time:                         0.012
% 11.63/1.97  total_time:                             1.333
% 11.63/1.97  num_of_symbols:                         60
% 11.63/1.97  num_of_terms:                           19672
% 11.63/1.97  
% 11.63/1.97  ------ Preprocessing
% 11.63/1.97  
% 11.63/1.97  num_of_splits:                          0
% 11.63/1.97  num_of_split_atoms:                     0
% 11.63/1.97  num_of_reused_defs:                     0
% 11.63/1.97  num_eq_ax_congr_red:                    27
% 11.63/1.97  num_of_sem_filtered_clauses:            1
% 11.63/1.97  num_of_subtypes:                        3
% 11.63/1.97  monotx_restored_types:                  0
% 11.63/1.97  sat_num_of_epr_types:                   0
% 11.63/1.97  sat_num_of_non_cyclic_types:            0
% 11.63/1.97  sat_guarded_non_collapsed_types:        0
% 11.63/1.97  num_pure_diseq_elim:                    0
% 11.63/1.97  simp_replaced_by:                       0
% 11.63/1.97  res_preprocessed:                       154
% 11.63/1.97  prep_upred:                             0
% 11.63/1.97  prep_unflattend:                        10
% 11.63/1.97  smt_new_axioms:                         0
% 11.63/1.97  pred_elim_cands:                        10
% 11.63/1.97  pred_elim:                              2
% 11.63/1.97  pred_elim_cl:                           3
% 11.63/1.97  pred_elim_cycles:                       6
% 11.63/1.97  merged_defs:                            0
% 11.63/1.97  merged_defs_ncl:                        0
% 11.63/1.97  bin_hyper_res:                          0
% 11.63/1.97  prep_cycles:                            4
% 11.63/1.97  pred_elim_time:                         0.007
% 11.63/1.97  splitting_time:                         0.
% 11.63/1.97  sem_filter_time:                        0.
% 11.63/1.97  monotx_time:                            0.
% 11.63/1.97  subtype_inf_time:                       0.
% 11.63/1.97  
% 11.63/1.97  ------ Problem properties
% 11.63/1.97  
% 11.63/1.97  clauses:                                30
% 11.63/1.97  conjectures:                            14
% 11.63/1.97  epr:                                    11
% 11.63/1.97  horn:                                   26
% 11.63/1.97  ground:                                 14
% 11.63/1.97  unary:                                  14
% 11.63/1.97  binary:                                 6
% 11.63/1.97  lits:                                   82
% 11.63/1.97  lits_eq:                                6
% 11.63/1.97  fd_pure:                                0
% 11.63/1.97  fd_pseudo:                              0
% 11.63/1.97  fd_cond:                                0
% 11.63/1.97  fd_pseudo_cond:                         0
% 11.63/1.97  ac_symbols:                             0
% 11.63/1.97  
% 11.63/1.97  ------ Propositional Solver
% 11.63/1.97  
% 11.63/1.97  prop_solver_calls:                      36
% 11.63/1.97  prop_fast_solver_calls:                 2461
% 11.63/1.97  smt_solver_calls:                       0
% 11.63/1.97  smt_fast_solver_calls:                  0
% 11.63/1.97  prop_num_of_clauses:                    9715
% 11.63/1.97  prop_preprocess_simplified:             18111
% 11.63/1.97  prop_fo_subsumed:                       104
% 11.63/1.97  prop_solver_time:                       0.
% 11.63/1.97  smt_solver_time:                        0.
% 11.63/1.97  smt_fast_solver_time:                   0.
% 11.63/1.97  prop_fast_solver_time:                  0.
% 11.63/1.97  prop_unsat_core_time:                   0.
% 11.63/1.97  
% 11.63/1.97  ------ QBF
% 11.63/1.97  
% 11.63/1.97  qbf_q_res:                              0
% 11.63/1.97  qbf_num_tautologies:                    0
% 11.63/1.97  qbf_prep_cycles:                        0
% 11.63/1.97  
% 11.63/1.97  ------ BMC1
% 11.63/1.97  
% 11.63/1.97  bmc1_current_bound:                     -1
% 11.63/1.97  bmc1_last_solved_bound:                 -1
% 11.63/1.97  bmc1_unsat_core_size:                   -1
% 11.63/1.97  bmc1_unsat_core_parents_size:           -1
% 11.63/1.97  bmc1_merge_next_fun:                    0
% 11.63/1.97  bmc1_unsat_core_clauses_time:           0.
% 11.63/1.97  
% 11.63/1.97  ------ Instantiation
% 11.63/1.97  
% 11.63/1.97  inst_num_of_clauses:                    3499
% 11.63/1.97  inst_num_in_passive:                    59
% 11.63/1.97  inst_num_in_active:                     2093
% 11.63/1.97  inst_num_in_unprocessed:                1348
% 11.63/1.97  inst_num_of_loops:                      2150
% 11.63/1.97  inst_num_of_learning_restarts:          0
% 11.63/1.97  inst_num_moves_active_passive:          50
% 11.63/1.97  inst_lit_activity:                      0
% 11.63/1.97  inst_lit_activity_moves:                0
% 11.63/1.97  inst_num_tautologies:                   0
% 11.63/1.97  inst_num_prop_implied:                  0
% 11.63/1.97  inst_num_existing_simplified:           0
% 11.63/1.97  inst_num_eq_res_simplified:             0
% 11.63/1.97  inst_num_child_elim:                    0
% 11.63/1.97  inst_num_of_dismatching_blockings:      8675
% 11.63/1.97  inst_num_of_non_proper_insts:           10033
% 11.63/1.97  inst_num_of_duplicates:                 0
% 11.63/1.97  inst_inst_num_from_inst_to_res:         0
% 11.63/1.97  inst_dismatching_checking_time:         0.
% 11.63/1.97  
% 11.63/1.97  ------ Resolution
% 11.63/1.97  
% 11.63/1.97  res_num_of_clauses:                     0
% 11.63/1.97  res_num_in_passive:                     0
% 11.63/1.97  res_num_in_active:                      0
% 11.63/1.97  res_num_of_loops:                       158
% 11.63/1.97  res_forward_subset_subsumed:            634
% 11.63/1.97  res_backward_subset_subsumed:           6
% 11.63/1.97  res_forward_subsumed:                   0
% 11.63/1.97  res_backward_subsumed:                  0
% 11.63/1.97  res_forward_subsumption_resolution:     0
% 11.63/1.97  res_backward_subsumption_resolution:    0
% 11.63/1.97  res_clause_to_clause_subsumption:       4284
% 11.63/1.97  res_orphan_elimination:                 0
% 11.63/1.97  res_tautology_del:                      2619
% 11.63/1.97  res_num_eq_res_simplified:              0
% 11.63/1.97  res_num_sel_changes:                    0
% 11.63/1.97  res_moves_from_active_to_pass:          0
% 11.63/1.97  
% 11.63/1.97  ------ Superposition
% 11.63/1.97  
% 11.63/1.97  sup_time_total:                         0.
% 11.63/1.97  sup_time_generating:                    0.
% 11.63/1.97  sup_time_sim_full:                      0.
% 11.63/1.97  sup_time_sim_immed:                     0.
% 11.63/1.97  
% 11.63/1.97  sup_num_of_clauses:                     1225
% 11.63/1.97  sup_num_in_active:                      422
% 11.63/1.97  sup_num_in_passive:                     803
% 11.63/1.97  sup_num_of_loops:                       429
% 11.63/1.97  sup_fw_superposition:                   768
% 11.63/1.97  sup_bw_superposition:                   993
% 11.63/1.97  sup_immediate_simplified:               435
% 11.63/1.97  sup_given_eliminated:                   2
% 11.63/1.97  comparisons_done:                       0
% 11.63/1.97  comparisons_avoided:                    0
% 11.63/1.97  
% 11.63/1.97  ------ Simplifications
% 11.63/1.97  
% 11.63/1.97  
% 11.63/1.97  sim_fw_subset_subsumed:                 144
% 11.63/1.97  sim_bw_subset_subsumed:                 22
% 11.63/1.97  sim_fw_subsumed:                        191
% 11.63/1.97  sim_bw_subsumed:                        19
% 11.63/1.97  sim_fw_subsumption_res:                 0
% 11.63/1.97  sim_bw_subsumption_res:                 0
% 11.63/1.97  sim_tautology_del:                      8
% 11.63/1.97  sim_eq_tautology_del:                   2
% 11.63/1.97  sim_eq_res_simp:                        0
% 11.63/1.97  sim_fw_demodulated:                     37
% 11.63/1.97  sim_bw_demodulated:                     3
% 11.63/1.97  sim_light_normalised:                   51
% 11.63/1.97  sim_joinable_taut:                      0
% 11.63/1.97  sim_joinable_simp:                      0
% 11.63/1.97  sim_ac_normalised:                      0
% 11.63/1.97  sim_smt_subsumption:                    0
% 11.63/1.97  
%------------------------------------------------------------------------------
