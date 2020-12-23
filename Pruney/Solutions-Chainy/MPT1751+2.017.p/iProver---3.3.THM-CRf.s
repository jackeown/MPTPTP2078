%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:34 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  207 (1974 expanded)
%              Number of clauses        :  123 ( 565 expanded)
%              Number of leaves         :   26 ( 712 expanded)
%              Depth                    :   25
%              Number of atoms          :  686 (17461 expanded)
%              Number of equality atoms :  219 (2534 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
          & r1_tarski(X4,u1_struct_0(X2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4)
        & r1_tarski(sK4,u1_struct_0(X2))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f44,f51,f50,f49,f48,f47])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f17,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2873,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2881,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3518,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2873,c_2881])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_975,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | u1_struct_0(sK0) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_976,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = u1_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_975])).

cnf(c_978,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = u1_struct_0(sK1)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_976,c_30])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_23,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_513,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_531,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23,c_513])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_669,plain,
    ( v2_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_531,c_38])).

cnf(c_670,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_2236,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2995,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_2237,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2930,plain,
    ( u1_struct_0(sK0) != X0
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2237])).

cnf(c_3010,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2930])).

cnf(c_3128,plain,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_978,c_40,c_670,c_2995,c_3010])).

cnf(c_3639,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3518,c_3128])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_33,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_582,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_33])).

cnf(c_583,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_585,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_35])).

cnf(c_2870,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2887,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3298,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2870,c_2887])).

cnf(c_3646,plain,
    ( r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3639,c_3298])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2883,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4210,plain,
    ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3646,c_2883])).

cnf(c_3172,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2873,c_2887])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_296,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_372,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_296])).

cnf(c_3248,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_3742,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3248])).

cnf(c_3743,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3742])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4156,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4157,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4156])).

cnf(c_4858,plain,
    ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4210,c_3172,c_3743,c_4157])).

cnf(c_3652,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3639,c_2873])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2880,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3853,plain,
    ( k7_relset_1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3652,c_2880])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2882,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4303,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3853,c_2882])).

cnf(c_5805,plain,
    ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4303,c_3652])).

cnf(c_5811,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5805,c_2887])).

cnf(c_3648,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3639,c_3172])).

cnf(c_2871,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_5359,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3648,c_2871])).

cnf(c_5551,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5359,c_3172,c_3743,c_4157])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2885,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5558,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_5551,c_2885])).

cnf(c_20,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2876,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4349,plain,
    ( k7_relset_1(k1_relat_1(X0),X1,X0,X2) = k9_relat_1(X0,X2)
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2876,c_2880])).

cnf(c_9450,plain,
    ( k7_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),X1,k7_relat_1(sK3,X0),X2) = k9_relat_1(k7_relat_1(sK3,X0),X2)
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5558,c_4349])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2877,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4017,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3652,c_2877])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4530,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4017,c_49])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2878,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3966,plain,
    ( v1_funct_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3652,c_2878])).

cnf(c_4483,plain,
    ( v1_funct_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3966,c_49])).

cnf(c_4534,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4530,c_4483])).

cnf(c_2886,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2879,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4538,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4530,c_2879])).

cnf(c_5816,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4538,c_49,c_3652])).

cnf(c_5822,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5816,c_2887])).

cnf(c_6055,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5822,c_2871])).

cnf(c_8290,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_6055])).

cnf(c_20758,plain,
    ( k7_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),X1,k7_relat_1(sK3,X0),X2) = k9_relat_1(k7_relat_1(sK3,X0),X2)
    | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9450,c_4534,c_8290])).

cnf(c_20765,plain,
    ( k7_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0),k7_relat_1(sK3,X0),X1) = k9_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(superposition,[status(thm)],[c_5811,c_20758])).

cnf(c_20772,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X0) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X0) ),
    inference(superposition,[status(thm)],[c_4858,c_20765])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f78])).

cnf(c_549,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
    | sK2 != X3
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_550,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_554,plain,
    ( ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_37,c_36,c_35])).

cnf(c_555,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
    inference(renaming,[status(thm)],[c_554])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_555,c_39])).

cnf(c_628,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_632,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_40,c_38])).

cnf(c_1093,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_632])).

cnf(c_1094,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_1093])).

cnf(c_1096,plain,
    ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_32,c_30])).

cnf(c_3651,plain,
    ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3639,c_1096])).

cnf(c_4533,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    inference(demodulation,[status(thm)],[c_4530,c_3651])).

cnf(c_27,negated_conjecture,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3655,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k7_relset_1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3639,c_27])).

cnf(c_4302,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3853,c_3655])).

cnf(c_4601,plain,
    ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_4533,c_4302])).

cnf(c_20924,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_20772,c_4601])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2875,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2884,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3961,plain,
    ( k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK4) = k9_relat_1(X0,sK4)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2875,c_2884])).

cnf(c_5557,plain,
    ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_5551,c_3961])).

cnf(c_20926,plain,
    ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_20924,c_5557])).

cnf(c_20927,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_20926])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:08:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.75/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.50  
% 7.75/1.50  ------  iProver source info
% 7.75/1.50  
% 7.75/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.50  git: non_committed_changes: false
% 7.75/1.50  git: last_make_outside_of_git: false
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     num_symb
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       true
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  ------ Parsing...
% 7.75/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.50  ------ Proving...
% 7.75/1.50  ------ Problem Properties 
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  clauses                                 32
% 7.75/1.50  conjectures                             5
% 7.75/1.50  EPR                                     2
% 7.75/1.50  Horn                                    27
% 7.75/1.50  unary                                   10
% 7.75/1.50  binary                                  7
% 7.75/1.50  lits                                    87
% 7.75/1.50  lits eq                                 30
% 7.75/1.50  fd_pure                                 0
% 7.75/1.50  fd_pseudo                               0
% 7.75/1.50  fd_cond                                 2
% 7.75/1.50  fd_pseudo_cond                          0
% 7.75/1.50  AC symbols                              0
% 7.75/1.50  
% 7.75/1.50  ------ Schedule dynamic 5 is on 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ 
% 7.75/1.50  Current options:
% 7.75/1.50  ------ 
% 7.75/1.50  
% 7.75/1.50  ------ Input Options
% 7.75/1.50  
% 7.75/1.50  --out_options                           all
% 7.75/1.50  --tptp_safe_out                         true
% 7.75/1.50  --problem_path                          ""
% 7.75/1.50  --include_path                          ""
% 7.75/1.50  --clausifier                            res/vclausify_rel
% 7.75/1.50  --clausifier_options                    ""
% 7.75/1.50  --stdin                                 false
% 7.75/1.50  --stats_out                             all
% 7.75/1.50  
% 7.75/1.50  ------ General Options
% 7.75/1.50  
% 7.75/1.50  --fof                                   false
% 7.75/1.50  --time_out_real                         305.
% 7.75/1.50  --time_out_virtual                      -1.
% 7.75/1.50  --symbol_type_check                     false
% 7.75/1.50  --clausify_out                          false
% 7.75/1.50  --sig_cnt_out                           false
% 7.75/1.50  --trig_cnt_out                          false
% 7.75/1.50  --trig_cnt_out_tolerance                1.
% 7.75/1.50  --trig_cnt_out_sk_spl                   false
% 7.75/1.50  --abstr_cl_out                          false
% 7.75/1.50  
% 7.75/1.50  ------ Global Options
% 7.75/1.50  
% 7.75/1.50  --schedule                              default
% 7.75/1.50  --add_important_lit                     false
% 7.75/1.50  --prop_solver_per_cl                    1000
% 7.75/1.50  --min_unsat_core                        false
% 7.75/1.50  --soft_assumptions                      false
% 7.75/1.50  --soft_lemma_size                       3
% 7.75/1.50  --prop_impl_unit_size                   0
% 7.75/1.50  --prop_impl_unit                        []
% 7.75/1.50  --share_sel_clauses                     true
% 7.75/1.50  --reset_solvers                         false
% 7.75/1.50  --bc_imp_inh                            [conj_cone]
% 7.75/1.50  --conj_cone_tolerance                   3.
% 7.75/1.50  --extra_neg_conj                        none
% 7.75/1.50  --large_theory_mode                     true
% 7.75/1.50  --prolific_symb_bound                   200
% 7.75/1.50  --lt_threshold                          2000
% 7.75/1.50  --clause_weak_htbl                      true
% 7.75/1.50  --gc_record_bc_elim                     false
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing Options
% 7.75/1.50  
% 7.75/1.50  --preprocessing_flag                    true
% 7.75/1.50  --time_out_prep_mult                    0.1
% 7.75/1.50  --splitting_mode                        input
% 7.75/1.50  --splitting_grd                         true
% 7.75/1.50  --splitting_cvd                         false
% 7.75/1.50  --splitting_cvd_svl                     false
% 7.75/1.50  --splitting_nvd                         32
% 7.75/1.50  --sub_typing                            true
% 7.75/1.50  --prep_gs_sim                           true
% 7.75/1.50  --prep_unflatten                        true
% 7.75/1.50  --prep_res_sim                          true
% 7.75/1.50  --prep_upred                            true
% 7.75/1.50  --prep_sem_filter                       exhaustive
% 7.75/1.50  --prep_sem_filter_out                   false
% 7.75/1.50  --pred_elim                             true
% 7.75/1.50  --res_sim_input                         true
% 7.75/1.50  --eq_ax_congr_red                       true
% 7.75/1.50  --pure_diseq_elim                       true
% 7.75/1.50  --brand_transform                       false
% 7.75/1.50  --non_eq_to_eq                          false
% 7.75/1.50  --prep_def_merge                        true
% 7.75/1.50  --prep_def_merge_prop_impl              false
% 7.75/1.50  --prep_def_merge_mbd                    true
% 7.75/1.50  --prep_def_merge_tr_red                 false
% 7.75/1.50  --prep_def_merge_tr_cl                  false
% 7.75/1.50  --smt_preprocessing                     true
% 7.75/1.50  --smt_ac_axioms                         fast
% 7.75/1.50  --preprocessed_out                      false
% 7.75/1.50  --preprocessed_stats                    false
% 7.75/1.50  
% 7.75/1.50  ------ Abstraction refinement Options
% 7.75/1.50  
% 7.75/1.50  --abstr_ref                             []
% 7.75/1.50  --abstr_ref_prep                        false
% 7.75/1.50  --abstr_ref_until_sat                   false
% 7.75/1.50  --abstr_ref_sig_restrict                funpre
% 7.75/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.75/1.50  --abstr_ref_under                       []
% 7.75/1.50  
% 7.75/1.50  ------ SAT Options
% 7.75/1.50  
% 7.75/1.50  --sat_mode                              false
% 7.75/1.50  --sat_fm_restart_options                ""
% 7.75/1.50  --sat_gr_def                            false
% 7.75/1.50  --sat_epr_types                         true
% 7.75/1.50  --sat_non_cyclic_types                  false
% 7.75/1.50  --sat_finite_models                     false
% 7.75/1.50  --sat_fm_lemmas                         false
% 7.75/1.50  --sat_fm_prep                           false
% 7.75/1.50  --sat_fm_uc_incr                        true
% 7.75/1.50  --sat_out_model                         small
% 7.75/1.50  --sat_out_clauses                       false
% 7.75/1.50  
% 7.75/1.50  ------ QBF Options
% 7.75/1.50  
% 7.75/1.50  --qbf_mode                              false
% 7.75/1.50  --qbf_elim_univ                         false
% 7.75/1.50  --qbf_dom_inst                          none
% 7.75/1.50  --qbf_dom_pre_inst                      false
% 7.75/1.50  --qbf_sk_in                             false
% 7.75/1.50  --qbf_pred_elim                         true
% 7.75/1.50  --qbf_split                             512
% 7.75/1.50  
% 7.75/1.50  ------ BMC1 Options
% 7.75/1.50  
% 7.75/1.50  --bmc1_incremental                      false
% 7.75/1.50  --bmc1_axioms                           reachable_all
% 7.75/1.50  --bmc1_min_bound                        0
% 7.75/1.50  --bmc1_max_bound                        -1
% 7.75/1.50  --bmc1_max_bound_default                -1
% 7.75/1.50  --bmc1_symbol_reachability              true
% 7.75/1.50  --bmc1_property_lemmas                  false
% 7.75/1.50  --bmc1_k_induction                      false
% 7.75/1.50  --bmc1_non_equiv_states                 false
% 7.75/1.50  --bmc1_deadlock                         false
% 7.75/1.50  --bmc1_ucm                              false
% 7.75/1.50  --bmc1_add_unsat_core                   none
% 7.75/1.50  --bmc1_unsat_core_children              false
% 7.75/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.75/1.50  --bmc1_out_stat                         full
% 7.75/1.50  --bmc1_ground_init                      false
% 7.75/1.50  --bmc1_pre_inst_next_state              false
% 7.75/1.50  --bmc1_pre_inst_state                   false
% 7.75/1.50  --bmc1_pre_inst_reach_state             false
% 7.75/1.50  --bmc1_out_unsat_core                   false
% 7.75/1.50  --bmc1_aig_witness_out                  false
% 7.75/1.50  --bmc1_verbose                          false
% 7.75/1.50  --bmc1_dump_clauses_tptp                false
% 7.75/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.75/1.50  --bmc1_dump_file                        -
% 7.75/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.75/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.75/1.50  --bmc1_ucm_extend_mode                  1
% 7.75/1.50  --bmc1_ucm_init_mode                    2
% 7.75/1.50  --bmc1_ucm_cone_mode                    none
% 7.75/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.75/1.50  --bmc1_ucm_relax_model                  4
% 7.75/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.75/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.75/1.50  --bmc1_ucm_layered_model                none
% 7.75/1.50  --bmc1_ucm_max_lemma_size               10
% 7.75/1.50  
% 7.75/1.50  ------ AIG Options
% 7.75/1.50  
% 7.75/1.50  --aig_mode                              false
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation Options
% 7.75/1.50  
% 7.75/1.50  --instantiation_flag                    true
% 7.75/1.50  --inst_sos_flag                         true
% 7.75/1.50  --inst_sos_phase                        true
% 7.75/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.75/1.50  --inst_lit_sel_side                     none
% 7.75/1.50  --inst_solver_per_active                1400
% 7.75/1.50  --inst_solver_calls_frac                1.
% 7.75/1.50  --inst_passive_queue_type               priority_queues
% 7.75/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.75/1.50  --inst_passive_queues_freq              [25;2]
% 7.75/1.50  --inst_dismatching                      true
% 7.75/1.50  --inst_eager_unprocessed_to_passive     true
% 7.75/1.50  --inst_prop_sim_given                   true
% 7.75/1.50  --inst_prop_sim_new                     false
% 7.75/1.50  --inst_subs_new                         false
% 7.75/1.50  --inst_eq_res_simp                      false
% 7.75/1.50  --inst_subs_given                       false
% 7.75/1.50  --inst_orphan_elimination               true
% 7.75/1.50  --inst_learning_loop_flag               true
% 7.75/1.50  --inst_learning_start                   3000
% 7.75/1.50  --inst_learning_factor                  2
% 7.75/1.50  --inst_start_prop_sim_after_learn       3
% 7.75/1.50  --inst_sel_renew                        solver
% 7.75/1.50  --inst_lit_activity_flag                true
% 7.75/1.50  --inst_restr_to_given                   false
% 7.75/1.50  --inst_activity_threshold               500
% 7.75/1.50  --inst_out_proof                        true
% 7.75/1.50  
% 7.75/1.50  ------ Resolution Options
% 7.75/1.50  
% 7.75/1.50  --resolution_flag                       false
% 7.75/1.50  --res_lit_sel                           adaptive
% 7.75/1.50  --res_lit_sel_side                      none
% 7.75/1.50  --res_ordering                          kbo
% 7.75/1.50  --res_to_prop_solver                    active
% 7.75/1.50  --res_prop_simpl_new                    false
% 7.75/1.50  --res_prop_simpl_given                  true
% 7.75/1.50  --res_passive_queue_type                priority_queues
% 7.75/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.75/1.50  --res_passive_queues_freq               [15;5]
% 7.75/1.50  --res_forward_subs                      full
% 7.75/1.50  --res_backward_subs                     full
% 7.75/1.50  --res_forward_subs_resolution           true
% 7.75/1.50  --res_backward_subs_resolution          true
% 7.75/1.50  --res_orphan_elimination                true
% 7.75/1.50  --res_time_limit                        2.
% 7.75/1.50  --res_out_proof                         true
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Options
% 7.75/1.50  
% 7.75/1.50  --superposition_flag                    true
% 7.75/1.50  --sup_passive_queue_type                priority_queues
% 7.75/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.75/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.75/1.50  --demod_completeness_check              fast
% 7.75/1.50  --demod_use_ground                      true
% 7.75/1.50  --sup_to_prop_solver                    passive
% 7.75/1.50  --sup_prop_simpl_new                    true
% 7.75/1.50  --sup_prop_simpl_given                  true
% 7.75/1.50  --sup_fun_splitting                     true
% 7.75/1.50  --sup_smt_interval                      50000
% 7.75/1.50  
% 7.75/1.50  ------ Superposition Simplification Setup
% 7.75/1.50  
% 7.75/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.75/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.75/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.75/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.75/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_immed_triv                        [TrivRules]
% 7.75/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_immed_bw_main                     []
% 7.75/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.75/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.75/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.75/1.50  --sup_input_bw                          []
% 7.75/1.50  
% 7.75/1.50  ------ Combination Options
% 7.75/1.50  
% 7.75/1.50  --comb_res_mult                         3
% 7.75/1.50  --comb_sup_mult                         2
% 7.75/1.50  --comb_inst_mult                        10
% 7.75/1.50  
% 7.75/1.50  ------ Debug Options
% 7.75/1.50  
% 7.75/1.50  --dbg_backtrace                         false
% 7.75/1.50  --dbg_dump_prop_clauses                 false
% 7.75/1.50  --dbg_dump_prop_clauses_file            -
% 7.75/1.50  --dbg_out_stat                          false
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  ------ Proving...
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS status Theorem for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50   Resolution empty clause
% 7.75/1.50  
% 7.75/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  fof(f19,conjecture,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f20,negated_conjecture,(
% 7.75/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(X4,u1_struct_0(X2)) => k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) = k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)))))))),
% 7.75/1.50    inference(negated_conjecture,[],[f19])).
% 7.75/1.50  
% 7.75/1.50  fof(f43,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f20])).
% 7.75/1.50  
% 7.75/1.50  fof(f44,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f43])).
% 7.75/1.50  
% 7.75/1.50  fof(f51,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) => (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,sK4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),sK4) & r1_tarski(sK4,u1_struct_0(X2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f50,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,sK3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(sK3))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f49,plain,(
% 7.75/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,sK2),X4) & r1_tarski(X4,u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(sK2,X1) & ~v2_struct_0(sK2))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f48,plain,(
% 7.75/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(sK1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f47,plain,(
% 7.75/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),X3,X4) != k7_relset_1(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4) & r1_tarski(X4,u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 7.75/1.50    introduced(choice_axiom,[])).
% 7.75/1.50  
% 7.75/1.50  fof(f52,plain,(
% 7.75/1.50    ((((k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) & r1_tarski(sK4,u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 7.75/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f44,f51,f50,f49,f48,f47])).
% 7.75/1.50  
% 7.75/1.50  fof(f90,plain,(
% 7.75/1.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f9,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f27,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f9])).
% 7.75/1.50  
% 7.75/1.50  fof(f62,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f27])).
% 7.75/1.50  
% 7.75/1.50  fof(f11,axiom,(
% 7.75/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f29,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f11])).
% 7.75/1.50  
% 7.75/1.50  fof(f30,plain,(
% 7.75/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(flattening,[],[f29])).
% 7.75/1.50  
% 7.75/1.50  fof(f46,plain,(
% 7.75/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(nnf_transformation,[],[f30])).
% 7.75/1.50  
% 7.75/1.50  fof(f64,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f46])).
% 7.75/1.50  
% 7.75/1.50  fof(f89,plain,(
% 7.75/1.50    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f80,plain,(
% 7.75/1.50    ~v2_struct_0(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f15,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f37,plain,(
% 7.75/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f15])).
% 7.75/1.50  
% 7.75/1.50  fof(f76,plain,(
% 7.75/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f37])).
% 7.75/1.50  
% 7.75/1.50  fof(f1,axiom,(
% 7.75/1.50    v1_xboole_0(k1_xboole_0)),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f53,plain,(
% 7.75/1.50    v1_xboole_0(k1_xboole_0)),
% 7.75/1.50    inference(cnf_transformation,[],[f1])).
% 7.75/1.50  
% 7.75/1.50  fof(f16,axiom,(
% 7.75/1.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f38,plain,(
% 7.75/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f16])).
% 7.75/1.50  
% 7.75/1.50  fof(f39,plain,(
% 7.75/1.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f38])).
% 7.75/1.50  
% 7.75/1.50  fof(f77,plain,(
% 7.75/1.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f39])).
% 7.75/1.50  
% 7.75/1.50  fof(f82,plain,(
% 7.75/1.50    l1_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f18,axiom,(
% 7.75/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f42,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f18])).
% 7.75/1.50  
% 7.75/1.50  fof(f79,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f42])).
% 7.75/1.50  
% 7.75/1.50  fof(f87,plain,(
% 7.75/1.50    m1_pre_topc(sK2,sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f85,plain,(
% 7.75/1.50    l1_pre_topc(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f2,axiom,(
% 7.75/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f45,plain,(
% 7.75/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.75/1.50    inference(nnf_transformation,[],[f2])).
% 7.75/1.50  
% 7.75/1.50  fof(f54,plain,(
% 7.75/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f45])).
% 7.75/1.50  
% 7.75/1.50  fof(f7,axiom,(
% 7.75/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f24,plain,(
% 7.75/1.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.75/1.50    inference(ennf_transformation,[],[f7])).
% 7.75/1.50  
% 7.75/1.50  fof(f25,plain,(
% 7.75/1.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.75/1.50    inference(flattening,[],[f24])).
% 7.75/1.50  
% 7.75/1.50  fof(f60,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f25])).
% 7.75/1.50  
% 7.75/1.50  fof(f3,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f21,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f3])).
% 7.75/1.50  
% 7.75/1.50  fof(f56,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f21])).
% 7.75/1.50  
% 7.75/1.50  fof(f55,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f45])).
% 7.75/1.50  
% 7.75/1.50  fof(f4,axiom,(
% 7.75/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f57,plain,(
% 7.75/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f4])).
% 7.75/1.50  
% 7.75/1.50  fof(f10,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f28,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f10])).
% 7.75/1.50  
% 7.75/1.50  fof(f63,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f28])).
% 7.75/1.50  
% 7.75/1.50  fof(f8,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f26,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.50    inference(ennf_transformation,[],[f8])).
% 7.75/1.50  
% 7.75/1.50  fof(f61,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.50    inference(cnf_transformation,[],[f26])).
% 7.75/1.50  
% 7.75/1.50  fof(f5,axiom,(
% 7.75/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f22,plain,(
% 7.75/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.75/1.50    inference(ennf_transformation,[],[f5])).
% 7.75/1.50  
% 7.75/1.50  fof(f58,plain,(
% 7.75/1.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f22])).
% 7.75/1.50  
% 7.75/1.50  fof(f14,axiom,(
% 7.75/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f35,plain,(
% 7.75/1.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.75/1.50    inference(ennf_transformation,[],[f14])).
% 7.75/1.50  
% 7.75/1.50  fof(f36,plain,(
% 7.75/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.75/1.50    inference(flattening,[],[f35])).
% 7.75/1.50  
% 7.75/1.50  fof(f75,plain,(
% 7.75/1.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f36])).
% 7.75/1.50  
% 7.75/1.50  fof(f13,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f33,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.75/1.50    inference(ennf_transformation,[],[f13])).
% 7.75/1.50  
% 7.75/1.50  fof(f34,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.75/1.50    inference(flattening,[],[f33])).
% 7.75/1.50  
% 7.75/1.50  fof(f72,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f34])).
% 7.75/1.50  
% 7.75/1.50  fof(f88,plain,(
% 7.75/1.50    v1_funct_1(sK3)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f12,axiom,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f31,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.75/1.50    inference(ennf_transformation,[],[f12])).
% 7.75/1.50  
% 7.75/1.50  fof(f32,plain,(
% 7.75/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.75/1.50    inference(flattening,[],[f31])).
% 7.75/1.50  
% 7.75/1.50  fof(f70,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f32])).
% 7.75/1.50  
% 7.75/1.50  fof(f71,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f32])).
% 7.75/1.50  
% 7.75/1.50  fof(f17,axiom,(
% 7.75/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3)))))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f40,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.75/1.50    inference(ennf_transformation,[],[f17])).
% 7.75/1.50  
% 7.75/1.50  fof(f41,plain,(
% 7.75/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.75/1.50    inference(flattening,[],[f40])).
% 7.75/1.50  
% 7.75/1.50  fof(f78,plain,(
% 7.75/1.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) = k2_tmap_1(X0,X1,X2,X3) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f41])).
% 7.75/1.50  
% 7.75/1.50  fof(f83,plain,(
% 7.75/1.50    ~v2_struct_0(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f84,plain,(
% 7.75/1.50    v2_pre_topc(sK1)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f81,plain,(
% 7.75/1.50    v2_pre_topc(sK0)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f93,plain,(
% 7.75/1.50    k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f92,plain,(
% 7.75/1.50    r1_tarski(sK4,u1_struct_0(sK2))),
% 7.75/1.50    inference(cnf_transformation,[],[f52])).
% 7.75/1.50  
% 7.75/1.50  fof(f6,axiom,(
% 7.75/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 7.75/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.75/1.50  
% 7.75/1.50  fof(f23,plain,(
% 7.75/1.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 7.75/1.50    inference(ennf_transformation,[],[f6])).
% 7.75/1.50  
% 7.75/1.50  fof(f59,plain,(
% 7.75/1.50    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 7.75/1.50    inference(cnf_transformation,[],[f23])).
% 7.75/1.50  
% 7.75/1.50  cnf(c_30,negated_conjecture,
% 7.75/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
% 7.75/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2873,plain,
% 7.75/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2881,plain,
% 7.75/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3518,plain,
% 7.75/1.50      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = k1_relat_1(sK3) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2873,c_2881]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_16,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.75/1.50      | k1_xboole_0 = X2 ),
% 7.75/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_31,negated_conjecture,
% 7.75/1.50      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_975,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.75/1.50      | u1_struct_0(sK0) != X2
% 7.75/1.50      | u1_struct_0(sK1) != X1
% 7.75/1.50      | sK3 != X0
% 7.75/1.50      | k1_xboole_0 = X2 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_976,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.50      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = u1_struct_0(sK1)
% 7.75/1.50      | k1_xboole_0 = u1_struct_0(sK0) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_975]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_978,plain,
% 7.75/1.50      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = u1_struct_0(sK1)
% 7.75/1.50      | k1_xboole_0 = u1_struct_0(sK0) ),
% 7.75/1.50      inference(global_propositional_subsumption,[status(thm)],[c_976,c_30]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_40,negated_conjecture,
% 7.75/1.50      ( ~ v2_struct_0(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_23,plain,
% 7.75/1.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_0,plain,
% 7.75/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_24,plain,
% 7.75/1.50      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_513,plain,
% 7.75/1.50      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_531,plain,
% 7.75/1.50      ( v2_struct_0(X0) | ~ l1_pre_topc(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 7.75/1.50      inference(resolution,[status(thm)],[c_23,c_513]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_38,negated_conjecture,
% 7.75/1.50      ( l1_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_669,plain,
% 7.75/1.50      ( v2_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK0 != X0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_531,c_38]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_670,plain,
% 7.75/1.50      ( v2_struct_0(sK0) | u1_struct_0(sK0) != k1_xboole_0 ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_669]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2236,plain,( X0 = X0 ),theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2995,plain,
% 7.75/1.50      ( u1_struct_0(sK0) = u1_struct_0(sK0) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_2236]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2237,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2930,plain,
% 7.75/1.50      ( u1_struct_0(sK0) != X0
% 7.75/1.50      | u1_struct_0(sK0) = k1_xboole_0
% 7.75/1.50      | k1_xboole_0 != X0 ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_2237]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3010,plain,
% 7.75/1.50      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.75/1.50      | u1_struct_0(sK0) = k1_xboole_0
% 7.75/1.50      | k1_xboole_0 != u1_struct_0(sK0) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_2930]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3128,plain,
% 7.75/1.50      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3) = u1_struct_0(sK1) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_978,c_40,c_670,c_2995,c_3010]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3639,plain,
% 7.75/1.50      ( u1_struct_0(sK1) = k1_relat_1(sK3) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3518,c_3128]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_26,plain,
% 7.75/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.75/1.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_33,negated_conjecture,
% 7.75/1.50      ( m1_pre_topc(sK2,sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_582,plain,
% 7.75/1.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | sK2 != X0
% 7.75/1.50      | sK1 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_33]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_583,plain,
% 7.75/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.75/1.50      | ~ l1_pre_topc(sK1) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_582]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_35,negated_conjecture,
% 7.75/1.50      ( l1_pre_topc(sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_585,plain,
% 7.75/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.75/1.50      inference(global_propositional_subsumption,[status(thm)],[c_583,c_35]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2870,plain,
% 7.75/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2887,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3298,plain,
% 7.75/1.50      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2870,c_2887]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3646,plain,
% 7.75/1.50      ( r1_tarski(u1_struct_0(sK2),k1_relat_1(sK3)) = iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3639,c_3298]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_7,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.75/1.50      | ~ v1_relat_1(X1)
% 7.75/1.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.75/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2883,plain,
% 7.75/1.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.75/1.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4210,plain,
% 7.75/1.50      ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2)
% 7.75/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3646,c_2883]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3172,plain,
% 7.75/1.50      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2873,c_2887]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_296,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.75/1.50      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_372,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.75/1.50      inference(bin_hyper_res,[status(thm)],[c_3,c_296]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3248,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 7.75/1.50      | v1_relat_1(X0)
% 7.75/1.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_372]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3742,plain,
% 7.75/1.50      ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 7.75/1.50      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 7.75/1.50      | v1_relat_1(sK3) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_3248]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3743,plain,
% 7.75/1.50      ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_3742]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4,plain,
% 7.75/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4156,plain,
% 7.75/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 7.75/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4157,plain,
% 7.75/1.50      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_4156]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4858,plain,
% 7.75/1.50      ( k1_relat_1(k7_relat_1(sK3,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_4210,c_3172,c_3743,c_4157]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3652,plain,
% 7.75/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3639,c_2873]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_10,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.75/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2880,plain,
% 7.75/1.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3853,plain,
% 7.75/1.50      ( k7_relset_1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3652,c_2880]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2882,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.50      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4303,plain,
% 7.75/1.50      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.75/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3853,c_2882]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5805,plain,
% 7.75/1.50      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,[status(thm)],[c_4303,c_3652]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5811,plain,
% 7.75/1.50      ( r1_tarski(k9_relat_1(sK3,X0),u1_struct_0(sK0)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5805,c_2887]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3648,plain,
% 7.75/1.50      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3639,c_3172]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2871,plain,
% 7.75/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.75/1.50      | v1_relat_1(X1) != iProver_top
% 7.75/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5359,plain,
% 7.75/1.50      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) != iProver_top
% 7.75/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3648,c_2871]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5551,plain,
% 7.75/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_5359,c_3172,c_3743,c_4157]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5,plain,
% 7.75/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2885,plain,
% 7.75/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5558,plain,
% 7.75/1.50      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5551,c_2885]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20,plain,
% 7.75/1.50      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | ~ v1_relat_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2876,plain,
% 7.75/1.50      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.75/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.75/1.50      | v1_funct_1(X0) != iProver_top
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4349,plain,
% 7.75/1.50      ( k7_relset_1(k1_relat_1(X0),X1,X0,X2) = k9_relat_1(X0,X2)
% 7.75/1.50      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.75/1.50      | v1_funct_1(X0) != iProver_top
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2876,c_2880]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_9450,plain,
% 7.75/1.50      ( k7_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),X1,k7_relat_1(sK3,X0),X2) = k9_relat_1(k7_relat_1(sK3,X0),X2)
% 7.75/1.50      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top
% 7.75/1.50      | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top
% 7.75/1.50      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5558,c_4349]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_19,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.75/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2877,plain,
% 7.75/1.50      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.75/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.75/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4017,plain,
% 7.75/1.50      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
% 7.75/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3652,c_2877]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_32,negated_conjecture,
% 7.75/1.50      ( v1_funct_1(sK3) ),
% 7.75/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_49,plain,
% 7.75/1.50      ( v1_funct_1(sK3) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4530,plain,
% 7.75/1.50      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0) ),
% 7.75/1.50      inference(global_propositional_subsumption,[status(thm)],[c_4017,c_49]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_18,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2878,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.50      | v1_funct_1(X0) != iProver_top
% 7.75/1.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3966,plain,
% 7.75/1.50      ( v1_funct_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)) = iProver_top
% 7.75/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_3652,c_2878]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4483,plain,
% 7.75/1.50      ( v1_funct_1(k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,[status(thm)],[c_3966,c_49]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4534,plain,
% 7.75/1.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_4530,c_4483]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2886,plain,
% 7.75/1.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_17,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.50      | ~ v1_funct_1(X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2879,plain,
% 7.75/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.75/1.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.75/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4538,plain,
% 7.75/1.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top
% 7.75/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) != iProver_top
% 7.75/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_4530,c_2879]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5816,plain,
% 7.75/1.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) = iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_4538,c_49,c_3652]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5822,plain,
% 7.75/1.50      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5816,c_2887]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6055,plain,
% 7.75/1.50      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 7.75/1.50      | v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5822,c_2871]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_8290,plain,
% 7.75/1.50      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2886,c_6055]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20758,plain,
% 7.75/1.50      ( k7_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),X1,k7_relat_1(sK3,X0),X2) = k9_relat_1(k7_relat_1(sK3,X0),X2)
% 7.75/1.50      | r1_tarski(k9_relat_1(sK3,X0),X1) != iProver_top ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_9450,c_4534,c_8290]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20765,plain,
% 7.75/1.50      ( k7_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK0),k7_relat_1(sK3,X0),X1) = k9_relat_1(k7_relat_1(sK3,X0),X1) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5811,c_20758]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20772,plain,
% 7.75/1.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),X0) = k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),X0) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_4858,c_20765]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_25,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.75/1.50      | ~ m1_pre_topc(X3,X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.75/1.50      | ~ v2_pre_topc(X2)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | v2_struct_0(X2)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ l1_pre_topc(X2)
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 7.75/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_549,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X2)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | v2_struct_0(X2)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ l1_pre_topc(X2)
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3)
% 7.75/1.50      | sK2 != X3
% 7.75/1.50      | sK1 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_550,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(sK1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | v2_struct_0(sK1)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ l1_pre_topc(sK1)
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_549]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_37,negated_conjecture,
% 7.75/1.50      ( ~ v2_struct_0(sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_36,negated_conjecture,
% 7.75/1.50      ( v2_pre_topc(sK1) ),
% 7.75/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_554,plain,
% 7.75/1.50      ( ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.75/1.50      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_550,c_37,c_36,c_35]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_555,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.75/1.50      | ~ v2_pre_topc(X1)
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2) ),
% 7.75/1.50      inference(renaming,[status(thm)],[c_554]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_39,negated_conjecture,
% 7.75/1.50      ( v2_pre_topc(sK0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_627,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(X1))
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
% 7.75/1.50      | v2_struct_0(X1)
% 7.75/1.50      | ~ l1_pre_topc(X1)
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(X1),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,X1,X0,sK2)
% 7.75/1.50      | sK0 != X1 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_555,c_39]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_628,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.50      | v2_struct_0(sK0)
% 7.75/1.50      | ~ l1_pre_topc(sK0)
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_627]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_632,plain,
% 7.75/1.50      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
% 7.75/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_628,c_40,c_38]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1093,plain,
% 7.75/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.50      | ~ v1_funct_1(X0)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,X0,sK2)
% 7.75/1.50      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 7.75/1.50      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 7.75/1.50      | sK3 != X0 ),
% 7.75/1.50      inference(resolution_lifted,[status(thm)],[c_31,c_632]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1094,plain,
% 7.75/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 7.75/1.50      | ~ v1_funct_1(sK3)
% 7.75/1.50      | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.75/1.50      inference(unflattening,[status(thm)],[c_1093]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_1096,plain,
% 7.75/1.50      ( k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.75/1.50      inference(global_propositional_subsumption,
% 7.75/1.50                [status(thm)],
% 7.75/1.50                [c_1094,c_32,c_30]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3651,plain,
% 7.75/1.50      ( k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = k2_tmap_1(sK1,sK0,sK3,sK2) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3639,c_1096]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4533,plain,
% 7.75/1.50      ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_4530,c_3651]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_27,negated_conjecture,
% 7.75/1.50      ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4) != k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
% 7.75/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3655,plain,
% 7.75/1.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k7_relset_1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK4) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3639,c_27]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4302,plain,
% 7.75/1.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) != k9_relat_1(sK3,sK4) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_3853,c_3655]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_4601,plain,
% 7.75/1.50      ( k7_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_4533,c_4302]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20924,plain,
% 7.75/1.50      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) != k9_relat_1(sK3,sK4) ),
% 7.75/1.50      inference(demodulation,[status(thm)],[c_20772,c_4601]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_28,negated_conjecture,
% 7.75/1.50      ( r1_tarski(sK4,u1_struct_0(sK2)) ),
% 7.75/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2875,plain,
% 7.75/1.50      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_6,plain,
% 7.75/1.50      ( ~ r1_tarski(X0,X1)
% 7.75/1.50      | ~ v1_relat_1(X2)
% 7.75/1.50      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 7.75/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_2884,plain,
% 7.75/1.50      ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 7.75/1.50      | r1_tarski(X2,X1) != iProver_top
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_3961,plain,
% 7.75/1.50      ( k9_relat_1(k7_relat_1(X0,u1_struct_0(sK2)),sK4) = k9_relat_1(X0,sK4)
% 7.75/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_2875,c_2884]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_5557,plain,
% 7.75/1.50      ( k9_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) = k9_relat_1(sK3,sK4) ),
% 7.75/1.50      inference(superposition,[status(thm)],[c_5551,c_3961]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20926,plain,
% 7.75/1.50      ( k9_relat_1(sK3,sK4) != k9_relat_1(sK3,sK4) ),
% 7.75/1.50      inference(light_normalisation,[status(thm)],[c_20924,c_5557]) ).
% 7.75/1.50  
% 7.75/1.50  cnf(c_20927,plain,
% 7.75/1.50      ( $false ),
% 7.75/1.50      inference(equality_resolution_simp,[status(thm)],[c_20926]) ).
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.50  
% 7.75/1.50  ------                               Statistics
% 7.75/1.50  
% 7.75/1.50  ------ General
% 7.75/1.50  
% 7.75/1.50  abstr_ref_over_cycles:                  0
% 7.75/1.50  abstr_ref_under_cycles:                 0
% 7.75/1.50  gc_basic_clause_elim:                   0
% 7.75/1.50  forced_gc_time:                         0
% 7.75/1.50  parsing_time:                           0.016
% 7.75/1.50  unif_index_cands_time:                  0.
% 7.75/1.50  unif_index_add_time:                    0.
% 7.75/1.50  orderings_time:                         0.
% 7.75/1.50  out_proof_time:                         0.014
% 7.75/1.50  total_time:                             0.787
% 7.75/1.50  num_of_symbols:                         59
% 7.75/1.50  num_of_terms:                           23412
% 7.75/1.50  
% 7.75/1.50  ------ Preprocessing
% 7.75/1.50  
% 7.75/1.50  num_of_splits:                          0
% 7.75/1.50  num_of_split_atoms:                     0
% 7.75/1.50  num_of_reused_defs:                     0
% 7.75/1.50  num_eq_ax_congr_red:                    13
% 7.75/1.50  num_of_sem_filtered_clauses:            1
% 7.75/1.50  num_of_subtypes:                        0
% 7.75/1.50  monotx_restored_types:                  0
% 7.75/1.50  sat_num_of_epr_types:                   0
% 7.75/1.50  sat_num_of_non_cyclic_types:            0
% 7.75/1.50  sat_guarded_non_collapsed_types:        0
% 7.75/1.50  num_pure_diseq_elim:                    0
% 7.75/1.50  simp_replaced_by:                       0
% 7.75/1.50  res_preprocessed:                       169
% 7.75/1.50  prep_upred:                             0
% 7.75/1.50  prep_unflattend:                        126
% 7.75/1.50  smt_new_axioms:                         0
% 7.75/1.50  pred_elim_cands:                        4
% 7.75/1.50  pred_elim:                              7
% 7.75/1.50  pred_elim_cl:                           8
% 7.75/1.50  pred_elim_cycles:                       10
% 7.75/1.50  merged_defs:                            8
% 7.75/1.50  merged_defs_ncl:                        0
% 7.75/1.50  bin_hyper_res:                          9
% 7.75/1.50  prep_cycles:                            4
% 7.75/1.50  pred_elim_time:                         0.046
% 7.75/1.50  splitting_time:                         0.
% 7.75/1.50  sem_filter_time:                        0.
% 7.75/1.50  monotx_time:                            0.
% 7.75/1.50  subtype_inf_time:                       0.
% 7.75/1.50  
% 7.75/1.50  ------ Problem properties
% 7.75/1.50  
% 7.75/1.50  clauses:                                32
% 7.75/1.50  conjectures:                            5
% 7.75/1.50  epr:                                    2
% 7.75/1.50  horn:                                   27
% 7.75/1.50  ground:                                 11
% 7.75/1.50  unary:                                  10
% 7.75/1.50  binary:                                 7
% 7.75/1.50  lits:                                   87
% 7.75/1.50  lits_eq:                                30
% 7.75/1.50  fd_pure:                                0
% 7.75/1.50  fd_pseudo:                              0
% 7.75/1.50  fd_cond:                                2
% 7.75/1.50  fd_pseudo_cond:                         0
% 7.75/1.50  ac_symbols:                             0
% 7.75/1.50  
% 7.75/1.50  ------ Propositional Solver
% 7.75/1.50  
% 7.75/1.50  prop_solver_calls:                      36
% 7.75/1.50  prop_fast_solver_calls:                 2530
% 7.75/1.50  smt_solver_calls:                       0
% 7.75/1.50  smt_fast_solver_calls:                  0
% 7.75/1.50  prop_num_of_clauses:                    9714
% 7.75/1.50  prop_preprocess_simplified:             16385
% 7.75/1.50  prop_fo_subsumed:                       98
% 7.75/1.50  prop_solver_time:                       0.
% 7.75/1.50  smt_solver_time:                        0.
% 7.75/1.50  smt_fast_solver_time:                   0.
% 7.75/1.50  prop_fast_solver_time:                  0.
% 7.75/1.50  prop_unsat_core_time:                   0.
% 7.75/1.50  
% 7.75/1.50  ------ QBF
% 7.75/1.50  
% 7.75/1.50  qbf_q_res:                              0
% 7.75/1.50  qbf_num_tautologies:                    0
% 7.75/1.50  qbf_prep_cycles:                        0
% 7.75/1.50  
% 7.75/1.50  ------ BMC1
% 7.75/1.50  
% 7.75/1.50  bmc1_current_bound:                     -1
% 7.75/1.50  bmc1_last_solved_bound:                 -1
% 7.75/1.50  bmc1_unsat_core_size:                   -1
% 7.75/1.50  bmc1_unsat_core_parents_size:           -1
% 7.75/1.50  bmc1_merge_next_fun:                    0
% 7.75/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.75/1.50  
% 7.75/1.50  ------ Instantiation
% 7.75/1.50  
% 7.75/1.50  inst_num_of_clauses:                    2704
% 7.75/1.50  inst_num_in_passive:                    425
% 7.75/1.50  inst_num_in_active:                     1816
% 7.75/1.50  inst_num_in_unprocessed:                464
% 7.75/1.50  inst_num_of_loops:                      1930
% 7.75/1.50  inst_num_of_learning_restarts:          0
% 7.75/1.50  inst_num_moves_active_passive:          107
% 7.75/1.50  inst_lit_activity:                      0
% 7.75/1.50  inst_lit_activity_moves:                0
% 7.75/1.50  inst_num_tautologies:                   0
% 7.75/1.50  inst_num_prop_implied:                  0
% 7.75/1.50  inst_num_existing_simplified:           0
% 7.75/1.50  inst_num_eq_res_simplified:             0
% 7.75/1.50  inst_num_child_elim:                    0
% 7.75/1.50  inst_num_of_dismatching_blockings:      1348
% 7.75/1.50  inst_num_of_non_proper_insts:           4013
% 7.75/1.50  inst_num_of_duplicates:                 0
% 7.75/1.50  inst_inst_num_from_inst_to_res:         0
% 7.75/1.50  inst_dismatching_checking_time:         0.
% 7.75/1.50  
% 7.75/1.50  ------ Resolution
% 7.75/1.50  
% 7.75/1.50  res_num_of_clauses:                     0
% 7.75/1.50  res_num_in_passive:                     0
% 7.75/1.50  res_num_in_active:                      0
% 7.75/1.50  res_num_of_loops:                       173
% 7.75/1.50  res_forward_subset_subsumed:            277
% 7.75/1.50  res_backward_subset_subsumed:           4
% 7.75/1.50  res_forward_subsumed:                   0
% 7.75/1.50  res_backward_subsumed:                  0
% 7.75/1.50  res_forward_subsumption_resolution:     1
% 7.75/1.50  res_backward_subsumption_resolution:    0
% 7.75/1.50  res_clause_to_clause_subsumption:       2636
% 7.75/1.50  res_orphan_elimination:                 0
% 7.75/1.50  res_tautology_del:                      443
% 7.75/1.50  res_num_eq_res_simplified:              0
% 7.75/1.50  res_num_sel_changes:                    0
% 7.75/1.50  res_moves_from_active_to_pass:          0
% 7.75/1.50  
% 7.75/1.50  ------ Superposition
% 7.75/1.50  
% 7.75/1.50  sup_time_total:                         0.
% 7.75/1.50  sup_time_generating:                    0.
% 7.75/1.50  sup_time_sim_full:                      0.
% 7.75/1.50  sup_time_sim_immed:                     0.
% 7.75/1.50  
% 7.75/1.50  sup_num_of_clauses:                     714
% 7.75/1.50  sup_num_in_active:                      303
% 7.75/1.50  sup_num_in_passive:                     411
% 7.75/1.50  sup_num_of_loops:                       384
% 7.75/1.50  sup_fw_superposition:                   696
% 7.75/1.50  sup_bw_superposition:                   419
% 7.75/1.50  sup_immediate_simplified:               229
% 7.75/1.50  sup_given_eliminated:                   1
% 7.75/1.50  comparisons_done:                       0
% 7.75/1.50  comparisons_avoided:                    1
% 7.75/1.50  
% 7.75/1.50  ------ Simplifications
% 7.75/1.50  
% 7.75/1.50  
% 7.75/1.50  sim_fw_subset_subsumed:                 28
% 7.75/1.50  sim_bw_subset_subsumed:                 75
% 7.75/1.50  sim_fw_subsumed:                        82
% 7.75/1.50  sim_bw_subsumed:                        25
% 7.75/1.50  sim_fw_subsumption_res:                 0
% 7.75/1.50  sim_bw_subsumption_res:                 0
% 7.75/1.50  sim_tautology_del:                      4
% 7.75/1.50  sim_eq_tautology_del:                   15
% 7.75/1.50  sim_eq_res_simp:                        0
% 7.75/1.50  sim_fw_demodulated:                     38
% 7.75/1.50  sim_bw_demodulated:                     41
% 7.75/1.50  sim_light_normalised:                   114
% 7.75/1.50  sim_joinable_taut:                      0
% 7.75/1.50  sim_joinable_simp:                      0
% 7.75/1.50  sim_ac_normalised:                      0
% 7.75/1.50  sim_smt_subsumption:                    0
% 7.75/1.50  
%------------------------------------------------------------------------------
