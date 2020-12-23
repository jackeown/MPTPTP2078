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
% DateTime   : Thu Dec  3 12:10:18 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  211 (1461 expanded)
%              Number of clauses        :  135 ( 358 expanded)
%              Number of leaves         :   21 ( 559 expanded)
%              Depth                    :   25
%              Number of atoms          :  805 (12127 expanded)
%              Number of equality atoms :  329 (1891 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5))
            & v1_partfun1(sK4,X0)
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                  & v1_partfun1(X4,X0)
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5))
                & v1_partfun1(X4,X0)
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5))
                    & v1_partfun1(X4,X0)
                    & m1_subset_1(X5,sK1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
            & v1_funct_2(X3,sK1,X0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f47,f46,f45,f44,f43])).

fof(f77,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f37])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1280,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1277,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1288,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1876,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1277,c_1288])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1279,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2377,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1291])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1717,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_1718,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1717])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1735,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1736,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1735])).

cnf(c_2654,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_37,c_1718,c_1736])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_465,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_466,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_466])).

cnf(c_531,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_766,plain,
    ( ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k1_relat_1(sK4) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_531])).

cnf(c_1266,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_2659,plain,
    ( k1_relat_1(sK4) = sK0
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_1266])).

cnf(c_798,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_765,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_531])).

cnf(c_1267,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_2092,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1267])).

cnf(c_3710,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2659,c_37,c_798,c_1718,c_1736,c_2092])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1289,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2367,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1279,c_1289])).

cnf(c_3713,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_3710,c_2367])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k7_partfun1(X3,X4,k1_funct_1(X0,X5))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1281,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k7_partfun1(X2,X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3905,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3713,c_1281])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_31,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6941,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3905,c_31,c_36,c_37])).

cnf(c_6942,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6941])).

cnf(c_6954,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1876,c_6942])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1720,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_1721,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1720])).

cnf(c_1738,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1739,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1738])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_321,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_1272,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_3828,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1272])).

cnf(c_8356,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6954,c_33,c_34,c_35,c_1721,c_1739,c_3828])).

cnf(c_8366,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1280,c_8356])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1286,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1283,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3047,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1283])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1284,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1285,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9542,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3047,c_1284,c_1285])).

cnf(c_9549,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_9542])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9758,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9549,c_32,c_33,c_34])).

cnf(c_9770,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_9758])).

cnf(c_9853,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9770,c_36])).

cnf(c_9854,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9853])).

cnf(c_9862,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1280,c_9854])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1282,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3046,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1282])).

cnf(c_8411,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3046,c_1284,c_1285])).

cnf(c_8418,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_8411])).

cnf(c_8675,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8418,c_32,c_33,c_34])).

cnf(c_8676,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8675])).

cnf(c_8688,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_8676])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_479,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_30])).

cnf(c_482,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_481])).

cnf(c_1269,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_1952,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1269])).

cnf(c_8801,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8688,c_36,c_1952])).

cnf(c_8810,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1280,c_8801])).

cnf(c_9881,plain,
    ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(demodulation,[status(thm)],[c_9862,c_8810])).

cnf(c_2514,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1283])).

cnf(c_2706,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2514,c_32,c_33,c_34])).

cnf(c_2715,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1280,c_2706])).

cnf(c_21,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2761,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2715,c_21])).

cnf(c_8829,plain,
    ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_8810,c_2761])).

cnf(c_9946,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_9881,c_8829])).

cnf(c_9953,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8366,c_9946])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1287,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2762,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2715,c_1287])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3734,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2762,c_32,c_33,c_34,c_35,c_38])).

cnf(c_2854,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1282])).

cnf(c_9,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_492,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_493,plain,
    ( v1_funct_2(sK4,sK0,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_funct_1(sK4) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_497,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | v1_funct_2(sK4,sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_25])).

cnf(c_498,plain,
    ( v1_funct_2(sK4,sK0,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    inference(renaming,[status(thm)],[c_497])).

cnf(c_1526,plain,
    ( v1_funct_2(sK4,sK0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_1527,plain,
    ( v1_funct_2(sK4,sK0,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1526])).

cnf(c_3146,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2854,c_31,c_36,c_37,c_1527,c_1952])).

cnf(c_3147,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3146])).

cnf(c_3739,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3734,c_3147])).

cnf(c_2513,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1283])).

cnf(c_2693,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2513,c_31,c_36,c_37,c_1527])).

cnf(c_3740,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3734,c_2693])).

cnf(c_3743,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_3739,c_3740])).

cnf(c_10045,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9953,c_3743])).

cnf(c_1274,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10104,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10045,c_1274])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10104,c_94])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.87/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.00  
% 3.87/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/1.00  
% 3.87/1.00  ------  iProver source info
% 3.87/1.00  
% 3.87/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.87/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/1.00  git: non_committed_changes: false
% 3.87/1.00  git: last_make_outside_of_git: false
% 3.87/1.00  
% 3.87/1.00  ------ 
% 3.87/1.00  
% 3.87/1.00  ------ Input Options
% 3.87/1.00  
% 3.87/1.00  --out_options                           all
% 3.87/1.00  --tptp_safe_out                         true
% 3.87/1.00  --problem_path                          ""
% 3.87/1.00  --include_path                          ""
% 3.87/1.00  --clausifier                            res/vclausify_rel
% 3.87/1.00  --clausifier_options                    --mode clausify
% 3.87/1.00  --stdin                                 false
% 3.87/1.00  --stats_out                             all
% 3.87/1.00  
% 3.87/1.00  ------ General Options
% 3.87/1.00  
% 3.87/1.00  --fof                                   false
% 3.87/1.00  --time_out_real                         305.
% 3.87/1.00  --time_out_virtual                      -1.
% 3.87/1.00  --symbol_type_check                     false
% 3.87/1.00  --clausify_out                          false
% 3.87/1.00  --sig_cnt_out                           false
% 3.87/1.00  --trig_cnt_out                          false
% 3.87/1.00  --trig_cnt_out_tolerance                1.
% 3.87/1.00  --trig_cnt_out_sk_spl                   false
% 3.87/1.00  --abstr_cl_out                          false
% 3.87/1.00  
% 3.87/1.00  ------ Global Options
% 3.87/1.00  
% 3.87/1.00  --schedule                              default
% 3.87/1.00  --add_important_lit                     false
% 3.87/1.00  --prop_solver_per_cl                    1000
% 3.87/1.00  --min_unsat_core                        false
% 3.87/1.00  --soft_assumptions                      false
% 3.87/1.00  --soft_lemma_size                       3
% 3.87/1.00  --prop_impl_unit_size                   0
% 3.87/1.00  --prop_impl_unit                        []
% 3.87/1.00  --share_sel_clauses                     true
% 3.87/1.00  --reset_solvers                         false
% 3.87/1.00  --bc_imp_inh                            [conj_cone]
% 3.87/1.00  --conj_cone_tolerance                   3.
% 3.87/1.00  --extra_neg_conj                        none
% 3.87/1.00  --large_theory_mode                     true
% 3.87/1.00  --prolific_symb_bound                   200
% 3.87/1.00  --lt_threshold                          2000
% 3.87/1.00  --clause_weak_htbl                      true
% 3.87/1.00  --gc_record_bc_elim                     false
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing Options
% 3.87/1.00  
% 3.87/1.00  --preprocessing_flag                    true
% 3.87/1.00  --time_out_prep_mult                    0.1
% 3.87/1.00  --splitting_mode                        input
% 3.87/1.00  --splitting_grd                         true
% 3.87/1.00  --splitting_cvd                         false
% 3.87/1.00  --splitting_cvd_svl                     false
% 3.87/1.00  --splitting_nvd                         32
% 3.87/1.00  --sub_typing                            true
% 3.87/1.00  --prep_gs_sim                           true
% 3.87/1.00  --prep_unflatten                        true
% 3.87/1.00  --prep_res_sim                          true
% 3.87/1.00  --prep_upred                            true
% 3.87/1.00  --prep_sem_filter                       exhaustive
% 3.87/1.00  --prep_sem_filter_out                   false
% 3.87/1.00  --pred_elim                             true
% 3.87/1.00  --res_sim_input                         true
% 3.87/1.00  --eq_ax_congr_red                       true
% 3.87/1.00  --pure_diseq_elim                       true
% 3.87/1.00  --brand_transform                       false
% 3.87/1.00  --non_eq_to_eq                          false
% 3.87/1.00  --prep_def_merge                        true
% 3.87/1.00  --prep_def_merge_prop_impl              false
% 3.87/1.00  --prep_def_merge_mbd                    true
% 3.87/1.00  --prep_def_merge_tr_red                 false
% 3.87/1.00  --prep_def_merge_tr_cl                  false
% 3.87/1.00  --smt_preprocessing                     true
% 3.87/1.00  --smt_ac_axioms                         fast
% 3.87/1.00  --preprocessed_out                      false
% 3.87/1.00  --preprocessed_stats                    false
% 3.87/1.00  
% 3.87/1.00  ------ Abstraction refinement Options
% 3.87/1.00  
% 3.87/1.00  --abstr_ref                             []
% 3.87/1.00  --abstr_ref_prep                        false
% 3.87/1.00  --abstr_ref_until_sat                   false
% 3.87/1.00  --abstr_ref_sig_restrict                funpre
% 3.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/1.00  --abstr_ref_under                       []
% 3.87/1.00  
% 3.87/1.00  ------ SAT Options
% 3.87/1.00  
% 3.87/1.00  --sat_mode                              false
% 3.87/1.00  --sat_fm_restart_options                ""
% 3.87/1.00  --sat_gr_def                            false
% 3.87/1.00  --sat_epr_types                         true
% 3.87/1.00  --sat_non_cyclic_types                  false
% 3.87/1.00  --sat_finite_models                     false
% 3.87/1.00  --sat_fm_lemmas                         false
% 3.87/1.00  --sat_fm_prep                           false
% 3.87/1.00  --sat_fm_uc_incr                        true
% 3.87/1.00  --sat_out_model                         small
% 3.87/1.00  --sat_out_clauses                       false
% 3.87/1.00  
% 3.87/1.00  ------ QBF Options
% 3.87/1.00  
% 3.87/1.00  --qbf_mode                              false
% 3.87/1.00  --qbf_elim_univ                         false
% 3.87/1.00  --qbf_dom_inst                          none
% 3.87/1.00  --qbf_dom_pre_inst                      false
% 3.87/1.00  --qbf_sk_in                             false
% 3.87/1.00  --qbf_pred_elim                         true
% 3.87/1.00  --qbf_split                             512
% 3.87/1.00  
% 3.87/1.00  ------ BMC1 Options
% 3.87/1.00  
% 3.87/1.00  --bmc1_incremental                      false
% 3.87/1.00  --bmc1_axioms                           reachable_all
% 3.87/1.00  --bmc1_min_bound                        0
% 3.87/1.00  --bmc1_max_bound                        -1
% 3.87/1.00  --bmc1_max_bound_default                -1
% 3.87/1.00  --bmc1_symbol_reachability              true
% 3.87/1.00  --bmc1_property_lemmas                  false
% 3.87/1.00  --bmc1_k_induction                      false
% 3.87/1.00  --bmc1_non_equiv_states                 false
% 3.87/1.00  --bmc1_deadlock                         false
% 3.87/1.00  --bmc1_ucm                              false
% 3.87/1.00  --bmc1_add_unsat_core                   none
% 3.87/1.00  --bmc1_unsat_core_children              false
% 3.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/1.00  --bmc1_out_stat                         full
% 3.87/1.00  --bmc1_ground_init                      false
% 3.87/1.00  --bmc1_pre_inst_next_state              false
% 3.87/1.00  --bmc1_pre_inst_state                   false
% 3.87/1.00  --bmc1_pre_inst_reach_state             false
% 3.87/1.00  --bmc1_out_unsat_core                   false
% 3.87/1.00  --bmc1_aig_witness_out                  false
% 3.87/1.00  --bmc1_verbose                          false
% 3.87/1.00  --bmc1_dump_clauses_tptp                false
% 3.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.87/1.00  --bmc1_dump_file                        -
% 3.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.87/1.00  --bmc1_ucm_extend_mode                  1
% 3.87/1.00  --bmc1_ucm_init_mode                    2
% 3.87/1.00  --bmc1_ucm_cone_mode                    none
% 3.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.87/1.00  --bmc1_ucm_relax_model                  4
% 3.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/1.00  --bmc1_ucm_layered_model                none
% 3.87/1.00  --bmc1_ucm_max_lemma_size               10
% 3.87/1.00  
% 3.87/1.00  ------ AIG Options
% 3.87/1.00  
% 3.87/1.00  --aig_mode                              false
% 3.87/1.00  
% 3.87/1.00  ------ Instantiation Options
% 3.87/1.00  
% 3.87/1.00  --instantiation_flag                    true
% 3.87/1.00  --inst_sos_flag                         false
% 3.87/1.00  --inst_sos_phase                        true
% 3.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel_side                     num_symb
% 3.87/1.00  --inst_solver_per_active                1400
% 3.87/1.00  --inst_solver_calls_frac                1.
% 3.87/1.00  --inst_passive_queue_type               priority_queues
% 3.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/1.00  --inst_passive_queues_freq              [25;2]
% 3.87/1.00  --inst_dismatching                      true
% 3.87/1.00  --inst_eager_unprocessed_to_passive     true
% 3.87/1.00  --inst_prop_sim_given                   true
% 3.87/1.00  --inst_prop_sim_new                     false
% 3.87/1.00  --inst_subs_new                         false
% 3.87/1.00  --inst_eq_res_simp                      false
% 3.87/1.00  --inst_subs_given                       false
% 3.87/1.00  --inst_orphan_elimination               true
% 3.87/1.00  --inst_learning_loop_flag               true
% 3.87/1.00  --inst_learning_start                   3000
% 3.87/1.00  --inst_learning_factor                  2
% 3.87/1.00  --inst_start_prop_sim_after_learn       3
% 3.87/1.00  --inst_sel_renew                        solver
% 3.87/1.00  --inst_lit_activity_flag                true
% 3.87/1.00  --inst_restr_to_given                   false
% 3.87/1.00  --inst_activity_threshold               500
% 3.87/1.00  --inst_out_proof                        true
% 3.87/1.00  
% 3.87/1.00  ------ Resolution Options
% 3.87/1.00  
% 3.87/1.00  --resolution_flag                       true
% 3.87/1.00  --res_lit_sel                           adaptive
% 3.87/1.00  --res_lit_sel_side                      none
% 3.87/1.00  --res_ordering                          kbo
% 3.87/1.00  --res_to_prop_solver                    active
% 3.87/1.00  --res_prop_simpl_new                    false
% 3.87/1.00  --res_prop_simpl_given                  true
% 3.87/1.00  --res_passive_queue_type                priority_queues
% 3.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/1.00  --res_passive_queues_freq               [15;5]
% 3.87/1.00  --res_forward_subs                      full
% 3.87/1.00  --res_backward_subs                     full
% 3.87/1.00  --res_forward_subs_resolution           true
% 3.87/1.00  --res_backward_subs_resolution          true
% 3.87/1.00  --res_orphan_elimination                true
% 3.87/1.00  --res_time_limit                        2.
% 3.87/1.00  --res_out_proof                         true
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Options
% 3.87/1.00  
% 3.87/1.00  --superposition_flag                    true
% 3.87/1.00  --sup_passive_queue_type                priority_queues
% 3.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.87/1.00  --demod_completeness_check              fast
% 3.87/1.00  --demod_use_ground                      true
% 3.87/1.00  --sup_to_prop_solver                    passive
% 3.87/1.00  --sup_prop_simpl_new                    true
% 3.87/1.00  --sup_prop_simpl_given                  true
% 3.87/1.00  --sup_fun_splitting                     false
% 3.87/1.00  --sup_smt_interval                      50000
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Simplification Setup
% 3.87/1.00  
% 3.87/1.00  --sup_indices_passive                   []
% 3.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_full_bw                           [BwDemod]
% 3.87/1.00  --sup_immed_triv                        [TrivRules]
% 3.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_immed_bw_main                     []
% 3.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  
% 3.87/1.00  ------ Combination Options
% 3.87/1.00  
% 3.87/1.00  --comb_res_mult                         3
% 3.87/1.00  --comb_sup_mult                         2
% 3.87/1.00  --comb_inst_mult                        10
% 3.87/1.00  
% 3.87/1.00  ------ Debug Options
% 3.87/1.00  
% 3.87/1.00  --dbg_backtrace                         false
% 3.87/1.00  --dbg_dump_prop_clauses                 false
% 3.87/1.00  --dbg_dump_prop_clauses_file            -
% 3.87/1.00  --dbg_out_stat                          false
% 3.87/1.00  ------ Parsing...
% 3.87/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/1.00  ------ Proving...
% 3.87/1.00  ------ Problem Properties 
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  clauses                                 28
% 3.87/1.00  conjectures                             9
% 3.87/1.00  EPR                                     7
% 3.87/1.00  Horn                                    23
% 3.87/1.00  unary                                   11
% 3.87/1.00  binary                                  5
% 3.87/1.00  lits                                    85
% 3.87/1.00  lits eq                                 8
% 3.87/1.00  fd_pure                                 0
% 3.87/1.00  fd_pseudo                               0
% 3.87/1.00  fd_cond                                 1
% 3.87/1.00  fd_pseudo_cond                          0
% 3.87/1.00  AC symbols                              0
% 3.87/1.00  
% 3.87/1.00  ------ Schedule dynamic 5 is on 
% 3.87/1.00  
% 3.87/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  ------ 
% 3.87/1.00  Current options:
% 3.87/1.00  ------ 
% 3.87/1.00  
% 3.87/1.00  ------ Input Options
% 3.87/1.00  
% 3.87/1.00  --out_options                           all
% 3.87/1.00  --tptp_safe_out                         true
% 3.87/1.00  --problem_path                          ""
% 3.87/1.00  --include_path                          ""
% 3.87/1.00  --clausifier                            res/vclausify_rel
% 3.87/1.00  --clausifier_options                    --mode clausify
% 3.87/1.00  --stdin                                 false
% 3.87/1.00  --stats_out                             all
% 3.87/1.00  
% 3.87/1.00  ------ General Options
% 3.87/1.00  
% 3.87/1.00  --fof                                   false
% 3.87/1.00  --time_out_real                         305.
% 3.87/1.00  --time_out_virtual                      -1.
% 3.87/1.00  --symbol_type_check                     false
% 3.87/1.00  --clausify_out                          false
% 3.87/1.00  --sig_cnt_out                           false
% 3.87/1.00  --trig_cnt_out                          false
% 3.87/1.00  --trig_cnt_out_tolerance                1.
% 3.87/1.00  --trig_cnt_out_sk_spl                   false
% 3.87/1.00  --abstr_cl_out                          false
% 3.87/1.00  
% 3.87/1.00  ------ Global Options
% 3.87/1.00  
% 3.87/1.00  --schedule                              default
% 3.87/1.00  --add_important_lit                     false
% 3.87/1.00  --prop_solver_per_cl                    1000
% 3.87/1.00  --min_unsat_core                        false
% 3.87/1.00  --soft_assumptions                      false
% 3.87/1.00  --soft_lemma_size                       3
% 3.87/1.00  --prop_impl_unit_size                   0
% 3.87/1.00  --prop_impl_unit                        []
% 3.87/1.00  --share_sel_clauses                     true
% 3.87/1.00  --reset_solvers                         false
% 3.87/1.00  --bc_imp_inh                            [conj_cone]
% 3.87/1.00  --conj_cone_tolerance                   3.
% 3.87/1.00  --extra_neg_conj                        none
% 3.87/1.00  --large_theory_mode                     true
% 3.87/1.00  --prolific_symb_bound                   200
% 3.87/1.00  --lt_threshold                          2000
% 3.87/1.00  --clause_weak_htbl                      true
% 3.87/1.00  --gc_record_bc_elim                     false
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing Options
% 3.87/1.00  
% 3.87/1.00  --preprocessing_flag                    true
% 3.87/1.00  --time_out_prep_mult                    0.1
% 3.87/1.00  --splitting_mode                        input
% 3.87/1.00  --splitting_grd                         true
% 3.87/1.00  --splitting_cvd                         false
% 3.87/1.00  --splitting_cvd_svl                     false
% 3.87/1.00  --splitting_nvd                         32
% 3.87/1.00  --sub_typing                            true
% 3.87/1.00  --prep_gs_sim                           true
% 3.87/1.00  --prep_unflatten                        true
% 3.87/1.00  --prep_res_sim                          true
% 3.87/1.00  --prep_upred                            true
% 3.87/1.00  --prep_sem_filter                       exhaustive
% 3.87/1.00  --prep_sem_filter_out                   false
% 3.87/1.00  --pred_elim                             true
% 3.87/1.00  --res_sim_input                         true
% 3.87/1.00  --eq_ax_congr_red                       true
% 3.87/1.00  --pure_diseq_elim                       true
% 3.87/1.00  --brand_transform                       false
% 3.87/1.00  --non_eq_to_eq                          false
% 3.87/1.00  --prep_def_merge                        true
% 3.87/1.00  --prep_def_merge_prop_impl              false
% 3.87/1.00  --prep_def_merge_mbd                    true
% 3.87/1.00  --prep_def_merge_tr_red                 false
% 3.87/1.00  --prep_def_merge_tr_cl                  false
% 3.87/1.00  --smt_preprocessing                     true
% 3.87/1.00  --smt_ac_axioms                         fast
% 3.87/1.00  --preprocessed_out                      false
% 3.87/1.00  --preprocessed_stats                    false
% 3.87/1.00  
% 3.87/1.00  ------ Abstraction refinement Options
% 3.87/1.00  
% 3.87/1.00  --abstr_ref                             []
% 3.87/1.00  --abstr_ref_prep                        false
% 3.87/1.00  --abstr_ref_until_sat                   false
% 3.87/1.00  --abstr_ref_sig_restrict                funpre
% 3.87/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.87/1.00  --abstr_ref_under                       []
% 3.87/1.00  
% 3.87/1.00  ------ SAT Options
% 3.87/1.00  
% 3.87/1.00  --sat_mode                              false
% 3.87/1.00  --sat_fm_restart_options                ""
% 3.87/1.00  --sat_gr_def                            false
% 3.87/1.00  --sat_epr_types                         true
% 3.87/1.00  --sat_non_cyclic_types                  false
% 3.87/1.00  --sat_finite_models                     false
% 3.87/1.00  --sat_fm_lemmas                         false
% 3.87/1.00  --sat_fm_prep                           false
% 3.87/1.00  --sat_fm_uc_incr                        true
% 3.87/1.00  --sat_out_model                         small
% 3.87/1.00  --sat_out_clauses                       false
% 3.87/1.00  
% 3.87/1.00  ------ QBF Options
% 3.87/1.00  
% 3.87/1.00  --qbf_mode                              false
% 3.87/1.00  --qbf_elim_univ                         false
% 3.87/1.00  --qbf_dom_inst                          none
% 3.87/1.00  --qbf_dom_pre_inst                      false
% 3.87/1.00  --qbf_sk_in                             false
% 3.87/1.00  --qbf_pred_elim                         true
% 3.87/1.00  --qbf_split                             512
% 3.87/1.00  
% 3.87/1.00  ------ BMC1 Options
% 3.87/1.00  
% 3.87/1.00  --bmc1_incremental                      false
% 3.87/1.00  --bmc1_axioms                           reachable_all
% 3.87/1.00  --bmc1_min_bound                        0
% 3.87/1.00  --bmc1_max_bound                        -1
% 3.87/1.00  --bmc1_max_bound_default                -1
% 3.87/1.00  --bmc1_symbol_reachability              true
% 3.87/1.00  --bmc1_property_lemmas                  false
% 3.87/1.00  --bmc1_k_induction                      false
% 3.87/1.00  --bmc1_non_equiv_states                 false
% 3.87/1.00  --bmc1_deadlock                         false
% 3.87/1.00  --bmc1_ucm                              false
% 3.87/1.00  --bmc1_add_unsat_core                   none
% 3.87/1.00  --bmc1_unsat_core_children              false
% 3.87/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.87/1.00  --bmc1_out_stat                         full
% 3.87/1.00  --bmc1_ground_init                      false
% 3.87/1.00  --bmc1_pre_inst_next_state              false
% 3.87/1.00  --bmc1_pre_inst_state                   false
% 3.87/1.00  --bmc1_pre_inst_reach_state             false
% 3.87/1.00  --bmc1_out_unsat_core                   false
% 3.87/1.00  --bmc1_aig_witness_out                  false
% 3.87/1.00  --bmc1_verbose                          false
% 3.87/1.00  --bmc1_dump_clauses_tptp                false
% 3.87/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.87/1.00  --bmc1_dump_file                        -
% 3.87/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.87/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.87/1.00  --bmc1_ucm_extend_mode                  1
% 3.87/1.00  --bmc1_ucm_init_mode                    2
% 3.87/1.00  --bmc1_ucm_cone_mode                    none
% 3.87/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.87/1.00  --bmc1_ucm_relax_model                  4
% 3.87/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.87/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.87/1.00  --bmc1_ucm_layered_model                none
% 3.87/1.00  --bmc1_ucm_max_lemma_size               10
% 3.87/1.00  
% 3.87/1.00  ------ AIG Options
% 3.87/1.00  
% 3.87/1.00  --aig_mode                              false
% 3.87/1.00  
% 3.87/1.00  ------ Instantiation Options
% 3.87/1.00  
% 3.87/1.00  --instantiation_flag                    true
% 3.87/1.00  --inst_sos_flag                         false
% 3.87/1.00  --inst_sos_phase                        true
% 3.87/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.87/1.00  --inst_lit_sel_side                     none
% 3.87/1.00  --inst_solver_per_active                1400
% 3.87/1.00  --inst_solver_calls_frac                1.
% 3.87/1.00  --inst_passive_queue_type               priority_queues
% 3.87/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.87/1.00  --inst_passive_queues_freq              [25;2]
% 3.87/1.00  --inst_dismatching                      true
% 3.87/1.00  --inst_eager_unprocessed_to_passive     true
% 3.87/1.00  --inst_prop_sim_given                   true
% 3.87/1.00  --inst_prop_sim_new                     false
% 3.87/1.00  --inst_subs_new                         false
% 3.87/1.00  --inst_eq_res_simp                      false
% 3.87/1.00  --inst_subs_given                       false
% 3.87/1.00  --inst_orphan_elimination               true
% 3.87/1.00  --inst_learning_loop_flag               true
% 3.87/1.00  --inst_learning_start                   3000
% 3.87/1.00  --inst_learning_factor                  2
% 3.87/1.00  --inst_start_prop_sim_after_learn       3
% 3.87/1.00  --inst_sel_renew                        solver
% 3.87/1.00  --inst_lit_activity_flag                true
% 3.87/1.00  --inst_restr_to_given                   false
% 3.87/1.00  --inst_activity_threshold               500
% 3.87/1.00  --inst_out_proof                        true
% 3.87/1.00  
% 3.87/1.00  ------ Resolution Options
% 3.87/1.00  
% 3.87/1.00  --resolution_flag                       false
% 3.87/1.00  --res_lit_sel                           adaptive
% 3.87/1.00  --res_lit_sel_side                      none
% 3.87/1.00  --res_ordering                          kbo
% 3.87/1.00  --res_to_prop_solver                    active
% 3.87/1.00  --res_prop_simpl_new                    false
% 3.87/1.00  --res_prop_simpl_given                  true
% 3.87/1.00  --res_passive_queue_type                priority_queues
% 3.87/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.87/1.00  --res_passive_queues_freq               [15;5]
% 3.87/1.00  --res_forward_subs                      full
% 3.87/1.00  --res_backward_subs                     full
% 3.87/1.00  --res_forward_subs_resolution           true
% 3.87/1.00  --res_backward_subs_resolution          true
% 3.87/1.00  --res_orphan_elimination                true
% 3.87/1.00  --res_time_limit                        2.
% 3.87/1.00  --res_out_proof                         true
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Options
% 3.87/1.00  
% 3.87/1.00  --superposition_flag                    true
% 3.87/1.00  --sup_passive_queue_type                priority_queues
% 3.87/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.87/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.87/1.00  --demod_completeness_check              fast
% 3.87/1.00  --demod_use_ground                      true
% 3.87/1.00  --sup_to_prop_solver                    passive
% 3.87/1.00  --sup_prop_simpl_new                    true
% 3.87/1.00  --sup_prop_simpl_given                  true
% 3.87/1.00  --sup_fun_splitting                     false
% 3.87/1.00  --sup_smt_interval                      50000
% 3.87/1.00  
% 3.87/1.00  ------ Superposition Simplification Setup
% 3.87/1.00  
% 3.87/1.00  --sup_indices_passive                   []
% 3.87/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.87/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.87/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_full_bw                           [BwDemod]
% 3.87/1.00  --sup_immed_triv                        [TrivRules]
% 3.87/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.87/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_immed_bw_main                     []
% 3.87/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.87/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.87/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.87/1.00  
% 3.87/1.00  ------ Combination Options
% 3.87/1.00  
% 3.87/1.00  --comb_res_mult                         3
% 3.87/1.00  --comb_sup_mult                         2
% 3.87/1.00  --comb_inst_mult                        10
% 3.87/1.00  
% 3.87/1.00  ------ Debug Options
% 3.87/1.00  
% 3.87/1.00  --dbg_backtrace                         false
% 3.87/1.00  --dbg_dump_prop_clauses                 false
% 3.87/1.00  --dbg_dump_prop_clauses_file            -
% 3.87/1.00  --dbg_out_stat                          false
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  ------ Proving...
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  % SZS status Theorem for theBenchmark.p
% 3.87/1.00  
% 3.87/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/1.00  
% 3.87/1.00  fof(f16,conjecture,(
% 3.87/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f17,negated_conjecture,(
% 3.87/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.87/1.00    inference(negated_conjecture,[],[f16])).
% 3.87/1.00  
% 3.87/1.00  fof(f39,plain,(
% 3.87/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f17])).
% 3.87/1.00  
% 3.87/1.00  fof(f40,plain,(
% 3.87/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.87/1.00    inference(flattening,[],[f39])).
% 3.87/1.00  
% 3.87/1.00  fof(f47,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f46,plain,(
% 3.87/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f45,plain,(
% 3.87/1.00    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f44,plain,(
% 3.87/1.00    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f43,plain,(
% 3.87/1.00    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.87/1.00    introduced(choice_axiom,[])).
% 3.87/1.00  
% 3.87/1.00  fof(f48,plain,(
% 3.87/1.00    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.87/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f47,f46,f45,f44,f43])).
% 3.87/1.00  
% 3.87/1.00  fof(f77,plain,(
% 3.87/1.00    m1_subset_1(sK5,sK1)),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f74,plain,(
% 3.87/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f7,axiom,(
% 3.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f22,plain,(
% 3.87/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/1.00    inference(ennf_transformation,[],[f7])).
% 3.87/1.00  
% 3.87/1.00  fof(f57,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/1.00    inference(cnf_transformation,[],[f22])).
% 3.87/1.00  
% 3.87/1.00  fof(f76,plain,(
% 3.87/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f2,axiom,(
% 3.87/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f18,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f2])).
% 3.87/1.00  
% 3.87/1.00  fof(f50,plain,(
% 3.87/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f18])).
% 3.87/1.00  
% 3.87/1.00  fof(f4,axiom,(
% 3.87/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f53,plain,(
% 3.87/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.87/1.00    inference(cnf_transformation,[],[f4])).
% 3.87/1.00  
% 3.87/1.00  fof(f5,axiom,(
% 3.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f20,plain,(
% 3.87/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/1.00    inference(ennf_transformation,[],[f5])).
% 3.87/1.00  
% 3.87/1.00  fof(f54,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/1.00    inference(cnf_transformation,[],[f20])).
% 3.87/1.00  
% 3.87/1.00  fof(f10,axiom,(
% 3.87/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f27,plain,(
% 3.87/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.87/1.00    inference(ennf_transformation,[],[f10])).
% 3.87/1.00  
% 3.87/1.00  fof(f28,plain,(
% 3.87/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.87/1.00    inference(flattening,[],[f27])).
% 3.87/1.00  
% 3.87/1.00  fof(f42,plain,(
% 3.87/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.87/1.00    inference(nnf_transformation,[],[f28])).
% 3.87/1.00  
% 3.87/1.00  fof(f61,plain,(
% 3.87/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f42])).
% 3.87/1.00  
% 3.87/1.00  fof(f78,plain,(
% 3.87/1.00    v1_partfun1(sK4,sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f6,axiom,(
% 3.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f21,plain,(
% 3.87/1.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/1.00    inference(ennf_transformation,[],[f6])).
% 3.87/1.00  
% 3.87/1.00  fof(f56,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/1.00    inference(cnf_transformation,[],[f21])).
% 3.87/1.00  
% 3.87/1.00  fof(f15,axiom,(
% 3.87/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f37,plain,(
% 3.87/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.87/1.00    inference(ennf_transformation,[],[f15])).
% 3.87/1.00  
% 3.87/1.00  fof(f38,plain,(
% 3.87/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.87/1.00    inference(flattening,[],[f37])).
% 3.87/1.00  
% 3.87/1.00  fof(f69,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f38])).
% 3.87/1.00  
% 3.87/1.00  fof(f70,plain,(
% 3.87/1.00    ~v1_xboole_0(sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f75,plain,(
% 3.87/1.00    v1_funct_1(sK4)),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f72,plain,(
% 3.87/1.00    v1_funct_1(sK3)),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f73,plain,(
% 3.87/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f55,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/1.00    inference(cnf_transformation,[],[f20])).
% 3.87/1.00  
% 3.87/1.00  fof(f3,axiom,(
% 3.87/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f19,plain,(
% 3.87/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.87/1.00    inference(ennf_transformation,[],[f3])).
% 3.87/1.00  
% 3.87/1.00  fof(f41,plain,(
% 3.87/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.87/1.00    inference(nnf_transformation,[],[f19])).
% 3.87/1.00  
% 3.87/1.00  fof(f51,plain,(
% 3.87/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f41])).
% 3.87/1.00  
% 3.87/1.00  fof(f12,axiom,(
% 3.87/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f31,plain,(
% 3.87/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.87/1.00    inference(ennf_transformation,[],[f12])).
% 3.87/1.00  
% 3.87/1.00  fof(f32,plain,(
% 3.87/1.00    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.87/1.00    inference(flattening,[],[f31])).
% 3.87/1.00  
% 3.87/1.00  fof(f66,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f32])).
% 3.87/1.00  
% 3.87/1.00  fof(f13,axiom,(
% 3.87/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f33,plain,(
% 3.87/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f13])).
% 3.87/1.00  
% 3.87/1.00  fof(f34,plain,(
% 3.87/1.00    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.87/1.00    inference(flattening,[],[f33])).
% 3.87/1.00  
% 3.87/1.00  fof(f67,plain,(
% 3.87/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f34])).
% 3.87/1.00  
% 3.87/1.00  fof(f64,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f32])).
% 3.87/1.00  
% 3.87/1.00  fof(f65,plain,(
% 3.87/1.00    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f32])).
% 3.87/1.00  
% 3.87/1.00  fof(f71,plain,(
% 3.87/1.00    ~v1_xboole_0(sK1)),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f14,axiom,(
% 3.87/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f35,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.87/1.00    inference(ennf_transformation,[],[f14])).
% 3.87/1.00  
% 3.87/1.00  fof(f36,plain,(
% 3.87/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.87/1.00    inference(flattening,[],[f35])).
% 3.87/1.00  
% 3.87/1.00  fof(f68,plain,(
% 3.87/1.00    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f36])).
% 3.87/1.00  
% 3.87/1.00  fof(f9,axiom,(
% 3.87/1.00    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f25,plain,(
% 3.87/1.00    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f9])).
% 3.87/1.00  
% 3.87/1.00  fof(f26,plain,(
% 3.87/1.00    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.87/1.00    inference(flattening,[],[f25])).
% 3.87/1.00  
% 3.87/1.00  fof(f60,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f26])).
% 3.87/1.00  
% 3.87/1.00  fof(f79,plain,(
% 3.87/1.00    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 3.87/1.00    inference(cnf_transformation,[],[f48])).
% 3.87/1.00  
% 3.87/1.00  fof(f11,axiom,(
% 3.87/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f29,plain,(
% 3.87/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.87/1.00    inference(ennf_transformation,[],[f11])).
% 3.87/1.00  
% 3.87/1.00  fof(f30,plain,(
% 3.87/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.87/1.00    inference(flattening,[],[f29])).
% 3.87/1.00  
% 3.87/1.00  fof(f63,plain,(
% 3.87/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.87/1.00    inference(cnf_transformation,[],[f30])).
% 3.87/1.00  
% 3.87/1.00  fof(f8,axiom,(
% 3.87/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f23,plain,(
% 3.87/1.00    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/1.00    inference(ennf_transformation,[],[f8])).
% 3.87/1.00  
% 3.87/1.00  fof(f24,plain,(
% 3.87/1.00    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/1.00    inference(flattening,[],[f23])).
% 3.87/1.00  
% 3.87/1.00  fof(f59,plain,(
% 3.87/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/1.00    inference(cnf_transformation,[],[f24])).
% 3.87/1.00  
% 3.87/1.00  fof(f1,axiom,(
% 3.87/1.00    v1_xboole_0(k1_xboole_0)),
% 3.87/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/1.00  
% 3.87/1.00  fof(f49,plain,(
% 3.87/1.00    v1_xboole_0(k1_xboole_0)),
% 3.87/1.00    inference(cnf_transformation,[],[f1])).
% 3.87/1.00  
% 3.87/1.00  cnf(c_23,negated_conjecture,
% 3.87/1.00      ( m1_subset_1(sK5,sK1) ),
% 3.87/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1280,plain,
% 3.87/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_26,negated_conjecture,
% 3.87/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.87/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1277,plain,
% 3.87/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8,plain,
% 3.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1288,plain,
% 3.87/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.87/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1876,plain,
% 3.87/1.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1277,c_1288]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_24,negated_conjecture,
% 3.87/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.87/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1279,plain,
% 3.87/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1,plain,
% 3.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.87/1.00      | ~ v1_relat_1(X1)
% 3.87/1.00      | v1_relat_1(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1291,plain,
% 3.87/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.87/1.00      | v1_relat_1(X1) != iProver_top
% 3.87/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2377,plain,
% 3.87/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 3.87/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_1291]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_37,plain,
% 3.87/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1532,plain,
% 3.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | v1_relat_1(X0)
% 3.87/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.87/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1717,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.87/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 3.87/1.00      | v1_relat_1(sK4) ),
% 3.87/1.00      inference(instantiation,[status(thm)],[c_1532]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1718,plain,
% 3.87/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.87/1.00      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 3.87/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1717]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_4,plain,
% 3.87/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.87/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1735,plain,
% 3.87/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 3.87/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1736,plain,
% 3.87/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1735]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2654,plain,
% 3.87/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_2377,c_37,c_1718,c_1736]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_6,plain,
% 3.87/1.00      ( v4_relat_1(X0,X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.87/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_13,plain,
% 3.87/1.00      ( ~ v1_partfun1(X0,X1)
% 3.87/1.00      | ~ v4_relat_1(X0,X1)
% 3.87/1.00      | ~ v1_relat_1(X0)
% 3.87/1.00      | k1_relat_1(X0) = X1 ),
% 3.87/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_22,negated_conjecture,
% 3.87/1.00      ( v1_partfun1(sK4,sK0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_465,plain,
% 3.87/1.00      ( ~ v4_relat_1(X0,X1)
% 3.87/1.00      | ~ v1_relat_1(X0)
% 3.87/1.00      | k1_relat_1(X0) = X1
% 3.87/1.00      | sK4 != X0
% 3.87/1.00      | sK0 != X1 ),
% 3.87/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_466,plain,
% 3.87/1.00      ( ~ v4_relat_1(sK4,sK0)
% 3.87/1.00      | ~ v1_relat_1(sK4)
% 3.87/1.00      | k1_relat_1(sK4) = sK0 ),
% 3.87/1.00      inference(unflattening,[status(thm)],[c_465]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_530,plain,
% 3.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_relat_1(sK4)
% 3.87/1.00      | k1_relat_1(sK4) = sK0
% 3.87/1.00      | sK4 != X0
% 3.87/1.00      | sK0 != X1 ),
% 3.87/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_466]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_531,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.87/1.00      | ~ v1_relat_1(sK4)
% 3.87/1.00      | k1_relat_1(sK4) = sK0 ),
% 3.87/1.00      inference(unflattening,[status(thm)],[c_530]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_766,plain,
% 3.87/1.00      ( ~ v1_relat_1(sK4) | sP0_iProver_split | k1_relat_1(sK4) = sK0 ),
% 3.87/1.00      inference(splitting,
% 3.87/1.00                [splitting(split),new_symbols(definition,[])],
% 3.87/1.00                [c_531]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1266,plain,
% 3.87/1.00      ( k1_relat_1(sK4) = sK0
% 3.87/1.00      | v1_relat_1(sK4) != iProver_top
% 3.87/1.00      | sP0_iProver_split = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2659,plain,
% 3.87/1.00      ( k1_relat_1(sK4) = sK0 | sP0_iProver_split = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_2654,c_1266]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_798,plain,
% 3.87/1.00      ( k1_relat_1(sK4) = sK0
% 3.87/1.00      | v1_relat_1(sK4) != iProver_top
% 3.87/1.00      | sP0_iProver_split = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_765,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.87/1.00      | ~ sP0_iProver_split ),
% 3.87/1.00      inference(splitting,
% 3.87/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.87/1.00                [c_531]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1267,plain,
% 3.87/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.87/1.00      | sP0_iProver_split != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2092,plain,
% 3.87/1.00      ( sP0_iProver_split != iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_1267]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3710,plain,
% 3.87/1.00      ( k1_relat_1(sK4) = sK0 ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_2659,c_37,c_798,c_1718,c_1736,c_2092]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_7,plain,
% 3.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1289,plain,
% 3.87/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.87/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2367,plain,
% 3.87/1.00      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_1289]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3713,plain,
% 3.87/1.00      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 3.87/1.00      inference(demodulation,[status(thm)],[c_3710,c_2367]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_20,plain,
% 3.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 3.87/1.00      | ~ m1_subset_1(X5,X1)
% 3.87/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_funct_1(X4)
% 3.87/1.00      | ~ v1_funct_1(X0)
% 3.87/1.00      | v1_xboole_0(X2)
% 3.87/1.00      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k7_partfun1(X3,X4,k1_funct_1(X0,X5))
% 3.87/1.00      | k1_xboole_0 = X1 ),
% 3.87/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1281,plain,
% 3.87/1.00      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k7_partfun1(X2,X4,k1_funct_1(X3,X5))
% 3.87/1.00      | k1_xboole_0 = X0
% 3.87/1.00      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.87/1.00      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.87/1.00      | m1_subset_1(X5,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.87/1.00      | v1_funct_1(X4) != iProver_top
% 3.87/1.00      | v1_funct_1(X3) != iProver_top
% 3.87/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3905,plain,
% 3.87/1.00      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
% 3.87/1.00      | k1_xboole_0 = X0
% 3.87/1.00      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.87/1.00      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.87/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.87/1.00      | v1_funct_1(X1) != iProver_top
% 3.87/1.00      | v1_funct_1(sK4) != iProver_top
% 3.87/1.00      | v1_xboole_0(sK0) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_3713,c_1281]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_30,negated_conjecture,
% 3.87/1.00      ( ~ v1_xboole_0(sK0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_31,plain,
% 3.87/1.00      ( v1_xboole_0(sK0) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_25,negated_conjecture,
% 3.87/1.00      ( v1_funct_1(sK4) ),
% 3.87/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_36,plain,
% 3.87/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_6941,plain,
% 3.87/1.00      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.87/1.00      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.87/1.00      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.87/1.00      | k1_xboole_0 = X0
% 3.87/1.00      | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
% 3.87/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_3905,c_31,c_36,c_37]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_6942,plain,
% 3.87/1.00      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
% 3.87/1.00      | k1_xboole_0 = X0
% 3.87/1.00      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.87/1.00      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.87/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.87/1.00      inference(renaming,[status(thm)],[c_6941]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_6954,plain,
% 3.87/1.00      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 3.87/1.00      | sK1 = k1_xboole_0
% 3.87/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.87/1.00      | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 3.87/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.87/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1876,c_6942]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_28,negated_conjecture,
% 3.87/1.00      ( v1_funct_1(sK3) ),
% 3.87/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_33,plain,
% 3.87/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_27,negated_conjecture,
% 3.87/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_34,plain,
% 3.87/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_35,plain,
% 3.87/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1720,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.87/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.87/1.00      | v1_relat_1(sK3) ),
% 3.87/1.00      inference(instantiation,[status(thm)],[c_1532]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1721,plain,
% 3.87/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.87/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.87/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1720]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1738,plain,
% 3.87/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.87/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1739,plain,
% 3.87/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_5,plain,
% 3.87/1.00      ( v5_relat_1(X0,X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.87/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3,plain,
% 3.87/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 3.87/1.00      | ~ v5_relat_1(X0,X1)
% 3.87/1.00      | ~ v1_relat_1(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_321,plain,
% 3.87/1.00      ( r1_tarski(k2_relat_1(X0),X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.87/1.00      | ~ v1_relat_1(X0) ),
% 3.87/1.00      inference(resolution,[status(thm)],[c_5,c_3]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1272,plain,
% 3.87/1.00      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.87/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.87/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3828,plain,
% 3.87/1.00      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.87/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1277,c_1272]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8356,plain,
% 3.87/1.00      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 3.87/1.00      | sK1 = k1_xboole_0
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_6954,c_33,c_34,c_35,c_1721,c_1739,c_3828]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8366,plain,
% 3.87/1.00      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
% 3.87/1.00      | sK1 = k1_xboole_0 ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1280,c_8356]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_15,plain,
% 3.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.87/1.00      | ~ v1_funct_1(X3)
% 3.87/1.00      | ~ v1_funct_1(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1286,plain,
% 3.87/1.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 3.87/1.00      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
% 3.87/1.00      | v1_funct_1(X0) != iProver_top
% 3.87/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_18,plain,
% 3.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ m1_subset_1(X3,X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_funct_1(X0)
% 3.87/1.00      | v1_xboole_0(X1)
% 3.87/1.00      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.87/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1283,plain,
% 3.87/1.00      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.87/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.87/1.00      | v1_funct_1(X2) != iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3047,plain,
% 3.87/1.00      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.87/1.00      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.87/1.00      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 3.87/1.00      | m1_subset_1(X5,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.87/1.00      | v1_funct_1(X3) != iProver_top
% 3.87/1.00      | v1_funct_1(X4) != iProver_top
% 3.87/1.00      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1286,c_1283]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_17,plain,
% 3.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_funct_1(X3)
% 3.87/1.00      | ~ v1_funct_1(X0)
% 3.87/1.00      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 3.87/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1284,plain,
% 3.87/1.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 3.87/1.00      | v1_funct_1(X0) != iProver_top
% 3.87/1.00      | v1_funct_1(X3) != iProver_top
% 3.87/1.00      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_16,plain,
% 3.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/1.00      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 3.87/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_funct_1(X4)
% 3.87/1.00      | ~ v1_funct_1(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1285,plain,
% 3.87/1.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.87/1.00      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
% 3.87/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.87/1.00      | v1_funct_1(X4) != iProver_top
% 3.87/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9542,plain,
% 3.87/1.00      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.87/1.00      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.87/1.00      | m1_subset_1(X5,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.87/1.00      | v1_funct_1(X4) != iProver_top
% 3.87/1.00      | v1_funct_1(X3) != iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.87/1.00      inference(forward_subsumption_resolution,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_3047,c_1284,c_1285]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9549,plain,
% 3.87/1.00      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.87/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.87/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(X1) != iProver_top
% 3.87/1.00      | v1_funct_1(sK3) != iProver_top
% 3.87/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1277,c_9542]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_29,negated_conjecture,
% 3.87/1.00      ( ~ v1_xboole_0(sK1) ),
% 3.87/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_32,plain,
% 3.87/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9758,plain,
% 3.87/1.00      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.87/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_9549,c_32,c_33,c_34]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9770,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_9758]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9853,plain,
% 3.87/1.00      ( m1_subset_1(X0,sK1) != iProver_top
% 3.87/1.00      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_9770,c_36]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9854,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.87/1.00      inference(renaming,[status(thm)],[c_9853]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9862,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1280,c_9854]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_19,plain,
% 3.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ m1_subset_1(X3,X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_funct_1(X0)
% 3.87/1.00      | v1_xboole_0(X2)
% 3.87/1.00      | v1_xboole_0(X1)
% 3.87/1.00      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 3.87/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1282,plain,
% 3.87/1.00      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
% 3.87/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.87/1.00      | v1_funct_1(X2) != iProver_top
% 3.87/1.00      | v1_xboole_0(X1) = iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3046,plain,
% 3.87/1.00      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.87/1.00      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.87/1.00      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 3.87/1.00      | m1_subset_1(X5,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.87/1.00      | v1_funct_1(X3) != iProver_top
% 3.87/1.00      | v1_funct_1(X4) != iProver_top
% 3.87/1.00      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top
% 3.87/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1286,c_1282]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8411,plain,
% 3.87/1.00      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.87/1.00      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.87/1.00      | m1_subset_1(X5,X0) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.87/1.00      | v1_funct_1(X4) != iProver_top
% 3.87/1.00      | v1_funct_1(X3) != iProver_top
% 3.87/1.00      | v1_xboole_0(X1) = iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.87/1.00      inference(forward_subsumption_resolution,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_3046,c_1284,c_1285]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8418,plain,
% 3.87/1.00      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.87/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.87/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(X1) != iProver_top
% 3.87/1.00      | v1_funct_1(sK3) != iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top
% 3.87/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1277,c_8411]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8675,plain,
% 3.87/1.00      ( v1_xboole_0(X0) = iProver_top
% 3.87/1.00      | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.87/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_8418,c_32,c_33,c_34]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8676,plain,
% 3.87/1.00      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.87/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.87/1.00      | m1_subset_1(X2,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(X1) != iProver_top
% 3.87/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.87/1.00      inference(renaming,[status(thm)],[c_8675]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8688,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(sK4) != iProver_top
% 3.87/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_8676]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_11,plain,
% 3.87/1.00      ( ~ v1_partfun1(X0,X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_xboole_0(X2)
% 3.87/1.00      | v1_xboole_0(X1) ),
% 3.87/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_478,plain,
% 3.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_xboole_0(X2)
% 3.87/1.00      | v1_xboole_0(X1)
% 3.87/1.00      | sK4 != X0
% 3.87/1.00      | sK0 != X1 ),
% 3.87/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_479,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.87/1.00      | ~ v1_xboole_0(X0)
% 3.87/1.00      | v1_xboole_0(sK0) ),
% 3.87/1.00      inference(unflattening,[status(thm)],[c_478]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_481,plain,
% 3.87/1.00      ( ~ v1_xboole_0(X0)
% 3.87/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_479,c_30]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_482,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.87/1.00      | ~ v1_xboole_0(X0) ),
% 3.87/1.00      inference(renaming,[status(thm)],[c_481]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1269,plain,
% 3.87/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.87/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1952,plain,
% 3.87/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_1269]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8801,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_8688,c_36,c_1952]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8810,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1280,c_8801]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9881,plain,
% 3.87/1.00      ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 3.87/1.00      inference(demodulation,[status(thm)],[c_9862,c_8810]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2514,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 3.87/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top
% 3.87/1.00      | v1_funct_1(sK3) != iProver_top
% 3.87/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1277,c_1283]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2706,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 3.87/1.00      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_2514,c_32,c_33,c_34]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2715,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1280,c_2706]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_21,negated_conjecture,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 3.87/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2761,plain,
% 3.87/1.00      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.87/1.00      inference(demodulation,[status(thm)],[c_2715,c_21]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_8829,plain,
% 3.87/1.00      ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.87/1.00      inference(demodulation,[status(thm)],[c_8810,c_2761]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9946,plain,
% 3.87/1.00      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.87/1.00      inference(demodulation,[status(thm)],[c_9881,c_8829]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9953,plain,
% 3.87/1.00      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 3.87/1.00      | sK1 = k1_xboole_0 ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_8366,c_9946]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_14,plain,
% 3.87/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ m1_subset_1(X3,X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 3.87/1.00      | ~ v1_funct_1(X0)
% 3.87/1.00      | v1_xboole_0(X1) ),
% 3.87/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1287,plain,
% 3.87/1.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.87/1.00      | m1_subset_1(X3,X1) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.87/1.00      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 3.87/1.00      | v1_funct_1(X0) != iProver_top
% 3.87/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2762,plain,
% 3.87/1.00      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.87/1.00      | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
% 3.87/1.00      | m1_subset_1(sK5,sK1) != iProver_top
% 3.87/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.87/1.00      | v1_funct_1(sK3) != iProver_top
% 3.87/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_2715,c_1287]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_38,plain,
% 3.87/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3734,plain,
% 3.87/1.00      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_2762,c_32,c_33,c_34,c_35,c_38]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2854,plain,
% 3.87/1.00      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 3.87/1.00      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,sK0) != iProver_top
% 3.87/1.00      | v1_funct_1(sK4) != iProver_top
% 3.87/1.00      | v1_xboole_0(sK0) = iProver_top
% 3.87/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_1282]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_9,plain,
% 3.87/1.00      ( v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ v1_partfun1(X0,X1)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_funct_1(X0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_492,plain,
% 3.87/1.00      ( v1_funct_2(X0,X1,X2)
% 3.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/1.00      | ~ v1_funct_1(X0)
% 3.87/1.00      | sK4 != X0
% 3.87/1.00      | sK0 != X1 ),
% 3.87/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_493,plain,
% 3.87/1.00      ( v1_funct_2(sK4,sK0,X0)
% 3.87/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.87/1.00      | ~ v1_funct_1(sK4) ),
% 3.87/1.00      inference(unflattening,[status(thm)],[c_492]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_497,plain,
% 3.87/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.87/1.00      | v1_funct_2(sK4,sK0,X0) ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_493,c_25]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_498,plain,
% 3.87/1.00      ( v1_funct_2(sK4,sK0,X0)
% 3.87/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
% 3.87/1.00      inference(renaming,[status(thm)],[c_497]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1526,plain,
% 3.87/1.00      ( v1_funct_2(sK4,sK0,sK2)
% 3.87/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.87/1.00      inference(instantiation,[status(thm)],[c_498]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1527,plain,
% 3.87/1.00      ( v1_funct_2(sK4,sK0,sK2) = iProver_top
% 3.87/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1526]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3146,plain,
% 3.87/1.00      ( m1_subset_1(X0,sK0) != iProver_top
% 3.87/1.00      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_2854,c_31,c_36,c_37,c_1527,c_1952]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3147,plain,
% 3.87/1.00      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 3.87/1.00      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.87/1.00      inference(renaming,[status(thm)],[c_3146]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3739,plain,
% 3.87/1.00      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_3734,c_3147]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2513,plain,
% 3.87/1.00      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 3.87/1.00      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 3.87/1.00      | m1_subset_1(X0,sK0) != iProver_top
% 3.87/1.00      | v1_funct_1(sK4) != iProver_top
% 3.87/1.00      | v1_xboole_0(sK0) = iProver_top ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_1279,c_1283]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_2693,plain,
% 3.87/1.00      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 3.87/1.00      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_2513,c_31,c_36,c_37,c_1527]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3740,plain,
% 3.87/1.00      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.87/1.00      inference(superposition,[status(thm)],[c_3734,c_2693]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_3743,plain,
% 3.87/1.00      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.87/1.00      inference(light_normalisation,[status(thm)],[c_3739,c_3740]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_10045,plain,
% 3.87/1.00      ( sK1 = k1_xboole_0 ),
% 3.87/1.00      inference(global_propositional_subsumption,
% 3.87/1.00                [status(thm)],
% 3.87/1.00                [c_9953,c_3743]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_1274,plain,
% 3.87/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_10104,plain,
% 3.87/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.87/1.00      inference(demodulation,[status(thm)],[c_10045,c_1274]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_0,plain,
% 3.87/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.87/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(c_94,plain,
% 3.87/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.87/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.87/1.00  
% 3.87/1.00  cnf(contradiction,plain,
% 3.87/1.00      ( $false ),
% 3.87/1.00      inference(minisat,[status(thm)],[c_10104,c_94]) ).
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/1.00  
% 3.87/1.00  ------                               Statistics
% 3.87/1.00  
% 3.87/1.00  ------ General
% 3.87/1.00  
% 3.87/1.00  abstr_ref_over_cycles:                  0
% 3.87/1.00  abstr_ref_under_cycles:                 0
% 3.87/1.00  gc_basic_clause_elim:                   0
% 3.87/1.00  forced_gc_time:                         0
% 3.87/1.00  parsing_time:                           0.011
% 3.87/1.00  unif_index_cands_time:                  0.
% 3.87/1.00  unif_index_add_time:                    0.
% 3.87/1.00  orderings_time:                         0.
% 3.87/1.00  out_proof_time:                         0.014
% 3.87/1.00  total_time:                             0.459
% 3.87/1.00  num_of_symbols:                         58
% 3.87/1.00  num_of_terms:                           13474
% 3.87/1.00  
% 3.87/1.00  ------ Preprocessing
% 3.87/1.00  
% 3.87/1.00  num_of_splits:                          1
% 3.87/1.00  num_of_split_atoms:                     1
% 3.87/1.00  num_of_reused_defs:                     0
% 3.87/1.00  num_eq_ax_congr_red:                    31
% 3.87/1.00  num_of_sem_filtered_clauses:            1
% 3.87/1.00  num_of_subtypes:                        0
% 3.87/1.00  monotx_restored_types:                  0
% 3.87/1.00  sat_num_of_epr_types:                   0
% 3.87/1.00  sat_num_of_non_cyclic_types:            0
% 3.87/1.00  sat_guarded_non_collapsed_types:        0
% 3.87/1.00  num_pure_diseq_elim:                    0
% 3.87/1.00  simp_replaced_by:                       0
% 3.87/1.00  res_preprocessed:                       144
% 3.87/1.00  prep_upred:                             0
% 3.87/1.00  prep_unflattend:                        18
% 3.87/1.00  smt_new_axioms:                         0
% 3.87/1.00  pred_elim_cands:                        6
% 3.87/1.00  pred_elim:                              3
% 3.87/1.00  pred_elim_cl:                           3
% 3.87/1.00  pred_elim_cycles:                       7
% 3.87/1.00  merged_defs:                            0
% 3.87/1.00  merged_defs_ncl:                        0
% 3.87/1.00  bin_hyper_res:                          0
% 3.87/1.00  prep_cycles:                            4
% 3.87/1.00  pred_elim_time:                         0.012
% 3.87/1.00  splitting_time:                         0.
% 3.87/1.00  sem_filter_time:                        0.
% 3.87/1.00  monotx_time:                            0.001
% 3.87/1.00  subtype_inf_time:                       0.
% 3.87/1.00  
% 3.87/1.00  ------ Problem properties
% 3.87/1.00  
% 3.87/1.00  clauses:                                28
% 3.87/1.00  conjectures:                            9
% 3.87/1.00  epr:                                    7
% 3.87/1.00  horn:                                   23
% 3.87/1.00  ground:                                 11
% 3.87/1.00  unary:                                  11
% 3.87/1.00  binary:                                 5
% 3.87/1.00  lits:                                   85
% 3.87/1.00  lits_eq:                                8
% 3.87/1.00  fd_pure:                                0
% 3.87/1.00  fd_pseudo:                              0
% 3.87/1.00  fd_cond:                                1
% 3.87/1.00  fd_pseudo_cond:                         0
% 3.87/1.00  ac_symbols:                             0
% 3.87/1.00  
% 3.87/1.00  ------ Propositional Solver
% 3.87/1.00  
% 3.87/1.00  prop_solver_calls:                      28
% 3.87/1.00  prop_fast_solver_calls:                 1866
% 3.87/1.00  smt_solver_calls:                       0
% 3.87/1.00  smt_fast_solver_calls:                  0
% 3.87/1.00  prop_num_of_clauses:                    3827
% 3.87/1.00  prop_preprocess_simplified:             7784
% 3.87/1.00  prop_fo_subsumed:                       107
% 3.87/1.00  prop_solver_time:                       0.
% 3.87/1.00  smt_solver_time:                        0.
% 3.87/1.00  smt_fast_solver_time:                   0.
% 3.87/1.00  prop_fast_solver_time:                  0.
% 3.87/1.00  prop_unsat_core_time:                   0.
% 3.87/1.00  
% 3.87/1.00  ------ QBF
% 3.87/1.00  
% 3.87/1.00  qbf_q_res:                              0
% 3.87/1.00  qbf_num_tautologies:                    0
% 3.87/1.00  qbf_prep_cycles:                        0
% 3.87/1.00  
% 3.87/1.00  ------ BMC1
% 3.87/1.00  
% 3.87/1.00  bmc1_current_bound:                     -1
% 3.87/1.00  bmc1_last_solved_bound:                 -1
% 3.87/1.00  bmc1_unsat_core_size:                   -1
% 3.87/1.00  bmc1_unsat_core_parents_size:           -1
% 3.87/1.00  bmc1_merge_next_fun:                    0
% 3.87/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.87/1.00  
% 3.87/1.00  ------ Instantiation
% 3.87/1.00  
% 3.87/1.00  inst_num_of_clauses:                    869
% 3.87/1.00  inst_num_in_passive:                    139
% 3.87/1.00  inst_num_in_active:                     641
% 3.87/1.00  inst_num_in_unprocessed:                89
% 3.87/1.00  inst_num_of_loops:                      670
% 3.87/1.00  inst_num_of_learning_restarts:          0
% 3.87/1.00  inst_num_moves_active_passive:          24
% 3.87/1.00  inst_lit_activity:                      0
% 3.87/1.00  inst_lit_activity_moves:                0
% 3.87/1.00  inst_num_tautologies:                   0
% 3.87/1.00  inst_num_prop_implied:                  0
% 3.87/1.00  inst_num_existing_simplified:           0
% 3.87/1.00  inst_num_eq_res_simplified:             0
% 3.87/1.00  inst_num_child_elim:                    0
% 3.87/1.00  inst_num_of_dismatching_blockings:      84
% 3.87/1.00  inst_num_of_non_proper_insts:           677
% 3.87/1.00  inst_num_of_duplicates:                 0
% 3.87/1.00  inst_inst_num_from_inst_to_res:         0
% 3.87/1.00  inst_dismatching_checking_time:         0.
% 3.87/1.00  
% 3.87/1.00  ------ Resolution
% 3.87/1.00  
% 3.87/1.00  res_num_of_clauses:                     0
% 3.87/1.00  res_num_in_passive:                     0
% 3.87/1.00  res_num_in_active:                      0
% 3.87/1.00  res_num_of_loops:                       148
% 3.87/1.00  res_forward_subset_subsumed:            72
% 3.87/1.00  res_backward_subset_subsumed:           0
% 3.87/1.00  res_forward_subsumed:                   0
% 3.87/1.00  res_backward_subsumed:                  0
% 3.87/1.00  res_forward_subsumption_resolution:     2
% 3.87/1.00  res_backward_subsumption_resolution:    0
% 3.87/1.00  res_clause_to_clause_subsumption:       2559
% 3.87/1.00  res_orphan_elimination:                 0
% 3.87/1.00  res_tautology_del:                      70
% 3.87/1.00  res_num_eq_res_simplified:              0
% 3.87/1.00  res_num_sel_changes:                    0
% 3.87/1.00  res_moves_from_active_to_pass:          0
% 3.87/1.00  
% 3.87/1.00  ------ Superposition
% 3.87/1.00  
% 3.87/1.00  sup_time_total:                         0.
% 3.87/1.00  sup_time_generating:                    0.
% 3.87/1.00  sup_time_sim_full:                      0.
% 3.87/1.00  sup_time_sim_immed:                     0.
% 3.87/1.00  
% 3.87/1.00  sup_num_of_clauses:                     224
% 3.87/1.00  sup_num_in_active:                      68
% 3.87/1.00  sup_num_in_passive:                     156
% 3.87/1.00  sup_num_of_loops:                       132
% 3.87/1.00  sup_fw_superposition:                   185
% 3.87/1.00  sup_bw_superposition:                   20
% 3.87/1.00  sup_immediate_simplified:               6
% 3.87/1.00  sup_given_eliminated:                   0
% 3.87/1.00  comparisons_done:                       0
% 3.87/1.00  comparisons_avoided:                    15
% 3.87/1.00  
% 3.87/1.00  ------ Simplifications
% 3.87/1.00  
% 3.87/1.00  
% 3.87/1.00  sim_fw_subset_subsumed:                 0
% 3.87/1.00  sim_bw_subset_subsumed:                 1
% 3.87/1.00  sim_fw_subsumed:                        2
% 3.87/1.00  sim_bw_subsumed:                        0
% 3.87/1.00  sim_fw_subsumption_res:                 31
% 3.87/1.00  sim_bw_subsumption_res:                 0
% 3.87/1.00  sim_tautology_del:                      0
% 3.87/1.00  sim_eq_tautology_del:                   5
% 3.87/1.00  sim_eq_res_simp:                        0
% 3.87/1.00  sim_fw_demodulated:                     0
% 3.87/1.00  sim_bw_demodulated:                     63
% 3.87/1.00  sim_light_normalised:                   6
% 3.87/1.00  sim_joinable_taut:                      0
% 3.87/1.00  sim_joinable_simp:                      0
% 3.87/1.00  sim_ac_normalised:                      0
% 3.87/1.00  sim_smt_subsumption:                    0
% 3.87/1.00  
%------------------------------------------------------------------------------
