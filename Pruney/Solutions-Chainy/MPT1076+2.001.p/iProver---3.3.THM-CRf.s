%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:20 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  205 (1348 expanded)
%              Number of clauses        :  123 ( 337 expanded)
%              Number of leaves         :   22 ( 469 expanded)
%              Depth                    :   22
%              Number of atoms          :  819 (9923 expanded)
%              Number of equality atoms :  308 (1531 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
          & v1_partfun1(X4,X0)
          & m1_subset_1(X5,X1) )
     => ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5))
        & v1_partfun1(X4,X0)
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
              & v1_partfun1(X4,X0)
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5))
            & v1_partfun1(sK4,X0)
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                  & v1_partfun1(X4,X0)
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5))
                & v1_partfun1(X4,X0)
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
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
                    ( k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5))
                    & v1_partfun1(X4,X0)
                    & m1_subset_1(X5,sK1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
            & v1_funct_2(X3,sK1,X0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
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
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
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

fof(f53,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f52,f51,f50,f49,f48])).

fof(f84,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
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
                   => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f42])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
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

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1824,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1821,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1835,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2571,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1821,c_1835])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1823,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_370,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_16])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_16,c_7,c_5])).

cnf(c_375,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_1815,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2604,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_partfun1(sK4,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1815])).

cnf(c_24,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2137,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | k1_relat_1(sK4) = sK0 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_2284,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relat_1(sK4) = sK0 ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_2852,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_26,c_24,c_2284])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1836,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2679,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1823,c_1836])).

cnf(c_2855,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_2852,c_2679])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X5,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1826,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4319,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2855,c_1826])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_33,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9795,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4319,c_33,c_38,c_39])).

cnf(c_9796,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9795])).

cnf(c_9808,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2571,c_9796])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2090,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2091,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2111,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2112,plain,
    ( v5_relat_1(sK3,sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2111])).

cnf(c_3,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2269,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ v5_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2275,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | v5_relat_1(sK3,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2269])).

cnf(c_2277,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v5_relat_1(sK3,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_10237,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9808,c_35,c_36,c_37,c_2091,c_2112,c_2277])).

cnf(c_10247,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1824,c_10237])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1831,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1828,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4552,plain,
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
    inference(superposition,[status(thm)],[c_1831,c_1828])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1829,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1830,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_11457,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4552,c_1829,c_1830])).

cnf(c_11464,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_11457])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11662,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11464,c_34,c_35,c_36])).

cnf(c_11674,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_11662])).

cnf(c_11723,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11674,c_38])).

cnf(c_11724,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_11723])).

cnf(c_11732,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1824,c_11724])).

cnf(c_2605,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_partfun1(sK3,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_1815])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2175,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | v1_partfun1(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2350,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_2553,plain,
    ( ~ v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | k1_relat_1(sK3) = sK1 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_2555,plain,
    ( ~ v1_partfun1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relat_1(sK3) = sK1 ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_2859,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2605,c_32,c_30,c_29,c_28,c_2350,c_2555])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_339,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ m1_subset_1(X2,X3)
    | m1_subset_1(k1_funct_1(X0,X4),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X3)
    | X4 != X2
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_340,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ m1_subset_1(X2,k1_relat_1(X0))
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_1816,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_relat_1(X0)) != iProver_top
    | m1_subset_1(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1827,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4440,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1827])).

cnf(c_41,plain,
    ( v1_partfun1(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2164,plain,
    ( v1_funct_2(sK4,X0,X1)
    | ~ v1_partfun1(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2341,plain,
    ( v1_funct_2(sK4,sK0,sK2)
    | ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2164])).

cnf(c_2342,plain,
    ( v1_funct_2(sK4,sK0,sK2) = iProver_top
    | v1_partfun1(sK4,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2341])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1833,plain,
    ( v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2822,plain,
    ( v1_partfun1(sK4,sK0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1833])).

cnf(c_4733,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4440,c_33,c_38,c_39,c_41,c_2342,c_2822])).

cnf(c_4734,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4733])).

cnf(c_4741,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(X0,X1)) = k7_partfun1(sK2,sK4,k1_funct_1(X0,X1))
    | v5_relat_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_4734])).

cnf(c_5313,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | v5_relat_1(sK3,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2859,c_4741])).

cnf(c_5320,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | v5_relat_1(sK3,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5313,c_2859])).

cnf(c_5370,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5320,c_34,c_35,c_37,c_2091,c_2112])).

cnf(c_5371,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5370])).

cnf(c_5379,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1824,c_5371])).

cnf(c_3618,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1823,c_1828])).

cnf(c_3928,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3618,c_33,c_38,c_39,c_41,c_2342])).

cnf(c_3936,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(X0,X1)) = k1_funct_1(sK4,k1_funct_1(X0,X1))
    | v5_relat_1(X0,sK0) != iProver_top
    | m1_subset_1(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_3928])).

cnf(c_4185,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | v5_relat_1(sK3,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2859,c_3936])).

cnf(c_4192,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | v5_relat_1(sK3,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4185,c_2859])).

cnf(c_4242,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4192,c_34,c_35,c_37,c_2091,c_2112])).

cnf(c_4243,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4242])).

cnf(c_4251,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1824,c_4243])).

cnf(c_5381,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_5379,c_4251])).

cnf(c_3619,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_1828])).

cnf(c_3941,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3619,c_34,c_35,c_36])).

cnf(c_3950,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1824,c_3941])).

cnf(c_23,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4121,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3950,c_23])).

cnf(c_5427,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_5381,c_4121])).

cnf(c_11751,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_11732,c_5427])).

cnf(c_11753,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10247,c_11751])).

cnf(c_1818,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11954,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11753,c_1818])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_102,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11954,c_102])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.73/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.99  
% 3.73/0.99  ------  iProver source info
% 3.73/0.99  
% 3.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.99  git: non_committed_changes: false
% 3.73/0.99  git: last_make_outside_of_git: false
% 3.73/0.99  
% 3.73/0.99  ------ 
% 3.73/0.99  
% 3.73/0.99  ------ Input Options
% 3.73/0.99  
% 3.73/0.99  --out_options                           all
% 3.73/0.99  --tptp_safe_out                         true
% 3.73/0.99  --problem_path                          ""
% 3.73/0.99  --include_path                          ""
% 3.73/0.99  --clausifier                            res/vclausify_rel
% 3.73/0.99  --clausifier_options                    --mode clausify
% 3.73/0.99  --stdin                                 false
% 3.73/0.99  --stats_out                             all
% 3.73/0.99  
% 3.73/0.99  ------ General Options
% 3.73/0.99  
% 3.73/0.99  --fof                                   false
% 3.73/0.99  --time_out_real                         305.
% 3.73/0.99  --time_out_virtual                      -1.
% 3.73/0.99  --symbol_type_check                     false
% 3.73/0.99  --clausify_out                          false
% 3.73/0.99  --sig_cnt_out                           false
% 3.73/0.99  --trig_cnt_out                          false
% 3.73/0.99  --trig_cnt_out_tolerance                1.
% 3.73/0.99  --trig_cnt_out_sk_spl                   false
% 3.73/0.99  --abstr_cl_out                          false
% 3.73/0.99  
% 3.73/0.99  ------ Global Options
% 3.73/0.99  
% 3.73/0.99  --schedule                              default
% 3.73/0.99  --add_important_lit                     false
% 3.73/0.99  --prop_solver_per_cl                    1000
% 3.73/0.99  --min_unsat_core                        false
% 3.73/0.99  --soft_assumptions                      false
% 3.73/0.99  --soft_lemma_size                       3
% 3.73/0.99  --prop_impl_unit_size                   0
% 3.73/0.99  --prop_impl_unit                        []
% 3.73/0.99  --share_sel_clauses                     true
% 3.73/0.99  --reset_solvers                         false
% 3.73/0.99  --bc_imp_inh                            [conj_cone]
% 3.73/0.99  --conj_cone_tolerance                   3.
% 3.73/0.99  --extra_neg_conj                        none
% 3.73/0.99  --large_theory_mode                     true
% 3.73/0.99  --prolific_symb_bound                   200
% 3.73/0.99  --lt_threshold                          2000
% 3.73/0.99  --clause_weak_htbl                      true
% 3.73/0.99  --gc_record_bc_elim                     false
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing Options
% 3.73/0.99  
% 3.73/0.99  --preprocessing_flag                    true
% 3.73/0.99  --time_out_prep_mult                    0.1
% 3.73/0.99  --splitting_mode                        input
% 3.73/0.99  --splitting_grd                         true
% 3.73/0.99  --splitting_cvd                         false
% 3.73/0.99  --splitting_cvd_svl                     false
% 3.73/0.99  --splitting_nvd                         32
% 3.73/0.99  --sub_typing                            true
% 3.73/0.99  --prep_gs_sim                           true
% 3.73/0.99  --prep_unflatten                        true
% 3.73/0.99  --prep_res_sim                          true
% 3.73/0.99  --prep_upred                            true
% 3.73/0.99  --prep_sem_filter                       exhaustive
% 3.73/0.99  --prep_sem_filter_out                   false
% 3.73/0.99  --pred_elim                             true
% 3.73/0.99  --res_sim_input                         true
% 3.73/0.99  --eq_ax_congr_red                       true
% 3.73/0.99  --pure_diseq_elim                       true
% 3.73/0.99  --brand_transform                       false
% 3.73/0.99  --non_eq_to_eq                          false
% 3.73/0.99  --prep_def_merge                        true
% 3.73/0.99  --prep_def_merge_prop_impl              false
% 3.73/0.99  --prep_def_merge_mbd                    true
% 3.73/0.99  --prep_def_merge_tr_red                 false
% 3.73/0.99  --prep_def_merge_tr_cl                  false
% 3.73/0.99  --smt_preprocessing                     true
% 3.73/0.99  --smt_ac_axioms                         fast
% 3.73/0.99  --preprocessed_out                      false
% 3.73/0.99  --preprocessed_stats                    false
% 3.73/0.99  
% 3.73/0.99  ------ Abstraction refinement Options
% 3.73/0.99  
% 3.73/0.99  --abstr_ref                             []
% 3.73/0.99  --abstr_ref_prep                        false
% 3.73/0.99  --abstr_ref_until_sat                   false
% 3.73/0.99  --abstr_ref_sig_restrict                funpre
% 3.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.99  --abstr_ref_under                       []
% 3.73/0.99  
% 3.73/0.99  ------ SAT Options
% 3.73/0.99  
% 3.73/0.99  --sat_mode                              false
% 3.73/0.99  --sat_fm_restart_options                ""
% 3.73/0.99  --sat_gr_def                            false
% 3.73/0.99  --sat_epr_types                         true
% 3.73/0.99  --sat_non_cyclic_types                  false
% 3.73/0.99  --sat_finite_models                     false
% 3.73/0.99  --sat_fm_lemmas                         false
% 3.73/0.99  --sat_fm_prep                           false
% 3.73/0.99  --sat_fm_uc_incr                        true
% 3.73/0.99  --sat_out_model                         small
% 3.73/0.99  --sat_out_clauses                       false
% 3.73/0.99  
% 3.73/0.99  ------ QBF Options
% 3.73/0.99  
% 3.73/0.99  --qbf_mode                              false
% 3.73/0.99  --qbf_elim_univ                         false
% 3.73/0.99  --qbf_dom_inst                          none
% 3.73/0.99  --qbf_dom_pre_inst                      false
% 3.73/0.99  --qbf_sk_in                             false
% 3.73/0.99  --qbf_pred_elim                         true
% 3.73/0.99  --qbf_split                             512
% 3.73/0.99  
% 3.73/0.99  ------ BMC1 Options
% 3.73/0.99  
% 3.73/0.99  --bmc1_incremental                      false
% 3.73/0.99  --bmc1_axioms                           reachable_all
% 3.73/0.99  --bmc1_min_bound                        0
% 3.73/0.99  --bmc1_max_bound                        -1
% 3.73/0.99  --bmc1_max_bound_default                -1
% 3.73/0.99  --bmc1_symbol_reachability              true
% 3.73/0.99  --bmc1_property_lemmas                  false
% 3.73/0.99  --bmc1_k_induction                      false
% 3.73/0.99  --bmc1_non_equiv_states                 false
% 3.73/0.99  --bmc1_deadlock                         false
% 3.73/0.99  --bmc1_ucm                              false
% 3.73/0.99  --bmc1_add_unsat_core                   none
% 3.73/0.99  --bmc1_unsat_core_children              false
% 3.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.99  --bmc1_out_stat                         full
% 3.73/0.99  --bmc1_ground_init                      false
% 3.73/0.99  --bmc1_pre_inst_next_state              false
% 3.73/0.99  --bmc1_pre_inst_state                   false
% 3.73/0.99  --bmc1_pre_inst_reach_state             false
% 3.73/0.99  --bmc1_out_unsat_core                   false
% 3.73/0.99  --bmc1_aig_witness_out                  false
% 3.73/0.99  --bmc1_verbose                          false
% 3.73/0.99  --bmc1_dump_clauses_tptp                false
% 3.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.99  --bmc1_dump_file                        -
% 3.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.99  --bmc1_ucm_extend_mode                  1
% 3.73/0.99  --bmc1_ucm_init_mode                    2
% 3.73/0.99  --bmc1_ucm_cone_mode                    none
% 3.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.99  --bmc1_ucm_relax_model                  4
% 3.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.99  --bmc1_ucm_layered_model                none
% 3.73/0.99  --bmc1_ucm_max_lemma_size               10
% 3.73/0.99  
% 3.73/0.99  ------ AIG Options
% 3.73/0.99  
% 3.73/0.99  --aig_mode                              false
% 3.73/0.99  
% 3.73/0.99  ------ Instantiation Options
% 3.73/0.99  
% 3.73/0.99  --instantiation_flag                    true
% 3.73/0.99  --inst_sos_flag                         false
% 3.73/0.99  --inst_sos_phase                        true
% 3.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel_side                     num_symb
% 3.73/0.99  --inst_solver_per_active                1400
% 3.73/0.99  --inst_solver_calls_frac                1.
% 3.73/0.99  --inst_passive_queue_type               priority_queues
% 3.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.99  --inst_passive_queues_freq              [25;2]
% 3.73/0.99  --inst_dismatching                      true
% 3.73/0.99  --inst_eager_unprocessed_to_passive     true
% 3.73/0.99  --inst_prop_sim_given                   true
% 3.73/0.99  --inst_prop_sim_new                     false
% 3.73/0.99  --inst_subs_new                         false
% 3.73/0.99  --inst_eq_res_simp                      false
% 3.73/0.99  --inst_subs_given                       false
% 3.73/0.99  --inst_orphan_elimination               true
% 3.73/0.99  --inst_learning_loop_flag               true
% 3.73/0.99  --inst_learning_start                   3000
% 3.73/0.99  --inst_learning_factor                  2
% 3.73/0.99  --inst_start_prop_sim_after_learn       3
% 3.73/0.99  --inst_sel_renew                        solver
% 3.73/0.99  --inst_lit_activity_flag                true
% 3.73/0.99  --inst_restr_to_given                   false
% 3.73/0.99  --inst_activity_threshold               500
% 3.73/0.99  --inst_out_proof                        true
% 3.73/0.99  
% 3.73/0.99  ------ Resolution Options
% 3.73/0.99  
% 3.73/0.99  --resolution_flag                       true
% 3.73/0.99  --res_lit_sel                           adaptive
% 3.73/0.99  --res_lit_sel_side                      none
% 3.73/0.99  --res_ordering                          kbo
% 3.73/0.99  --res_to_prop_solver                    active
% 3.73/0.99  --res_prop_simpl_new                    false
% 3.73/0.99  --res_prop_simpl_given                  true
% 3.73/0.99  --res_passive_queue_type                priority_queues
% 3.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.99  --res_passive_queues_freq               [15;5]
% 3.73/0.99  --res_forward_subs                      full
% 3.73/0.99  --res_backward_subs                     full
% 3.73/0.99  --res_forward_subs_resolution           true
% 3.73/0.99  --res_backward_subs_resolution          true
% 3.73/0.99  --res_orphan_elimination                true
% 3.73/0.99  --res_time_limit                        2.
% 3.73/0.99  --res_out_proof                         true
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Options
% 3.73/0.99  
% 3.73/0.99  --superposition_flag                    true
% 3.73/0.99  --sup_passive_queue_type                priority_queues
% 3.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.99  --demod_completeness_check              fast
% 3.73/0.99  --demod_use_ground                      true
% 3.73/0.99  --sup_to_prop_solver                    passive
% 3.73/0.99  --sup_prop_simpl_new                    true
% 3.73/0.99  --sup_prop_simpl_given                  true
% 3.73/0.99  --sup_fun_splitting                     false
% 3.73/0.99  --sup_smt_interval                      50000
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Simplification Setup
% 3.73/0.99  
% 3.73/0.99  --sup_indices_passive                   []
% 3.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_full_bw                           [BwDemod]
% 3.73/0.99  --sup_immed_triv                        [TrivRules]
% 3.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_immed_bw_main                     []
% 3.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  
% 3.73/0.99  ------ Combination Options
% 3.73/0.99  
% 3.73/0.99  --comb_res_mult                         3
% 3.73/0.99  --comb_sup_mult                         2
% 3.73/0.99  --comb_inst_mult                        10
% 3.73/0.99  
% 3.73/0.99  ------ Debug Options
% 3.73/0.99  
% 3.73/0.99  --dbg_backtrace                         false
% 3.73/0.99  --dbg_dump_prop_clauses                 false
% 3.73/0.99  --dbg_dump_prop_clauses_file            -
% 3.73/0.99  --dbg_out_stat                          false
% 3.73/0.99  ------ Parsing...
% 3.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.99  ------ Proving...
% 3.73/0.99  ------ Problem Properties 
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  clauses                                 29
% 3.73/0.99  conjectures                             10
% 3.73/0.99  EPR                                     8
% 3.73/0.99  Horn                                    24
% 3.73/0.99  unary                                   11
% 3.73/0.99  binary                                  5
% 3.73/0.99  lits                                    90
% 3.73/0.99  lits eq                                 8
% 3.73/0.99  fd_pure                                 0
% 3.73/0.99  fd_pseudo                               0
% 3.73/0.99  fd_cond                                 1
% 3.73/0.99  fd_pseudo_cond                          1
% 3.73/0.99  AC symbols                              0
% 3.73/0.99  
% 3.73/0.99  ------ Schedule dynamic 5 is on 
% 3.73/0.99  
% 3.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ 
% 3.73/0.99  Current options:
% 3.73/0.99  ------ 
% 3.73/0.99  
% 3.73/0.99  ------ Input Options
% 3.73/0.99  
% 3.73/0.99  --out_options                           all
% 3.73/0.99  --tptp_safe_out                         true
% 3.73/0.99  --problem_path                          ""
% 3.73/0.99  --include_path                          ""
% 3.73/0.99  --clausifier                            res/vclausify_rel
% 3.73/0.99  --clausifier_options                    --mode clausify
% 3.73/0.99  --stdin                                 false
% 3.73/0.99  --stats_out                             all
% 3.73/0.99  
% 3.73/0.99  ------ General Options
% 3.73/0.99  
% 3.73/0.99  --fof                                   false
% 3.73/0.99  --time_out_real                         305.
% 3.73/0.99  --time_out_virtual                      -1.
% 3.73/0.99  --symbol_type_check                     false
% 3.73/0.99  --clausify_out                          false
% 3.73/0.99  --sig_cnt_out                           false
% 3.73/0.99  --trig_cnt_out                          false
% 3.73/0.99  --trig_cnt_out_tolerance                1.
% 3.73/0.99  --trig_cnt_out_sk_spl                   false
% 3.73/0.99  --abstr_cl_out                          false
% 3.73/0.99  
% 3.73/0.99  ------ Global Options
% 3.73/0.99  
% 3.73/0.99  --schedule                              default
% 3.73/0.99  --add_important_lit                     false
% 3.73/0.99  --prop_solver_per_cl                    1000
% 3.73/0.99  --min_unsat_core                        false
% 3.73/0.99  --soft_assumptions                      false
% 3.73/0.99  --soft_lemma_size                       3
% 3.73/0.99  --prop_impl_unit_size                   0
% 3.73/0.99  --prop_impl_unit                        []
% 3.73/0.99  --share_sel_clauses                     true
% 3.73/0.99  --reset_solvers                         false
% 3.73/0.99  --bc_imp_inh                            [conj_cone]
% 3.73/0.99  --conj_cone_tolerance                   3.
% 3.73/0.99  --extra_neg_conj                        none
% 3.73/0.99  --large_theory_mode                     true
% 3.73/0.99  --prolific_symb_bound                   200
% 3.73/0.99  --lt_threshold                          2000
% 3.73/0.99  --clause_weak_htbl                      true
% 3.73/0.99  --gc_record_bc_elim                     false
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing Options
% 3.73/0.99  
% 3.73/0.99  --preprocessing_flag                    true
% 3.73/0.99  --time_out_prep_mult                    0.1
% 3.73/0.99  --splitting_mode                        input
% 3.73/0.99  --splitting_grd                         true
% 3.73/0.99  --splitting_cvd                         false
% 3.73/0.99  --splitting_cvd_svl                     false
% 3.73/0.99  --splitting_nvd                         32
% 3.73/0.99  --sub_typing                            true
% 3.73/0.99  --prep_gs_sim                           true
% 3.73/0.99  --prep_unflatten                        true
% 3.73/0.99  --prep_res_sim                          true
% 3.73/0.99  --prep_upred                            true
% 3.73/0.99  --prep_sem_filter                       exhaustive
% 3.73/0.99  --prep_sem_filter_out                   false
% 3.73/0.99  --pred_elim                             true
% 3.73/0.99  --res_sim_input                         true
% 3.73/0.99  --eq_ax_congr_red                       true
% 3.73/0.99  --pure_diseq_elim                       true
% 3.73/0.99  --brand_transform                       false
% 3.73/0.99  --non_eq_to_eq                          false
% 3.73/0.99  --prep_def_merge                        true
% 3.73/0.99  --prep_def_merge_prop_impl              false
% 3.73/0.99  --prep_def_merge_mbd                    true
% 3.73/0.99  --prep_def_merge_tr_red                 false
% 3.73/0.99  --prep_def_merge_tr_cl                  false
% 3.73/0.99  --smt_preprocessing                     true
% 3.73/0.99  --smt_ac_axioms                         fast
% 3.73/0.99  --preprocessed_out                      false
% 3.73/0.99  --preprocessed_stats                    false
% 3.73/0.99  
% 3.73/0.99  ------ Abstraction refinement Options
% 3.73/0.99  
% 3.73/0.99  --abstr_ref                             []
% 3.73/0.99  --abstr_ref_prep                        false
% 3.73/0.99  --abstr_ref_until_sat                   false
% 3.73/0.99  --abstr_ref_sig_restrict                funpre
% 3.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.73/0.99  --abstr_ref_under                       []
% 3.73/0.99  
% 3.73/0.99  ------ SAT Options
% 3.73/0.99  
% 3.73/0.99  --sat_mode                              false
% 3.73/0.99  --sat_fm_restart_options                ""
% 3.73/0.99  --sat_gr_def                            false
% 3.73/0.99  --sat_epr_types                         true
% 3.73/0.99  --sat_non_cyclic_types                  false
% 3.73/0.99  --sat_finite_models                     false
% 3.73/0.99  --sat_fm_lemmas                         false
% 3.73/0.99  --sat_fm_prep                           false
% 3.73/0.99  --sat_fm_uc_incr                        true
% 3.73/0.99  --sat_out_model                         small
% 3.73/0.99  --sat_out_clauses                       false
% 3.73/0.99  
% 3.73/0.99  ------ QBF Options
% 3.73/0.99  
% 3.73/0.99  --qbf_mode                              false
% 3.73/0.99  --qbf_elim_univ                         false
% 3.73/0.99  --qbf_dom_inst                          none
% 3.73/0.99  --qbf_dom_pre_inst                      false
% 3.73/0.99  --qbf_sk_in                             false
% 3.73/0.99  --qbf_pred_elim                         true
% 3.73/0.99  --qbf_split                             512
% 3.73/0.99  
% 3.73/0.99  ------ BMC1 Options
% 3.73/0.99  
% 3.73/0.99  --bmc1_incremental                      false
% 3.73/0.99  --bmc1_axioms                           reachable_all
% 3.73/0.99  --bmc1_min_bound                        0
% 3.73/0.99  --bmc1_max_bound                        -1
% 3.73/0.99  --bmc1_max_bound_default                -1
% 3.73/0.99  --bmc1_symbol_reachability              true
% 3.73/0.99  --bmc1_property_lemmas                  false
% 3.73/0.99  --bmc1_k_induction                      false
% 3.73/0.99  --bmc1_non_equiv_states                 false
% 3.73/0.99  --bmc1_deadlock                         false
% 3.73/0.99  --bmc1_ucm                              false
% 3.73/0.99  --bmc1_add_unsat_core                   none
% 3.73/0.99  --bmc1_unsat_core_children              false
% 3.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.73/0.99  --bmc1_out_stat                         full
% 3.73/0.99  --bmc1_ground_init                      false
% 3.73/0.99  --bmc1_pre_inst_next_state              false
% 3.73/0.99  --bmc1_pre_inst_state                   false
% 3.73/0.99  --bmc1_pre_inst_reach_state             false
% 3.73/0.99  --bmc1_out_unsat_core                   false
% 3.73/0.99  --bmc1_aig_witness_out                  false
% 3.73/0.99  --bmc1_verbose                          false
% 3.73/0.99  --bmc1_dump_clauses_tptp                false
% 3.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.73/0.99  --bmc1_dump_file                        -
% 3.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.73/0.99  --bmc1_ucm_extend_mode                  1
% 3.73/0.99  --bmc1_ucm_init_mode                    2
% 3.73/0.99  --bmc1_ucm_cone_mode                    none
% 3.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.73/0.99  --bmc1_ucm_relax_model                  4
% 3.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.73/0.99  --bmc1_ucm_layered_model                none
% 3.73/0.99  --bmc1_ucm_max_lemma_size               10
% 3.73/0.99  
% 3.73/0.99  ------ AIG Options
% 3.73/0.99  
% 3.73/0.99  --aig_mode                              false
% 3.73/0.99  
% 3.73/0.99  ------ Instantiation Options
% 3.73/0.99  
% 3.73/0.99  --instantiation_flag                    true
% 3.73/0.99  --inst_sos_flag                         false
% 3.73/0.99  --inst_sos_phase                        true
% 3.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.73/0.99  --inst_lit_sel_side                     none
% 3.73/0.99  --inst_solver_per_active                1400
% 3.73/0.99  --inst_solver_calls_frac                1.
% 3.73/0.99  --inst_passive_queue_type               priority_queues
% 3.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.73/0.99  --inst_passive_queues_freq              [25;2]
% 3.73/0.99  --inst_dismatching                      true
% 3.73/0.99  --inst_eager_unprocessed_to_passive     true
% 3.73/0.99  --inst_prop_sim_given                   true
% 3.73/0.99  --inst_prop_sim_new                     false
% 3.73/0.99  --inst_subs_new                         false
% 3.73/0.99  --inst_eq_res_simp                      false
% 3.73/0.99  --inst_subs_given                       false
% 3.73/0.99  --inst_orphan_elimination               true
% 3.73/0.99  --inst_learning_loop_flag               true
% 3.73/0.99  --inst_learning_start                   3000
% 3.73/0.99  --inst_learning_factor                  2
% 3.73/0.99  --inst_start_prop_sim_after_learn       3
% 3.73/0.99  --inst_sel_renew                        solver
% 3.73/0.99  --inst_lit_activity_flag                true
% 3.73/0.99  --inst_restr_to_given                   false
% 3.73/0.99  --inst_activity_threshold               500
% 3.73/0.99  --inst_out_proof                        true
% 3.73/0.99  
% 3.73/0.99  ------ Resolution Options
% 3.73/0.99  
% 3.73/0.99  --resolution_flag                       false
% 3.73/0.99  --res_lit_sel                           adaptive
% 3.73/0.99  --res_lit_sel_side                      none
% 3.73/0.99  --res_ordering                          kbo
% 3.73/0.99  --res_to_prop_solver                    active
% 3.73/0.99  --res_prop_simpl_new                    false
% 3.73/0.99  --res_prop_simpl_given                  true
% 3.73/0.99  --res_passive_queue_type                priority_queues
% 3.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.73/0.99  --res_passive_queues_freq               [15;5]
% 3.73/0.99  --res_forward_subs                      full
% 3.73/0.99  --res_backward_subs                     full
% 3.73/0.99  --res_forward_subs_resolution           true
% 3.73/0.99  --res_backward_subs_resolution          true
% 3.73/0.99  --res_orphan_elimination                true
% 3.73/0.99  --res_time_limit                        2.
% 3.73/0.99  --res_out_proof                         true
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Options
% 3.73/0.99  
% 3.73/0.99  --superposition_flag                    true
% 3.73/0.99  --sup_passive_queue_type                priority_queues
% 3.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.73/0.99  --demod_completeness_check              fast
% 3.73/0.99  --demod_use_ground                      true
% 3.73/0.99  --sup_to_prop_solver                    passive
% 3.73/0.99  --sup_prop_simpl_new                    true
% 3.73/0.99  --sup_prop_simpl_given                  true
% 3.73/0.99  --sup_fun_splitting                     false
% 3.73/0.99  --sup_smt_interval                      50000
% 3.73/0.99  
% 3.73/0.99  ------ Superposition Simplification Setup
% 3.73/0.99  
% 3.73/0.99  --sup_indices_passive                   []
% 3.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_full_bw                           [BwDemod]
% 3.73/0.99  --sup_immed_triv                        [TrivRules]
% 3.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_immed_bw_main                     []
% 3.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.73/0.99  
% 3.73/0.99  ------ Combination Options
% 3.73/0.99  
% 3.73/0.99  --comb_res_mult                         3
% 3.73/0.99  --comb_sup_mult                         2
% 3.73/0.99  --comb_inst_mult                        10
% 3.73/0.99  
% 3.73/0.99  ------ Debug Options
% 3.73/0.99  
% 3.73/0.99  --dbg_backtrace                         false
% 3.73/0.99  --dbg_dump_prop_clauses                 false
% 3.73/0.99  --dbg_dump_prop_clauses_file            -
% 3.73/0.99  --dbg_out_stat                          false
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  ------ Proving...
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS status Theorem for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  fof(f17,conjecture,(
% 3.73/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f18,negated_conjecture,(
% 3.73/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.73/0.99    inference(negated_conjecture,[],[f17])).
% 3.73/0.99  
% 3.73/0.99  fof(f44,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f18])).
% 3.73/0.99  
% 3.73/0.99  fof(f45,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.73/0.99    inference(flattening,[],[f44])).
% 3.73/0.99  
% 3.73/0.99  fof(f52,plain,(
% 3.73/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f51,plain,(
% 3.73/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k7_partfun1(X2,sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f50,plain,(
% 3.73/0.99    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f49,plain,(
% 3.73/0.99    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f48,plain,(
% 3.73/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.73/0.99    introduced(choice_axiom,[])).
% 3.73/0.99  
% 3.73/0.99  fof(f53,plain,(
% 3.73/0.99    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f45,f52,f51,f50,f49,f48])).
% 3.73/0.99  
% 3.73/0.99  fof(f84,plain,(
% 3.73/0.99    m1_subset_1(sK5,sK1)),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f81,plain,(
% 3.73/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f8,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f27,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.99    inference(ennf_transformation,[],[f8])).
% 3.73/0.99  
% 3.73/0.99  fof(f63,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f27])).
% 3.73/0.99  
% 3.73/0.99  fof(f83,plain,(
% 3.73/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f6,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f25,plain,(
% 3.73/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.99    inference(ennf_transformation,[],[f6])).
% 3.73/0.99  
% 3.73/0.99  fof(f60,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f25])).
% 3.73/0.99  
% 3.73/0.99  fof(f12,axiom,(
% 3.73/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f34,plain,(
% 3.73/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.73/0.99    inference(ennf_transformation,[],[f12])).
% 3.73/0.99  
% 3.73/0.99  fof(f35,plain,(
% 3.73/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.73/0.99    inference(flattening,[],[f34])).
% 3.73/0.99  
% 3.73/0.99  fof(f47,plain,(
% 3.73/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.73/0.99    inference(nnf_transformation,[],[f35])).
% 3.73/0.99  
% 3.73/0.99  fof(f69,plain,(
% 3.73/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f47])).
% 3.73/0.99  
% 3.73/0.99  fof(f5,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f24,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.99    inference(ennf_transformation,[],[f5])).
% 3.73/0.99  
% 3.73/0.99  fof(f59,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f24])).
% 3.73/0.99  
% 3.73/0.99  fof(f85,plain,(
% 3.73/0.99    v1_partfun1(sK4,sK0)),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f7,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f26,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.99    inference(ennf_transformation,[],[f7])).
% 3.73/0.99  
% 3.73/0.99  fof(f62,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f26])).
% 3.73/0.99  
% 3.73/0.99  fof(f16,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f42,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.73/0.99    inference(ennf_transformation,[],[f16])).
% 3.73/0.99  
% 3.73/0.99  fof(f43,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.73/0.99    inference(flattening,[],[f42])).
% 3.73/0.99  
% 3.73/0.99  fof(f76,plain,(
% 3.73/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f43])).
% 3.73/0.99  
% 3.73/0.99  fof(f77,plain,(
% 3.73/0.99    ~v1_xboole_0(sK0)),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f82,plain,(
% 3.73/0.99    v1_funct_1(sK4)),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f79,plain,(
% 3.73/0.99    v1_funct_1(sK3)),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f80,plain,(
% 3.73/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f61,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f25])).
% 3.73/0.99  
% 3.73/0.99  fof(f3,axiom,(
% 3.73/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f21,plain,(
% 3.73/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.73/0.99    inference(ennf_transformation,[],[f3])).
% 3.73/0.99  
% 3.73/0.99  fof(f46,plain,(
% 3.73/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.73/0.99    inference(nnf_transformation,[],[f21])).
% 3.73/0.99  
% 3.73/0.99  fof(f56,plain,(
% 3.73/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f46])).
% 3.73/0.99  
% 3.73/0.99  fof(f13,axiom,(
% 3.73/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f36,plain,(
% 3.73/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.73/0.99    inference(ennf_transformation,[],[f13])).
% 3.73/0.99  
% 3.73/0.99  fof(f37,plain,(
% 3.73/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.73/0.99    inference(flattening,[],[f36])).
% 3.73/0.99  
% 3.73/0.99  fof(f73,plain,(
% 3.73/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f37])).
% 3.73/0.99  
% 3.73/0.99  fof(f14,axiom,(
% 3.73/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f38,plain,(
% 3.73/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f14])).
% 3.73/0.99  
% 3.73/0.99  fof(f39,plain,(
% 3.73/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.73/0.99    inference(flattening,[],[f38])).
% 3.73/0.99  
% 3.73/0.99  fof(f74,plain,(
% 3.73/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f39])).
% 3.73/0.99  
% 3.73/0.99  fof(f71,plain,(
% 3.73/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f37])).
% 3.73/0.99  
% 3.73/0.99  fof(f72,plain,(
% 3.73/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f37])).
% 3.73/0.99  
% 3.73/0.99  fof(f78,plain,(
% 3.73/0.99    ~v1_xboole_0(sK1)),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f11,axiom,(
% 3.73/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f32,plain,(
% 3.73/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.73/0.99    inference(ennf_transformation,[],[f11])).
% 3.73/0.99  
% 3.73/0.99  fof(f33,plain,(
% 3.73/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.73/0.99    inference(flattening,[],[f32])).
% 3.73/0.99  
% 3.73/0.99  fof(f68,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f33])).
% 3.73/0.99  
% 3.73/0.99  fof(f2,axiom,(
% 3.73/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f19,plain,(
% 3.73/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.73/0.99    inference(ennf_transformation,[],[f2])).
% 3.73/0.99  
% 3.73/0.99  fof(f20,plain,(
% 3.73/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.73/0.99    inference(flattening,[],[f19])).
% 3.73/0.99  
% 3.73/0.99  fof(f55,plain,(
% 3.73/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f20])).
% 3.73/0.99  
% 3.73/0.99  fof(f4,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f22,plain,(
% 3.73/0.99    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 3.73/0.99    inference(ennf_transformation,[],[f4])).
% 3.73/0.99  
% 3.73/0.99  fof(f23,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 3.73/0.99    inference(flattening,[],[f22])).
% 3.73/0.99  
% 3.73/0.99  fof(f58,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f23])).
% 3.73/0.99  
% 3.73/0.99  fof(f15,axiom,(
% 3.73/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f40,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.73/0.99    inference(ennf_transformation,[],[f15])).
% 3.73/0.99  
% 3.73/0.99  fof(f41,plain,(
% 3.73/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.73/0.99    inference(flattening,[],[f40])).
% 3.73/0.99  
% 3.73/0.99  fof(f75,plain,(
% 3.73/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f41])).
% 3.73/0.99  
% 3.73/0.99  fof(f9,axiom,(
% 3.73/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f28,plain,(
% 3.73/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.99    inference(ennf_transformation,[],[f9])).
% 3.73/0.99  
% 3.73/0.99  fof(f29,plain,(
% 3.73/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.99    inference(flattening,[],[f28])).
% 3.73/0.99  
% 3.73/0.99  fof(f65,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.99    inference(cnf_transformation,[],[f29])).
% 3.73/0.99  
% 3.73/0.99  fof(f10,axiom,(
% 3.73/0.99    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f30,plain,(
% 3.73/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.73/0.99    inference(ennf_transformation,[],[f10])).
% 3.73/0.99  
% 3.73/0.99  fof(f31,plain,(
% 3.73/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.73/0.99    inference(flattening,[],[f30])).
% 3.73/0.99  
% 3.73/0.99  fof(f66,plain,(
% 3.73/0.99    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.73/0.99    inference(cnf_transformation,[],[f31])).
% 3.73/0.99  
% 3.73/0.99  fof(f86,plain,(
% 3.73/0.99    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 3.73/0.99    inference(cnf_transformation,[],[f53])).
% 3.73/0.99  
% 3.73/0.99  fof(f1,axiom,(
% 3.73/0.99    v1_xboole_0(k1_xboole_0)),
% 3.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/0.99  
% 3.73/0.99  fof(f54,plain,(
% 3.73/0.99    v1_xboole_0(k1_xboole_0)),
% 3.73/0.99    inference(cnf_transformation,[],[f1])).
% 3.73/0.99  
% 3.73/0.99  cnf(c_25,negated_conjecture,
% 3.73/0.99      ( m1_subset_1(sK5,sK1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1824,plain,
% 3.73/0.99      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_28,negated_conjecture,
% 3.73/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.73/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1821,plain,
% 3.73/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_9,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1835,plain,
% 3.73/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.73/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2571,plain,
% 3.73/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1821,c_1835]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_26,negated_conjecture,
% 3.73/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.73/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1823,plain,
% 3.73/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_7,plain,
% 3.73/0.99      ( v4_relat_1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.73/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_16,plain,
% 3.73/0.99      ( ~ v1_partfun1(X0,X1)
% 3.73/0.99      | ~ v4_relat_1(X0,X1)
% 3.73/0.99      | ~ v1_relat_1(X0)
% 3.73/0.99      | k1_relat_1(X0) = X1 ),
% 3.73/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_370,plain,
% 3.73/0.99      ( ~ v1_partfun1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_relat_1(X0)
% 3.73/0.99      | k1_relat_1(X0) = X1 ),
% 3.73/0.99      inference(resolution,[status(thm)],[c_7,c_16]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | v1_relat_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_374,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_partfun1(X0,X1)
% 3.73/0.99      | k1_relat_1(X0) = X1 ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_370,c_16,c_7,c_5]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_375,plain,
% 3.73/0.99      ( ~ v1_partfun1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | k1_relat_1(X0) = X1 ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_374]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1815,plain,
% 3.73/0.99      ( k1_relat_1(X0) = X1
% 3.73/0.99      | v1_partfun1(X0,X1) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2604,plain,
% 3.73/0.99      ( k1_relat_1(sK4) = sK0 | v1_partfun1(sK4,sK0) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1823,c_1815]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_24,negated_conjecture,
% 3.73/0.99      ( v1_partfun1(sK4,sK0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2137,plain,
% 3.73/0.99      ( ~ v1_partfun1(sK4,sK0)
% 3.73/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.73/0.99      | k1_relat_1(sK4) = sK0 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_375]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2284,plain,
% 3.73/0.99      ( ~ v1_partfun1(sK4,sK0)
% 3.73/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.73/0.99      | k1_relat_1(sK4) = sK0 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2137]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2852,plain,
% 3.73/0.99      ( k1_relat_1(sK4) = sK0 ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_2604,c_26,c_24,c_2284]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_8,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1836,plain,
% 3.73/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.73/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2679,plain,
% 3.73/0.99      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1823,c_1836]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2855,plain,
% 3.73/0.99      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_2852,c_2679]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_22,plain,
% 3.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 3.73/0.99      | ~ m1_subset_1(X5,X1)
% 3.73/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_funct_1(X4)
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | v1_xboole_0(X2)
% 3.73/0.99      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 3.73/0.99      | k1_xboole_0 = X1 ),
% 3.73/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1826,plain,
% 3.73/0.99      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.73/0.99      | k1_xboole_0 = X0
% 3.73/0.99      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.73/0.99      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.73/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.73/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/0.99      | v1_funct_1(X4) != iProver_top
% 3.73/0.99      | v1_funct_1(X3) != iProver_top
% 3.73/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4319,plain,
% 3.73/0.99      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 3.73/0.99      | k1_xboole_0 = X0
% 3.73/0.99      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.73/0.99      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.73/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.73/0.99      | v1_funct_1(X1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK4) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_2855,c_1826]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_32,negated_conjecture,
% 3.73/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_33,plain,
% 3.73/0.99      ( v1_xboole_0(sK0) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_27,negated_conjecture,
% 3.73/0.99      ( v1_funct_1(sK4) ),
% 3.73/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_38,plain,
% 3.73/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_39,plain,
% 3.73/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_9795,plain,
% 3.73/0.99      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.73/0.99      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.73/0.99      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.73/0.99      | k1_xboole_0 = X0
% 3.73/0.99      | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 3.73/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_4319,c_33,c_38,c_39]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_9796,plain,
% 3.73/0.99      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))
% 3.73/0.99      | k1_xboole_0 = X0
% 3.73/0.99      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.73/0.99      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.73/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_9795]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_9808,plain,
% 3.73/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | sK1 = k1_xboole_0
% 3.73/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.73/0.99      | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.73/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_2571,c_9796]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_30,negated_conjecture,
% 3.73/0.99      ( v1_funct_1(sK3) ),
% 3.73/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_35,plain,
% 3.73/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_29,negated_conjecture,
% 3.73/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_36,plain,
% 3.73/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_37,plain,
% 3.73/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2090,plain,
% 3.73/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.73/0.99      | v1_relat_1(sK3) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2091,plain,
% 3.73/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.73/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2090]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_6,plain,
% 3.73/0.99      ( v5_relat_1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.73/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2111,plain,
% 3.73/0.99      ( v5_relat_1(sK3,sK0)
% 3.73/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2112,plain,
% 3.73/0.99      ( v5_relat_1(sK3,sK0) = iProver_top
% 3.73/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2111]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3,plain,
% 3.73/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.73/0.99      | ~ v5_relat_1(X0,X1)
% 3.73/0.99      | ~ v1_relat_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2269,plain,
% 3.73/0.99      ( r1_tarski(k2_relat_1(sK3),X0)
% 3.73/0.99      | ~ v5_relat_1(sK3,X0)
% 3.73/0.99      | ~ v1_relat_1(sK3) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2275,plain,
% 3.73/0.99      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 3.73/0.99      | v5_relat_1(sK3,X0) != iProver_top
% 3.73/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2269]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2277,plain,
% 3.73/0.99      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.73/0.99      | v5_relat_1(sK3,sK0) != iProver_top
% 3.73/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2275]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_10237,plain,
% 3.73/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | sK1 = k1_xboole_0
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_9808,c_35,c_36,c_37,c_2091,c_2112,c_2277]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_10247,plain,
% 3.73/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 3.73/0.99      | sK1 = k1_xboole_0 ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1824,c_10237]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_17,plain,
% 3.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.73/0.99      | ~ v1_funct_1(X3)
% 3.73/0.99      | ~ v1_funct_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1831,plain,
% 3.73/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 3.73/0.99      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
% 3.73/0.99      | v1_funct_1(X0) != iProver_top
% 3.73/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_20,plain,
% 3.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.99      | ~ m1_subset_1(X3,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | v1_xboole_0(X1)
% 3.73/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.73/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1828,plain,
% 3.73/0.99      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.73/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.73/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/0.99      | v1_funct_1(X2) != iProver_top
% 3.73/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4552,plain,
% 3.73/0.99      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.73/0.99      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.73/0.99      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 3.73/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.73/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.73/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.73/0.99      | v1_funct_1(X3) != iProver_top
% 3.73/0.99      | v1_funct_1(X4) != iProver_top
% 3.73/0.99      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 3.73/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1831,c_1828]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_19,plain,
% 3.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_funct_1(X3)
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 3.73/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1829,plain,
% 3.73/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 3.73/0.99      | v1_funct_1(X0) != iProver_top
% 3.73/0.99      | v1_funct_1(X3) != iProver_top
% 3.73/0.99      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_18,plain,
% 3.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.99      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 3.73/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_funct_1(X4)
% 3.73/0.99      | ~ v1_funct_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1830,plain,
% 3.73/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.73/0.99      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
% 3.73/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.99      | v1_funct_1(X4) != iProver_top
% 3.73/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11457,plain,
% 3.73/0.99      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.73/0.99      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.73/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.73/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.73/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.73/0.99      | v1_funct_1(X4) != iProver_top
% 3.73/0.99      | v1_funct_1(X3) != iProver_top
% 3.73/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.73/0.99      inference(forward_subsumption_resolution,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_4552,c_1829,c_1830]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11464,plain,
% 3.73/0.99      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.73/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(X1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK3) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1821,c_11457]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_31,negated_conjecture,
% 3.73/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_34,plain,
% 3.73/0.99      ( v1_xboole_0(sK1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11662,plain,
% 3.73/0.99      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_11464,c_34,c_35,c_36]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11674,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1823,c_11662]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11723,plain,
% 3.73/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_11674,c_38]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11724,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_11723]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11732,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1824,c_11724]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2605,plain,
% 3.73/0.99      ( k1_relat_1(sK3) = sK1 | v1_partfun1(sK3,sK1) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1821,c_1815]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_13,plain,
% 3.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.99      | v1_partfun1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | v1_xboole_0(X2) ),
% 3.73/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2175,plain,
% 3.73/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 3.73/0.99      | v1_partfun1(sK3,X0)
% 3.73/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/0.99      | ~ v1_funct_1(sK3)
% 3.73/0.99      | v1_xboole_0(X1) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2350,plain,
% 3.73/0.99      ( ~ v1_funct_2(sK3,sK1,sK0)
% 3.73/0.99      | v1_partfun1(sK3,sK1)
% 3.73/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.73/0.99      | ~ v1_funct_1(sK3)
% 3.73/0.99      | v1_xboole_0(sK0) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2175]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2553,plain,
% 3.73/0.99      ( ~ v1_partfun1(sK3,sK1)
% 3.73/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
% 3.73/0.99      | k1_relat_1(sK3) = sK1 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_375]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2555,plain,
% 3.73/0.99      ( ~ v1_partfun1(sK3,sK1)
% 3.73/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.73/0.99      | k1_relat_1(sK3) = sK1 ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2553]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2859,plain,
% 3.73/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_2605,c_32,c_30,c_29,c_28,c_2350,c_2555]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1,plain,
% 3.73/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4,plain,
% 3.73/0.99      ( ~ v5_relat_1(X0,X1)
% 3.73/0.99      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 3.73/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | ~ v1_relat_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_339,plain,
% 3.73/0.99      ( ~ v5_relat_1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X2,X3)
% 3.73/0.99      | m1_subset_1(k1_funct_1(X0,X4),X1)
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | ~ v1_relat_1(X0)
% 3.73/0.99      | v1_xboole_0(X3)
% 3.73/0.99      | X4 != X2
% 3.73/0.99      | k1_relat_1(X0) != X3 ),
% 3.73/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_340,plain,
% 3.73/0.99      ( ~ v5_relat_1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X2,k1_relat_1(X0))
% 3.73/0.99      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | ~ v1_relat_1(X0)
% 3.73/0.99      | v1_xboole_0(k1_relat_1(X0)) ),
% 3.73/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1816,plain,
% 3.73/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,k1_relat_1(X0)) != iProver_top
% 3.73/0.99      | m1_subset_1(k1_funct_1(X0,X2),X1) = iProver_top
% 3.73/0.99      | v1_funct_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_21,plain,
% 3.73/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.99      | ~ m1_subset_1(X3,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_funct_1(X0)
% 3.73/0.99      | v1_xboole_0(X2)
% 3.73/0.99      | v1_xboole_0(X1)
% 3.73/0.99      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 3.73/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1827,plain,
% 3.73/0.99      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
% 3.73/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.73/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.73/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.73/0.99      | v1_funct_1(X2) != iProver_top
% 3.73/0.99      | v1_xboole_0(X1) = iProver_top
% 3.73/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4440,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 3.73/0.99      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.73/0.99      | v1_funct_1(sK4) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK0) = iProver_top
% 3.73/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1823,c_1827]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_41,plain,
% 3.73/0.99      ( v1_partfun1(sK4,sK0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_10,plain,
% 3.73/0.99      ( v1_funct_2(X0,X1,X2)
% 3.73/0.99      | ~ v1_partfun1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_funct_1(X0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2164,plain,
% 3.73/0.99      ( v1_funct_2(sK4,X0,X1)
% 3.73/0.99      | ~ v1_partfun1(sK4,X0)
% 3.73/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.73/0.99      | ~ v1_funct_1(sK4) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2341,plain,
% 3.73/0.99      ( v1_funct_2(sK4,sK0,sK2)
% 3.73/0.99      | ~ v1_partfun1(sK4,sK0)
% 3.73/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.73/0.99      | ~ v1_funct_1(sK4) ),
% 3.73/0.99      inference(instantiation,[status(thm)],[c_2164]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2342,plain,
% 3.73/0.99      ( v1_funct_2(sK4,sK0,sK2) = iProver_top
% 3.73/0.99      | v1_partfun1(sK4,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.73/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2341]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_12,plain,
% 3.73/0.99      ( ~ v1_partfun1(X0,X1)
% 3.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.99      | ~ v1_xboole_0(X2)
% 3.73/0.99      | v1_xboole_0(X1) ),
% 3.73/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1833,plain,
% 3.73/0.99      ( v1_partfun1(X0,X1) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.99      | v1_xboole_0(X2) != iProver_top
% 3.73/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_2822,plain,
% 3.73/0.99      ( v1_partfun1(sK4,sK0) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK0) = iProver_top
% 3.73/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1823,c_1833]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4733,plain,
% 3.73/0.99      ( m1_subset_1(X0,sK0) != iProver_top
% 3.73/0.99      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_4440,c_33,c_38,c_39,c_41,c_2342,c_2822]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4734,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 3.73/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_4733]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4741,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(X0,X1)) = k7_partfun1(sK2,sK4,k1_funct_1(X0,X1))
% 3.73/0.99      | v5_relat_1(X0,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X1,k1_relat_1(X0)) != iProver_top
% 3.73/0.99      | v1_funct_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1816,c_4734]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5313,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | v5_relat_1(sK3,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK3) != iProver_top
% 3.73/0.99      | v1_relat_1(sK3) != iProver_top
% 3.73/0.99      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_2859,c_4741]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5320,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | v5_relat_1(sK3,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK3) != iProver_top
% 3.73/0.99      | v1_relat_1(sK3) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.73/0.99      inference(light_normalisation,[status(thm)],[c_5313,c_2859]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5370,plain,
% 3.73/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_5320,c_34,c_35,c_37,c_2091,c_2112]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5371,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_5370]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5379,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1824,c_5371]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3618,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 3.73/0.99      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.73/0.99      | v1_funct_1(sK4) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1823,c_1828]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3928,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 3.73/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_3618,c_33,c_38,c_39,c_41,c_2342]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3936,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(X0,X1)) = k1_funct_1(sK4,k1_funct_1(X0,X1))
% 3.73/0.99      | v5_relat_1(X0,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X1,k1_relat_1(X0)) != iProver_top
% 3.73/0.99      | v1_funct_1(X0) != iProver_top
% 3.73/0.99      | v1_relat_1(X0) != iProver_top
% 3.73/0.99      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1816,c_3928]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4185,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | v5_relat_1(sK3,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK3) != iProver_top
% 3.73/0.99      | v1_relat_1(sK3) != iProver_top
% 3.73/0.99      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_2859,c_3936]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4192,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | v5_relat_1(sK3,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK3) != iProver_top
% 3.73/0.99      | v1_relat_1(sK3) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.73/0.99      inference(light_normalisation,[status(thm)],[c_4185,c_2859]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4242,plain,
% 3.73/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_4192,c_34,c_35,c_37,c_2091,c_2112]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4243,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.73/0.99      inference(renaming,[status(thm)],[c_4242]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4251,plain,
% 3.73/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1824,c_4243]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5381,plain,
% 3.73/0.99      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.73/0.99      inference(light_normalisation,[status(thm)],[c_5379,c_4251]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3619,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 3.73/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.73/0.99      | v1_funct_1(sK3) != iProver_top
% 3.73/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1821,c_1828]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3941,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 3.73/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.73/0.99      inference(global_propositional_subsumption,
% 3.73/0.99                [status(thm)],
% 3.73/0.99                [c_3619,c_34,c_35,c_36]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_3950,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_1824,c_3941]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_23,negated_conjecture,
% 3.73/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 3.73/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_4121,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_3950,c_23]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_5427,plain,
% 3.73/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_5381,c_4121]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11751,plain,
% 3.73/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_11732,c_5427]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11753,plain,
% 3.73/0.99      ( sK1 = k1_xboole_0 ),
% 3.73/0.99      inference(superposition,[status(thm)],[c_10247,c_11751]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_1818,plain,
% 3.73/0.99      ( v1_xboole_0(sK1) != iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_11954,plain,
% 3.73/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.73/0.99      inference(demodulation,[status(thm)],[c_11753,c_1818]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_0,plain,
% 3.73/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.73/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(c_102,plain,
% 3.73/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.73/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/0.99  
% 3.73/0.99  cnf(contradiction,plain,
% 3.73/0.99      ( $false ),
% 3.73/0.99      inference(minisat,[status(thm)],[c_11954,c_102]) ).
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.99  
% 3.73/0.99  ------                               Statistics
% 3.73/0.99  
% 3.73/0.99  ------ General
% 3.73/0.99  
% 3.73/0.99  abstr_ref_over_cycles:                  0
% 3.73/0.99  abstr_ref_under_cycles:                 0
% 3.73/0.99  gc_basic_clause_elim:                   0
% 3.73/0.99  forced_gc_time:                         0
% 3.73/0.99  parsing_time:                           0.01
% 3.73/0.99  unif_index_cands_time:                  0.
% 3.73/0.99  unif_index_add_time:                    0.
% 3.73/0.99  orderings_time:                         0.
% 3.73/0.99  out_proof_time:                         0.015
% 3.73/0.99  total_time:                             0.483
% 3.73/0.99  num_of_symbols:                         58
% 3.73/0.99  num_of_terms:                           16690
% 3.73/0.99  
% 3.73/0.99  ------ Preprocessing
% 3.73/0.99  
% 3.73/0.99  num_of_splits:                          0
% 3.73/0.99  num_of_split_atoms:                     0
% 3.73/0.99  num_of_reused_defs:                     0
% 3.73/0.99  num_eq_ax_congr_red:                    35
% 3.73/0.99  num_of_sem_filtered_clauses:            1
% 3.73/0.99  num_of_subtypes:                        0
% 3.73/0.99  monotx_restored_types:                  0
% 3.73/0.99  sat_num_of_epr_types:                   0
% 3.73/0.99  sat_num_of_non_cyclic_types:            0
% 3.73/0.99  sat_guarded_non_collapsed_types:        0
% 3.73/0.99  num_pure_diseq_elim:                    0
% 3.73/0.99  simp_replaced_by:                       0
% 3.73/0.99  res_preprocessed:                       147
% 3.73/0.99  prep_upred:                             0
% 3.73/0.99  prep_unflattend:                        30
% 3.73/0.99  smt_new_axioms:                         0
% 3.73/0.99  pred_elim_cands:                        8
% 3.73/0.99  pred_elim:                              2
% 3.73/0.99  pred_elim_cl:                           2
% 3.73/0.99  pred_elim_cycles:                       10
% 3.73/0.99  merged_defs:                            0
% 3.73/0.99  merged_defs_ncl:                        0
% 3.73/0.99  bin_hyper_res:                          0
% 3.73/0.99  prep_cycles:                            4
% 3.73/0.99  pred_elim_time:                         0.014
% 3.73/0.99  splitting_time:                         0.
% 3.73/0.99  sem_filter_time:                        0.
% 3.73/0.99  monotx_time:                            0.001
% 3.73/0.99  subtype_inf_time:                       0.
% 3.73/0.99  
% 3.73/0.99  ------ Problem properties
% 3.73/0.99  
% 3.73/0.99  clauses:                                29
% 3.73/0.99  conjectures:                            10
% 3.73/0.99  epr:                                    8
% 3.73/0.99  horn:                                   24
% 3.73/0.99  ground:                                 11
% 3.73/0.99  unary:                                  11
% 3.73/0.99  binary:                                 5
% 3.73/0.99  lits:                                   90
% 3.73/0.99  lits_eq:                                8
% 3.73/0.99  fd_pure:                                0
% 3.73/0.99  fd_pseudo:                              0
% 3.73/0.99  fd_cond:                                1
% 3.73/0.99  fd_pseudo_cond:                         1
% 3.73/0.99  ac_symbols:                             0
% 3.73/0.99  
% 3.73/0.99  ------ Propositional Solver
% 3.73/0.99  
% 3.73/0.99  prop_solver_calls:                      29
% 3.73/0.99  prop_fast_solver_calls:                 2140
% 3.73/0.99  smt_solver_calls:                       0
% 3.73/0.99  smt_fast_solver_calls:                  0
% 3.73/0.99  prop_num_of_clauses:                    4869
% 3.73/0.99  prop_preprocess_simplified:             9616
% 3.73/0.99  prop_fo_subsumed:                       128
% 3.73/0.99  prop_solver_time:                       0.
% 3.73/0.99  smt_solver_time:                        0.
% 3.73/0.99  smt_fast_solver_time:                   0.
% 3.73/0.99  prop_fast_solver_time:                  0.
% 3.73/0.99  prop_unsat_core_time:                   0.
% 3.73/0.99  
% 3.73/0.99  ------ QBF
% 3.73/0.99  
% 3.73/0.99  qbf_q_res:                              0
% 3.73/0.99  qbf_num_tautologies:                    0
% 3.73/0.99  qbf_prep_cycles:                        0
% 3.73/0.99  
% 3.73/0.99  ------ BMC1
% 3.73/0.99  
% 3.73/0.99  bmc1_current_bound:                     -1
% 3.73/0.99  bmc1_last_solved_bound:                 -1
% 3.73/0.99  bmc1_unsat_core_size:                   -1
% 3.73/0.99  bmc1_unsat_core_parents_size:           -1
% 3.73/0.99  bmc1_merge_next_fun:                    0
% 3.73/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.73/0.99  
% 3.73/0.99  ------ Instantiation
% 3.73/0.99  
% 3.73/0.99  inst_num_of_clauses:                    1049
% 3.73/0.99  inst_num_in_passive:                    23
% 3.73/0.99  inst_num_in_active:                     704
% 3.73/0.99  inst_num_in_unprocessed:                322
% 3.73/0.99  inst_num_of_loops:                      730
% 3.73/0.99  inst_num_of_learning_restarts:          0
% 3.73/0.99  inst_num_moves_active_passive:          22
% 3.73/0.99  inst_lit_activity:                      0
% 3.73/0.99  inst_lit_activity_moves:                0
% 3.73/0.99  inst_num_tautologies:                   0
% 3.73/0.99  inst_num_prop_implied:                  0
% 3.73/0.99  inst_num_existing_simplified:           0
% 3.73/0.99  inst_num_eq_res_simplified:             0
% 3.73/0.99  inst_num_child_elim:                    0
% 3.73/0.99  inst_num_of_dismatching_blockings:      67
% 3.73/0.99  inst_num_of_non_proper_insts:           826
% 3.73/0.99  inst_num_of_duplicates:                 0
% 3.73/0.99  inst_inst_num_from_inst_to_res:         0
% 3.73/0.99  inst_dismatching_checking_time:         0.
% 3.73/0.99  
% 3.73/0.99  ------ Resolution
% 3.73/0.99  
% 3.73/0.99  res_num_of_clauses:                     0
% 3.73/0.99  res_num_in_passive:                     0
% 3.73/0.99  res_num_in_active:                      0
% 3.73/0.99  res_num_of_loops:                       151
% 3.73/0.99  res_forward_subset_subsumed:            48
% 3.73/0.99  res_backward_subset_subsumed:           0
% 3.73/0.99  res_forward_subsumed:                   0
% 3.73/0.99  res_backward_subsumed:                  0
% 3.73/0.99  res_forward_subsumption_resolution:     2
% 3.73/0.99  res_backward_subsumption_resolution:    0
% 3.73/0.99  res_clause_to_clause_subsumption:       2121
% 3.73/0.99  res_orphan_elimination:                 0
% 3.73/0.99  res_tautology_del:                      68
% 3.73/0.99  res_num_eq_res_simplified:              0
% 3.73/0.99  res_num_sel_changes:                    0
% 3.73/0.99  res_moves_from_active_to_pass:          0
% 3.73/0.99  
% 3.73/0.99  ------ Superposition
% 3.73/0.99  
% 3.73/0.99  sup_time_total:                         0.
% 3.73/0.99  sup_time_generating:                    0.
% 3.73/0.99  sup_time_sim_full:                      0.
% 3.73/0.99  sup_time_sim_immed:                     0.
% 3.73/0.99  
% 3.73/0.99  sup_num_of_clauses:                     223
% 3.73/0.99  sup_num_in_active:                      78
% 3.73/0.99  sup_num_in_passive:                     145
% 3.73/0.99  sup_num_of_loops:                       144
% 3.73/0.99  sup_fw_superposition:                   179
% 3.73/0.99  sup_bw_superposition:                   31
% 3.73/0.99  sup_immediate_simplified:               25
% 3.73/0.99  sup_given_eliminated:                   0
% 3.73/0.99  comparisons_done:                       0
% 3.73/0.99  comparisons_avoided:                    15
% 3.73/0.99  
% 3.73/0.99  ------ Simplifications
% 3.73/0.99  
% 3.73/0.99  
% 3.73/0.99  sim_fw_subset_subsumed:                 4
% 3.73/0.99  sim_bw_subset_subsumed:                 2
% 3.73/0.99  sim_fw_subsumed:                        4
% 3.73/0.99  sim_bw_subsumed:                        0
% 3.73/0.99  sim_fw_subsumption_res:                 27
% 3.73/0.99  sim_bw_subsumption_res:                 0
% 3.73/0.99  sim_tautology_del:                      2
% 3.73/0.99  sim_eq_tautology_del:                   4
% 3.73/0.99  sim_eq_res_simp:                        0
% 3.73/0.99  sim_fw_demodulated:                     0
% 3.73/0.99  sim_bw_demodulated:                     65
% 3.73/0.99  sim_light_normalised:                   18
% 3.73/0.99  sim_joinable_taut:                      0
% 3.73/0.99  sim_joinable_simp:                      0
% 3.73/0.99  sim_ac_normalised:                      0
% 3.73/0.99  sim_smt_subsumption:                    0
% 3.73/0.99  
%------------------------------------------------------------------------------
