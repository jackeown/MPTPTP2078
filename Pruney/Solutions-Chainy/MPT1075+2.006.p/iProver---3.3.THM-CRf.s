%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:19 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  207 (1607 expanded)
%              Number of clauses        :  131 ( 412 expanded)
%              Number of leaves         :   21 ( 597 expanded)
%              Depth                    :   25
%              Number of atoms          :  800 (12913 expanded)
%              Number of equality atoms :  338 (2069 expanded)
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

fof(f78,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f75,plain,(
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

fof(f77,plain,(
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

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
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

fof(f70,plain,(
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

fof(f71,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
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

fof(f11,axiom,(
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

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
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

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1210,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1207,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1219,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1830,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1207,c_1219])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1209,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1222,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2044,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1222])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1659,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_1660,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1659])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1929,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1930,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_2335,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2044,c_38,c_1660,c_1930])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,negated_conjecture,
    ( v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_446,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_23])).

cnf(c_447,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_447])).

cnf(c_486,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK0 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_714,plain,
    ( ~ v1_relat_1(sK4)
    | sP0_iProver_split
    | k1_relat_1(sK4) = sK0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_486])).

cnf(c_1198,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_2340,plain,
    ( k1_relat_1(sK4) = sK0
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_2335,c_1198])).

cnf(c_746,plain,
    ( k1_relat_1(sK4) = sK0
    | v1_relat_1(sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_713,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_486])).

cnf(c_1199,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_1937,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1199])).

cnf(c_3317,plain,
    ( k1_relat_1(sK4) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2340,c_38,c_746,c_1660,c_1930,c_1937])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1220,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1948,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1209,c_1220])).

cnf(c_3320,plain,
    ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
    inference(demodulation,[status(thm)],[c_3317,c_1948])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_1211,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3493,plain,
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
    inference(superposition,[status(thm)],[c_3320,c_1211])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7609,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3493,c_32,c_37,c_38])).

cnf(c_7610,plain,
    ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7609])).

cnf(c_7622,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_7610])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1662,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_1663,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1662])).

cnf(c_1939,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1940,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1939])).

cnf(c_5,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_325,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_5,c_3])).

cnf(c_1202,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_2552,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1202])).

cnf(c_9016,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
    | sK1 = k1_xboole_0
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7622,c_34,c_35,c_36,c_1663,c_1940,c_2552])).

cnf(c_9026,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1210,c_9016])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1217,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1214,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2915,plain,
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
    inference(superposition,[status(thm)],[c_1217,c_1214])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1215,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1216,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9957,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2915,c_1215,c_1216])).

cnf(c_9964,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_9957])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10146,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9964,c_33,c_34,c_35])).

cnf(c_10158,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_10146])).

cnf(c_10272,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10158,c_37])).

cnf(c_10273,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10272])).

cnf(c_10281,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1210,c_10273])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1212,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2914,plain,
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
    inference(superposition,[status(thm)],[c_1217,c_1212])).

cnf(c_9106,plain,
    ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
    | v1_funct_2(X3,X0,X2) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2914,c_1215,c_1216])).

cnf(c_9113,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_9106])).

cnf(c_9409,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9113,c_33,c_34,c_35])).

cnf(c_9410,plain,
    ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9409])).

cnf(c_9422,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_9410])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | sK4 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_460,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_462,plain,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_31])).

cnf(c_463,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_1200,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_1896,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1200])).

cnf(c_9477,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9422,c_37,c_1896])).

cnf(c_9486,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_1210,c_9477])).

cnf(c_10300,plain,
    ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    inference(demodulation,[status(thm)],[c_10281,c_9486])).

cnf(c_2178,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1214])).

cnf(c_2422,plain,
    ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2178,c_33,c_34,c_35])).

cnf(c_2431,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1210,c_2422])).

cnf(c_22,negated_conjecture,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2450,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2431,c_22])).

cnf(c_9544,plain,
    ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_9486,c_2450])).

cnf(c_10355,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_10300,c_9544])).

cnf(c_10362,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9026,c_10355])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1218,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2451,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_1218])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3468,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_33,c_34,c_35,c_36,c_39])).

cnf(c_2815,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1212])).

cnf(c_18,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X2,X0) != X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1213,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2061,plain,
    ( k1_relat_1(sK4) != sK0
    | v1_funct_2(sK4,sK0,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1948,c_1213])).

cnf(c_3075,plain,
    ( m1_subset_1(X0,sK0) != iProver_top
    | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2815,c_32,c_37,c_38,c_746,c_1660,c_1896,c_1930,c_1937,c_2061])).

cnf(c_3076,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3075])).

cnf(c_3473,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3468,c_3076])).

cnf(c_2177,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | v1_funct_2(sK4,sK0,sK2) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1214])).

cnf(c_2381,plain,
    ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2177,c_32,c_37,c_38,c_746,c_1660,c_1930,c_1937,c_2061])).

cnf(c_3474,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3468,c_2381])).

cnf(c_3477,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_3473,c_3474])).

cnf(c_10403,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10362,c_3477])).

cnf(c_1204,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10463,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10403,c_1204])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_96,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10463,c_96])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:45:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.90/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.99  
% 3.90/0.99  ------  iProver source info
% 3.90/0.99  
% 3.90/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.99  git: non_committed_changes: false
% 3.90/0.99  git: last_make_outside_of_git: false
% 3.90/0.99  
% 3.90/0.99  ------ 
% 3.90/0.99  
% 3.90/0.99  ------ Input Options
% 3.90/0.99  
% 3.90/0.99  --out_options                           all
% 3.90/0.99  --tptp_safe_out                         true
% 3.90/0.99  --problem_path                          ""
% 3.90/0.99  --include_path                          ""
% 3.90/0.99  --clausifier                            res/vclausify_rel
% 3.90/0.99  --clausifier_options                    --mode clausify
% 3.90/0.99  --stdin                                 false
% 3.90/0.99  --stats_out                             all
% 3.90/0.99  
% 3.90/0.99  ------ General Options
% 3.90/0.99  
% 3.90/0.99  --fof                                   false
% 3.90/0.99  --time_out_real                         305.
% 3.90/0.99  --time_out_virtual                      -1.
% 3.90/0.99  --symbol_type_check                     false
% 3.90/0.99  --clausify_out                          false
% 3.90/0.99  --sig_cnt_out                           false
% 3.90/0.99  --trig_cnt_out                          false
% 3.90/0.99  --trig_cnt_out_tolerance                1.
% 3.90/0.99  --trig_cnt_out_sk_spl                   false
% 3.90/0.99  --abstr_cl_out                          false
% 3.90/0.99  
% 3.90/0.99  ------ Global Options
% 3.90/0.99  
% 3.90/0.99  --schedule                              default
% 3.90/0.99  --add_important_lit                     false
% 3.90/0.99  --prop_solver_per_cl                    1000
% 3.90/0.99  --min_unsat_core                        false
% 3.90/0.99  --soft_assumptions                      false
% 3.90/0.99  --soft_lemma_size                       3
% 3.90/0.99  --prop_impl_unit_size                   0
% 3.90/0.99  --prop_impl_unit                        []
% 3.90/0.99  --share_sel_clauses                     true
% 3.90/0.99  --reset_solvers                         false
% 3.90/0.99  --bc_imp_inh                            [conj_cone]
% 3.90/0.99  --conj_cone_tolerance                   3.
% 3.90/0.99  --extra_neg_conj                        none
% 3.90/0.99  --large_theory_mode                     true
% 3.90/0.99  --prolific_symb_bound                   200
% 3.90/0.99  --lt_threshold                          2000
% 3.90/0.99  --clause_weak_htbl                      true
% 3.90/0.99  --gc_record_bc_elim                     false
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing Options
% 3.90/0.99  
% 3.90/0.99  --preprocessing_flag                    true
% 3.90/0.99  --time_out_prep_mult                    0.1
% 3.90/0.99  --splitting_mode                        input
% 3.90/0.99  --splitting_grd                         true
% 3.90/0.99  --splitting_cvd                         false
% 3.90/0.99  --splitting_cvd_svl                     false
% 3.90/0.99  --splitting_nvd                         32
% 3.90/0.99  --sub_typing                            true
% 3.90/0.99  --prep_gs_sim                           true
% 3.90/0.99  --prep_unflatten                        true
% 3.90/0.99  --prep_res_sim                          true
% 3.90/0.99  --prep_upred                            true
% 3.90/0.99  --prep_sem_filter                       exhaustive
% 3.90/0.99  --prep_sem_filter_out                   false
% 3.90/0.99  --pred_elim                             true
% 3.90/0.99  --res_sim_input                         true
% 3.90/0.99  --eq_ax_congr_red                       true
% 3.90/0.99  --pure_diseq_elim                       true
% 3.90/0.99  --brand_transform                       false
% 3.90/0.99  --non_eq_to_eq                          false
% 3.90/0.99  --prep_def_merge                        true
% 3.90/0.99  --prep_def_merge_prop_impl              false
% 3.90/0.99  --prep_def_merge_mbd                    true
% 3.90/0.99  --prep_def_merge_tr_red                 false
% 3.90/0.99  --prep_def_merge_tr_cl                  false
% 3.90/0.99  --smt_preprocessing                     true
% 3.90/0.99  --smt_ac_axioms                         fast
% 3.90/0.99  --preprocessed_out                      false
% 3.90/0.99  --preprocessed_stats                    false
% 3.90/0.99  
% 3.90/0.99  ------ Abstraction refinement Options
% 3.90/0.99  
% 3.90/0.99  --abstr_ref                             []
% 3.90/0.99  --abstr_ref_prep                        false
% 3.90/0.99  --abstr_ref_until_sat                   false
% 3.90/0.99  --abstr_ref_sig_restrict                funpre
% 3.90/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/0.99  --abstr_ref_under                       []
% 3.90/0.99  
% 3.90/0.99  ------ SAT Options
% 3.90/0.99  
% 3.90/0.99  --sat_mode                              false
% 3.90/0.99  --sat_fm_restart_options                ""
% 3.90/0.99  --sat_gr_def                            false
% 3.90/0.99  --sat_epr_types                         true
% 3.90/0.99  --sat_non_cyclic_types                  false
% 3.90/0.99  --sat_finite_models                     false
% 3.90/0.99  --sat_fm_lemmas                         false
% 3.90/0.99  --sat_fm_prep                           false
% 3.90/0.99  --sat_fm_uc_incr                        true
% 3.90/0.99  --sat_out_model                         small
% 3.90/0.99  --sat_out_clauses                       false
% 3.90/0.99  
% 3.90/0.99  ------ QBF Options
% 3.90/0.99  
% 3.90/0.99  --qbf_mode                              false
% 3.90/0.99  --qbf_elim_univ                         false
% 3.90/0.99  --qbf_dom_inst                          none
% 3.90/0.99  --qbf_dom_pre_inst                      false
% 3.90/0.99  --qbf_sk_in                             false
% 3.90/0.99  --qbf_pred_elim                         true
% 3.90/0.99  --qbf_split                             512
% 3.90/0.99  
% 3.90/0.99  ------ BMC1 Options
% 3.90/0.99  
% 3.90/0.99  --bmc1_incremental                      false
% 3.90/0.99  --bmc1_axioms                           reachable_all
% 3.90/0.99  --bmc1_min_bound                        0
% 3.90/0.99  --bmc1_max_bound                        -1
% 3.90/0.99  --bmc1_max_bound_default                -1
% 3.90/0.99  --bmc1_symbol_reachability              true
% 3.90/0.99  --bmc1_property_lemmas                  false
% 3.90/0.99  --bmc1_k_induction                      false
% 3.90/0.99  --bmc1_non_equiv_states                 false
% 3.90/0.99  --bmc1_deadlock                         false
% 3.90/0.99  --bmc1_ucm                              false
% 3.90/0.99  --bmc1_add_unsat_core                   none
% 3.90/0.99  --bmc1_unsat_core_children              false
% 3.90/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/0.99  --bmc1_out_stat                         full
% 3.90/0.99  --bmc1_ground_init                      false
% 3.90/0.99  --bmc1_pre_inst_next_state              false
% 3.90/0.99  --bmc1_pre_inst_state                   false
% 3.90/0.99  --bmc1_pre_inst_reach_state             false
% 3.90/0.99  --bmc1_out_unsat_core                   false
% 3.90/0.99  --bmc1_aig_witness_out                  false
% 3.90/0.99  --bmc1_verbose                          false
% 3.90/0.99  --bmc1_dump_clauses_tptp                false
% 3.90/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.90/0.99  --bmc1_dump_file                        -
% 3.90/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.90/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.90/0.99  --bmc1_ucm_extend_mode                  1
% 3.90/0.99  --bmc1_ucm_init_mode                    2
% 3.90/0.99  --bmc1_ucm_cone_mode                    none
% 3.90/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.90/0.99  --bmc1_ucm_relax_model                  4
% 3.90/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.90/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/0.99  --bmc1_ucm_layered_model                none
% 3.90/0.99  --bmc1_ucm_max_lemma_size               10
% 3.90/0.99  
% 3.90/0.99  ------ AIG Options
% 3.90/0.99  
% 3.90/0.99  --aig_mode                              false
% 3.90/0.99  
% 3.90/0.99  ------ Instantiation Options
% 3.90/0.99  
% 3.90/0.99  --instantiation_flag                    true
% 3.90/0.99  --inst_sos_flag                         false
% 3.90/0.99  --inst_sos_phase                        true
% 3.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/0.99  --inst_lit_sel_side                     num_symb
% 3.90/0.99  --inst_solver_per_active                1400
% 3.90/0.99  --inst_solver_calls_frac                1.
% 3.90/0.99  --inst_passive_queue_type               priority_queues
% 3.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/0.99  --inst_passive_queues_freq              [25;2]
% 3.90/0.99  --inst_dismatching                      true
% 3.90/0.99  --inst_eager_unprocessed_to_passive     true
% 3.90/0.99  --inst_prop_sim_given                   true
% 3.90/0.99  --inst_prop_sim_new                     false
% 3.90/0.99  --inst_subs_new                         false
% 3.90/0.99  --inst_eq_res_simp                      false
% 3.90/0.99  --inst_subs_given                       false
% 3.90/0.99  --inst_orphan_elimination               true
% 3.90/0.99  --inst_learning_loop_flag               true
% 3.90/0.99  --inst_learning_start                   3000
% 3.90/0.99  --inst_learning_factor                  2
% 3.90/0.99  --inst_start_prop_sim_after_learn       3
% 3.90/0.99  --inst_sel_renew                        solver
% 3.90/0.99  --inst_lit_activity_flag                true
% 3.90/0.99  --inst_restr_to_given                   false
% 3.90/0.99  --inst_activity_threshold               500
% 3.90/0.99  --inst_out_proof                        true
% 3.90/0.99  
% 3.90/0.99  ------ Resolution Options
% 3.90/0.99  
% 3.90/0.99  --resolution_flag                       true
% 3.90/0.99  --res_lit_sel                           adaptive
% 3.90/0.99  --res_lit_sel_side                      none
% 3.90/0.99  --res_ordering                          kbo
% 3.90/0.99  --res_to_prop_solver                    active
% 3.90/0.99  --res_prop_simpl_new                    false
% 3.90/0.99  --res_prop_simpl_given                  true
% 3.90/0.99  --res_passive_queue_type                priority_queues
% 3.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/0.99  --res_passive_queues_freq               [15;5]
% 3.90/0.99  --res_forward_subs                      full
% 3.90/0.99  --res_backward_subs                     full
% 3.90/0.99  --res_forward_subs_resolution           true
% 3.90/0.99  --res_backward_subs_resolution          true
% 3.90/0.99  --res_orphan_elimination                true
% 3.90/0.99  --res_time_limit                        2.
% 3.90/0.99  --res_out_proof                         true
% 3.90/0.99  
% 3.90/0.99  ------ Superposition Options
% 3.90/0.99  
% 3.90/0.99  --superposition_flag                    true
% 3.90/0.99  --sup_passive_queue_type                priority_queues
% 3.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.90/0.99  --demod_completeness_check              fast
% 3.90/0.99  --demod_use_ground                      true
% 3.90/0.99  --sup_to_prop_solver                    passive
% 3.90/0.99  --sup_prop_simpl_new                    true
% 3.90/0.99  --sup_prop_simpl_given                  true
% 3.90/0.99  --sup_fun_splitting                     false
% 3.90/0.99  --sup_smt_interval                      50000
% 3.90/0.99  
% 3.90/0.99  ------ Superposition Simplification Setup
% 3.90/0.99  
% 3.90/0.99  --sup_indices_passive                   []
% 3.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.99  --sup_full_bw                           [BwDemod]
% 3.90/0.99  --sup_immed_triv                        [TrivRules]
% 3.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.99  --sup_immed_bw_main                     []
% 3.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.99  
% 3.90/0.99  ------ Combination Options
% 3.90/0.99  
% 3.90/0.99  --comb_res_mult                         3
% 3.90/0.99  --comb_sup_mult                         2
% 3.90/0.99  --comb_inst_mult                        10
% 3.90/0.99  
% 3.90/0.99  ------ Debug Options
% 3.90/0.99  
% 3.90/0.99  --dbg_backtrace                         false
% 3.90/0.99  --dbg_dump_prop_clauses                 false
% 3.90/0.99  --dbg_dump_prop_clauses_file            -
% 3.90/0.99  --dbg_out_stat                          false
% 3.90/0.99  ------ Parsing...
% 3.90/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.99  ------ Proving...
% 3.90/0.99  ------ Problem Properties 
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  clauses                                 27
% 3.90/0.99  conjectures                             9
% 3.90/0.99  EPR                                     7
% 3.90/0.99  Horn                                    22
% 3.90/0.99  unary                                   11
% 3.90/0.99  binary                                  4
% 3.90/0.99  lits                                    83
% 3.90/0.99  lits eq                                 9
% 3.90/0.99  fd_pure                                 0
% 3.90/0.99  fd_pseudo                               0
% 3.90/0.99  fd_cond                                 1
% 3.90/0.99  fd_pseudo_cond                          0
% 3.90/0.99  AC symbols                              0
% 3.90/0.99  
% 3.90/0.99  ------ Schedule dynamic 5 is on 
% 3.90/0.99  
% 3.90/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ 
% 3.90/0.99  Current options:
% 3.90/0.99  ------ 
% 3.90/0.99  
% 3.90/0.99  ------ Input Options
% 3.90/0.99  
% 3.90/0.99  --out_options                           all
% 3.90/0.99  --tptp_safe_out                         true
% 3.90/0.99  --problem_path                          ""
% 3.90/0.99  --include_path                          ""
% 3.90/0.99  --clausifier                            res/vclausify_rel
% 3.90/0.99  --clausifier_options                    --mode clausify
% 3.90/0.99  --stdin                                 false
% 3.90/0.99  --stats_out                             all
% 3.90/0.99  
% 3.90/0.99  ------ General Options
% 3.90/0.99  
% 3.90/0.99  --fof                                   false
% 3.90/0.99  --time_out_real                         305.
% 3.90/0.99  --time_out_virtual                      -1.
% 3.90/0.99  --symbol_type_check                     false
% 3.90/0.99  --clausify_out                          false
% 3.90/0.99  --sig_cnt_out                           false
% 3.90/0.99  --trig_cnt_out                          false
% 3.90/0.99  --trig_cnt_out_tolerance                1.
% 3.90/0.99  --trig_cnt_out_sk_spl                   false
% 3.90/0.99  --abstr_cl_out                          false
% 3.90/0.99  
% 3.90/0.99  ------ Global Options
% 3.90/0.99  
% 3.90/0.99  --schedule                              default
% 3.90/0.99  --add_important_lit                     false
% 3.90/0.99  --prop_solver_per_cl                    1000
% 3.90/0.99  --min_unsat_core                        false
% 3.90/0.99  --soft_assumptions                      false
% 3.90/0.99  --soft_lemma_size                       3
% 3.90/0.99  --prop_impl_unit_size                   0
% 3.90/0.99  --prop_impl_unit                        []
% 3.90/0.99  --share_sel_clauses                     true
% 3.90/0.99  --reset_solvers                         false
% 3.90/0.99  --bc_imp_inh                            [conj_cone]
% 3.90/0.99  --conj_cone_tolerance                   3.
% 3.90/0.99  --extra_neg_conj                        none
% 3.90/0.99  --large_theory_mode                     true
% 3.90/0.99  --prolific_symb_bound                   200
% 3.90/0.99  --lt_threshold                          2000
% 3.90/0.99  --clause_weak_htbl                      true
% 3.90/0.99  --gc_record_bc_elim                     false
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing Options
% 3.90/0.99  
% 3.90/0.99  --preprocessing_flag                    true
% 3.90/0.99  --time_out_prep_mult                    0.1
% 3.90/0.99  --splitting_mode                        input
% 3.90/0.99  --splitting_grd                         true
% 3.90/0.99  --splitting_cvd                         false
% 3.90/0.99  --splitting_cvd_svl                     false
% 3.90/0.99  --splitting_nvd                         32
% 3.90/0.99  --sub_typing                            true
% 3.90/0.99  --prep_gs_sim                           true
% 3.90/0.99  --prep_unflatten                        true
% 3.90/0.99  --prep_res_sim                          true
% 3.90/0.99  --prep_upred                            true
% 3.90/0.99  --prep_sem_filter                       exhaustive
% 3.90/0.99  --prep_sem_filter_out                   false
% 3.90/0.99  --pred_elim                             true
% 3.90/0.99  --res_sim_input                         true
% 3.90/0.99  --eq_ax_congr_red                       true
% 3.90/0.99  --pure_diseq_elim                       true
% 3.90/0.99  --brand_transform                       false
% 3.90/0.99  --non_eq_to_eq                          false
% 3.90/0.99  --prep_def_merge                        true
% 3.90/0.99  --prep_def_merge_prop_impl              false
% 3.90/0.99  --prep_def_merge_mbd                    true
% 3.90/0.99  --prep_def_merge_tr_red                 false
% 3.90/0.99  --prep_def_merge_tr_cl                  false
% 3.90/0.99  --smt_preprocessing                     true
% 3.90/0.99  --smt_ac_axioms                         fast
% 3.90/0.99  --preprocessed_out                      false
% 3.90/0.99  --preprocessed_stats                    false
% 3.90/0.99  
% 3.90/0.99  ------ Abstraction refinement Options
% 3.90/0.99  
% 3.90/0.99  --abstr_ref                             []
% 3.90/0.99  --abstr_ref_prep                        false
% 3.90/0.99  --abstr_ref_until_sat                   false
% 3.90/0.99  --abstr_ref_sig_restrict                funpre
% 3.90/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/0.99  --abstr_ref_under                       []
% 3.90/0.99  
% 3.90/0.99  ------ SAT Options
% 3.90/0.99  
% 3.90/0.99  --sat_mode                              false
% 3.90/0.99  --sat_fm_restart_options                ""
% 3.90/0.99  --sat_gr_def                            false
% 3.90/0.99  --sat_epr_types                         true
% 3.90/0.99  --sat_non_cyclic_types                  false
% 3.90/0.99  --sat_finite_models                     false
% 3.90/0.99  --sat_fm_lemmas                         false
% 3.90/0.99  --sat_fm_prep                           false
% 3.90/0.99  --sat_fm_uc_incr                        true
% 3.90/0.99  --sat_out_model                         small
% 3.90/0.99  --sat_out_clauses                       false
% 3.90/0.99  
% 3.90/0.99  ------ QBF Options
% 3.90/0.99  
% 3.90/0.99  --qbf_mode                              false
% 3.90/0.99  --qbf_elim_univ                         false
% 3.90/0.99  --qbf_dom_inst                          none
% 3.90/0.99  --qbf_dom_pre_inst                      false
% 3.90/0.99  --qbf_sk_in                             false
% 3.90/0.99  --qbf_pred_elim                         true
% 3.90/0.99  --qbf_split                             512
% 3.90/0.99  
% 3.90/0.99  ------ BMC1 Options
% 3.90/0.99  
% 3.90/0.99  --bmc1_incremental                      false
% 3.90/0.99  --bmc1_axioms                           reachable_all
% 3.90/0.99  --bmc1_min_bound                        0
% 3.90/0.99  --bmc1_max_bound                        -1
% 3.90/0.99  --bmc1_max_bound_default                -1
% 3.90/0.99  --bmc1_symbol_reachability              true
% 3.90/0.99  --bmc1_property_lemmas                  false
% 3.90/0.99  --bmc1_k_induction                      false
% 3.90/0.99  --bmc1_non_equiv_states                 false
% 3.90/0.99  --bmc1_deadlock                         false
% 3.90/0.99  --bmc1_ucm                              false
% 3.90/0.99  --bmc1_add_unsat_core                   none
% 3.90/0.99  --bmc1_unsat_core_children              false
% 3.90/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/0.99  --bmc1_out_stat                         full
% 3.90/0.99  --bmc1_ground_init                      false
% 3.90/0.99  --bmc1_pre_inst_next_state              false
% 3.90/0.99  --bmc1_pre_inst_state                   false
% 3.90/0.99  --bmc1_pre_inst_reach_state             false
% 3.90/0.99  --bmc1_out_unsat_core                   false
% 3.90/0.99  --bmc1_aig_witness_out                  false
% 3.90/0.99  --bmc1_verbose                          false
% 3.90/0.99  --bmc1_dump_clauses_tptp                false
% 3.90/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.90/0.99  --bmc1_dump_file                        -
% 3.90/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.90/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.90/0.99  --bmc1_ucm_extend_mode                  1
% 3.90/0.99  --bmc1_ucm_init_mode                    2
% 3.90/0.99  --bmc1_ucm_cone_mode                    none
% 3.90/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.90/0.99  --bmc1_ucm_relax_model                  4
% 3.90/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.90/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/0.99  --bmc1_ucm_layered_model                none
% 3.90/0.99  --bmc1_ucm_max_lemma_size               10
% 3.90/0.99  
% 3.90/0.99  ------ AIG Options
% 3.90/0.99  
% 3.90/0.99  --aig_mode                              false
% 3.90/0.99  
% 3.90/0.99  ------ Instantiation Options
% 3.90/0.99  
% 3.90/0.99  --instantiation_flag                    true
% 3.90/0.99  --inst_sos_flag                         false
% 3.90/0.99  --inst_sos_phase                        true
% 3.90/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/0.99  --inst_lit_sel_side                     none
% 3.90/0.99  --inst_solver_per_active                1400
% 3.90/0.99  --inst_solver_calls_frac                1.
% 3.90/0.99  --inst_passive_queue_type               priority_queues
% 3.90/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/0.99  --inst_passive_queues_freq              [25;2]
% 3.90/0.99  --inst_dismatching                      true
% 3.90/0.99  --inst_eager_unprocessed_to_passive     true
% 3.90/0.99  --inst_prop_sim_given                   true
% 3.90/0.99  --inst_prop_sim_new                     false
% 3.90/0.99  --inst_subs_new                         false
% 3.90/0.99  --inst_eq_res_simp                      false
% 3.90/0.99  --inst_subs_given                       false
% 3.90/0.99  --inst_orphan_elimination               true
% 3.90/0.99  --inst_learning_loop_flag               true
% 3.90/0.99  --inst_learning_start                   3000
% 3.90/0.99  --inst_learning_factor                  2
% 3.90/0.99  --inst_start_prop_sim_after_learn       3
% 3.90/0.99  --inst_sel_renew                        solver
% 3.90/0.99  --inst_lit_activity_flag                true
% 3.90/0.99  --inst_restr_to_given                   false
% 3.90/0.99  --inst_activity_threshold               500
% 3.90/0.99  --inst_out_proof                        true
% 3.90/0.99  
% 3.90/0.99  ------ Resolution Options
% 3.90/0.99  
% 3.90/0.99  --resolution_flag                       false
% 3.90/0.99  --res_lit_sel                           adaptive
% 3.90/0.99  --res_lit_sel_side                      none
% 3.90/0.99  --res_ordering                          kbo
% 3.90/0.99  --res_to_prop_solver                    active
% 3.90/0.99  --res_prop_simpl_new                    false
% 3.90/0.99  --res_prop_simpl_given                  true
% 3.90/0.99  --res_passive_queue_type                priority_queues
% 3.90/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/0.99  --res_passive_queues_freq               [15;5]
% 3.90/0.99  --res_forward_subs                      full
% 3.90/0.99  --res_backward_subs                     full
% 3.90/0.99  --res_forward_subs_resolution           true
% 3.90/0.99  --res_backward_subs_resolution          true
% 3.90/0.99  --res_orphan_elimination                true
% 3.90/0.99  --res_time_limit                        2.
% 3.90/0.99  --res_out_proof                         true
% 3.90/0.99  
% 3.90/0.99  ------ Superposition Options
% 3.90/0.99  
% 3.90/0.99  --superposition_flag                    true
% 3.90/0.99  --sup_passive_queue_type                priority_queues
% 3.90/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.90/0.99  --demod_completeness_check              fast
% 3.90/0.99  --demod_use_ground                      true
% 3.90/0.99  --sup_to_prop_solver                    passive
% 3.90/0.99  --sup_prop_simpl_new                    true
% 3.90/0.99  --sup_prop_simpl_given                  true
% 3.90/0.99  --sup_fun_splitting                     false
% 3.90/0.99  --sup_smt_interval                      50000
% 3.90/0.99  
% 3.90/0.99  ------ Superposition Simplification Setup
% 3.90/0.99  
% 3.90/0.99  --sup_indices_passive                   []
% 3.90/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.99  --sup_full_bw                           [BwDemod]
% 3.90/0.99  --sup_immed_triv                        [TrivRules]
% 3.90/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.99  --sup_immed_bw_main                     []
% 3.90/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.99  
% 3.90/0.99  ------ Combination Options
% 3.90/0.99  
% 3.90/0.99  --comb_res_mult                         3
% 3.90/0.99  --comb_sup_mult                         2
% 3.90/0.99  --comb_inst_mult                        10
% 3.90/0.99  
% 3.90/0.99  ------ Debug Options
% 3.90/0.99  
% 3.90/0.99  --dbg_backtrace                         false
% 3.90/0.99  --dbg_dump_prop_clauses                 false
% 3.90/0.99  --dbg_dump_prop_clauses_file            -
% 3.90/0.99  --dbg_out_stat                          false
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  ------ Proving...
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  % SZS status Theorem for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  fof(f16,conjecture,(
% 3.90/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f17,negated_conjecture,(
% 3.90/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 3.90/0.99    inference(negated_conjecture,[],[f16])).
% 3.90/0.99  
% 3.90/0.99  fof(f39,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.90/0.99    inference(ennf_transformation,[],[f17])).
% 3.90/0.99  
% 3.90/0.99  fof(f40,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.90/0.99    inference(flattening,[],[f39])).
% 3.90/0.99  
% 3.90/0.99  fof(f47,plain,(
% 3.90/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) => (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),sK5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,sK5)) & v1_partfun1(X4,X0) & m1_subset_1(sK5,X1))) )),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f46,plain,(
% 3.90/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(sK4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(sK4))) )),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f45,plain,(
% 3.90/0.99    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(X1,sK2,k8_funct_2(X1,X0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,sK3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f44,plain,(
% 3.90/0.99    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) & v1_funct_2(X3,sK1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))) )),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f43,plain,(
% 3.90/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.90/0.99    introduced(choice_axiom,[])).
% 3.90/0.99  
% 3.90/0.99  fof(f48,plain,(
% 3.90/0.99    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.90/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f47,f46,f45,f44,f43])).
% 3.90/0.99  
% 3.90/0.99  fof(f78,plain,(
% 3.90/0.99    m1_subset_1(sK5,sK1)),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f75,plain,(
% 3.90/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f7,axiom,(
% 3.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f22,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.99    inference(ennf_transformation,[],[f7])).
% 3.90/0.99  
% 3.90/0.99  fof(f57,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f22])).
% 3.90/0.99  
% 3.90/0.99  fof(f77,plain,(
% 3.90/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f2,axiom,(
% 3.90/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f18,plain,(
% 3.90/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.90/0.99    inference(ennf_transformation,[],[f2])).
% 3.90/0.99  
% 3.90/0.99  fof(f50,plain,(
% 3.90/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f18])).
% 3.90/0.99  
% 3.90/0.99  fof(f4,axiom,(
% 3.90/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f53,plain,(
% 3.90/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f4])).
% 3.90/0.99  
% 3.90/0.99  fof(f5,axiom,(
% 3.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f20,plain,(
% 3.90/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.99    inference(ennf_transformation,[],[f5])).
% 3.90/0.99  
% 3.90/0.99  fof(f54,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f20])).
% 3.90/0.99  
% 3.90/0.99  fof(f9,axiom,(
% 3.90/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f25,plain,(
% 3.90/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.90/0.99    inference(ennf_transformation,[],[f9])).
% 3.90/0.99  
% 3.90/0.99  fof(f26,plain,(
% 3.90/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.90/0.99    inference(flattening,[],[f25])).
% 3.90/0.99  
% 3.90/0.99  fof(f42,plain,(
% 3.90/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.90/0.99    inference(nnf_transformation,[],[f26])).
% 3.90/0.99  
% 3.90/0.99  fof(f59,plain,(
% 3.90/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f42])).
% 3.90/0.99  
% 3.90/0.99  fof(f79,plain,(
% 3.90/0.99    v1_partfun1(sK4,sK0)),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f6,axiom,(
% 3.90/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f21,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.99    inference(ennf_transformation,[],[f6])).
% 3.90/0.99  
% 3.90/0.99  fof(f56,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f21])).
% 3.90/0.99  
% 3.90/0.99  fof(f15,axiom,(
% 3.90/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f37,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.90/0.99    inference(ennf_transformation,[],[f15])).
% 3.90/0.99  
% 3.90/0.99  fof(f38,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.90/0.99    inference(flattening,[],[f37])).
% 3.90/0.99  
% 3.90/0.99  fof(f70,plain,(
% 3.90/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f38])).
% 3.90/0.99  
% 3.90/0.99  fof(f71,plain,(
% 3.90/0.99    ~v1_xboole_0(sK0)),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f76,plain,(
% 3.90/0.99    v1_funct_1(sK4)),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f73,plain,(
% 3.90/0.99    v1_funct_1(sK3)),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f74,plain,(
% 3.90/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f55,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.99    inference(cnf_transformation,[],[f20])).
% 3.90/0.99  
% 3.90/0.99  fof(f3,axiom,(
% 3.90/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f19,plain,(
% 3.90/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.90/0.99    inference(ennf_transformation,[],[f3])).
% 3.90/0.99  
% 3.90/0.99  fof(f41,plain,(
% 3.90/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.90/0.99    inference(nnf_transformation,[],[f19])).
% 3.90/0.99  
% 3.90/0.99  fof(f51,plain,(
% 3.90/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f41])).
% 3.90/0.99  
% 3.90/0.99  fof(f11,axiom,(
% 3.90/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f29,plain,(
% 3.90/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.90/0.99    inference(ennf_transformation,[],[f11])).
% 3.90/0.99  
% 3.90/0.99  fof(f30,plain,(
% 3.90/0.99    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.90/0.99    inference(flattening,[],[f29])).
% 3.90/0.99  
% 3.90/0.99  fof(f64,plain,(
% 3.90/0.99    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f30])).
% 3.90/0.99  
% 3.90/0.99  fof(f12,axiom,(
% 3.90/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f31,plain,(
% 3.90/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.90/0.99    inference(ennf_transformation,[],[f12])).
% 3.90/0.99  
% 3.90/0.99  fof(f32,plain,(
% 3.90/0.99    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.90/0.99    inference(flattening,[],[f31])).
% 3.90/0.99  
% 3.90/0.99  fof(f65,plain,(
% 3.90/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f32])).
% 3.90/0.99  
% 3.90/0.99  fof(f62,plain,(
% 3.90/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f30])).
% 3.90/0.99  
% 3.90/0.99  fof(f63,plain,(
% 3.90/0.99    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f30])).
% 3.90/0.99  
% 3.90/0.99  fof(f72,plain,(
% 3.90/0.99    ~v1_xboole_0(sK1)),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f14,axiom,(
% 3.90/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f35,plain,(
% 3.90/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.90/0.99    inference(ennf_transformation,[],[f14])).
% 3.90/0.99  
% 3.90/0.99  fof(f36,plain,(
% 3.90/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.90/0.99    inference(flattening,[],[f35])).
% 3.90/0.99  
% 3.90/0.99  fof(f69,plain,(
% 3.90/0.99    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f36])).
% 3.90/0.99  
% 3.90/0.99  fof(f8,axiom,(
% 3.90/0.99    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f23,plain,(
% 3.90/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.90/0.99    inference(ennf_transformation,[],[f8])).
% 3.90/0.99  
% 3.90/0.99  fof(f24,plain,(
% 3.90/0.99    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.90/0.99    inference(flattening,[],[f23])).
% 3.90/0.99  
% 3.90/0.99  fof(f58,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f24])).
% 3.90/0.99  
% 3.90/0.99  fof(f80,plain,(
% 3.90/0.99    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 3.90/0.99    inference(cnf_transformation,[],[f48])).
% 3.90/0.99  
% 3.90/0.99  fof(f10,axiom,(
% 3.90/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f27,plain,(
% 3.90/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.90/0.99    inference(ennf_transformation,[],[f10])).
% 3.90/0.99  
% 3.90/0.99  fof(f28,plain,(
% 3.90/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.90/0.99    inference(flattening,[],[f27])).
% 3.90/0.99  
% 3.90/0.99  fof(f61,plain,(
% 3.90/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f28])).
% 3.90/0.99  
% 3.90/0.99  fof(f13,axiom,(
% 3.90/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f33,plain,(
% 3.90/0.99    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.90/0.99    inference(ennf_transformation,[],[f13])).
% 3.90/0.99  
% 3.90/0.99  fof(f34,plain,(
% 3.90/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.90/0.99    inference(flattening,[],[f33])).
% 3.90/0.99  
% 3.90/0.99  fof(f67,plain,(
% 3.90/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.90/0.99    inference(cnf_transformation,[],[f34])).
% 3.90/0.99  
% 3.90/0.99  fof(f1,axiom,(
% 3.90/0.99    v1_xboole_0(k1_xboole_0)),
% 3.90/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.99  
% 3.90/0.99  fof(f49,plain,(
% 3.90/0.99    v1_xboole_0(k1_xboole_0)),
% 3.90/0.99    inference(cnf_transformation,[],[f1])).
% 3.90/0.99  
% 3.90/0.99  cnf(c_24,negated_conjecture,
% 3.90/0.99      ( m1_subset_1(sK5,sK1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1210,plain,
% 3.90/0.99      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_27,negated_conjecture,
% 3.90/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.90/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1207,plain,
% 3.90/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_8,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1219,plain,
% 3.90/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1830,plain,
% 3.90/0.99      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1207,c_1219]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_25,negated_conjecture,
% 3.90/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.90/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1209,plain,
% 3.90/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/0.99      | ~ v1_relat_1(X1)
% 3.90/0.99      | v1_relat_1(X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1222,plain,
% 3.90/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.90/0.99      | v1_relat_1(X1) != iProver_top
% 3.90/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2044,plain,
% 3.90/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 3.90/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_1222]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_38,plain,
% 3.90/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1454,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | v1_relat_1(X0)
% 3.90/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1659,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.90/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
% 3.90/0.99      | v1_relat_1(sK4) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_1454]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1660,plain,
% 3.90/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.90/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK2)) != iProver_top
% 3.90/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_1659]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_4,plain,
% 3.90/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.90/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1929,plain,
% 3.90/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1930,plain,
% 3.90/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK2)) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2335,plain,
% 3.90/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2044,c_38,c_1660,c_1930]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_6,plain,
% 3.90/0.99      ( v4_relat_1(X0,X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.90/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_11,plain,
% 3.90/0.99      ( ~ v1_partfun1(X0,X1)
% 3.90/0.99      | ~ v4_relat_1(X0,X1)
% 3.90/0.99      | ~ v1_relat_1(X0)
% 3.90/0.99      | k1_relat_1(X0) = X1 ),
% 3.90/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_23,negated_conjecture,
% 3.90/0.99      ( v1_partfun1(sK4,sK0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_446,plain,
% 3.90/0.99      ( ~ v4_relat_1(X0,X1)
% 3.90/0.99      | ~ v1_relat_1(X0)
% 3.90/0.99      | k1_relat_1(X0) = X1
% 3.90/0.99      | sK4 != X0
% 3.90/0.99      | sK0 != X1 ),
% 3.90/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_23]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_447,plain,
% 3.90/0.99      ( ~ v4_relat_1(sK4,sK0)
% 3.90/0.99      | ~ v1_relat_1(sK4)
% 3.90/0.99      | k1_relat_1(sK4) = sK0 ),
% 3.90/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_485,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_relat_1(sK4)
% 3.90/0.99      | k1_relat_1(sK4) = sK0
% 3.90/0.99      | sK4 != X0
% 3.90/0.99      | sK0 != X1 ),
% 3.90/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_447]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_486,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.90/0.99      | ~ v1_relat_1(sK4)
% 3.90/0.99      | k1_relat_1(sK4) = sK0 ),
% 3.90/0.99      inference(unflattening,[status(thm)],[c_485]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_714,plain,
% 3.90/0.99      ( ~ v1_relat_1(sK4) | sP0_iProver_split | k1_relat_1(sK4) = sK0 ),
% 3.90/0.99      inference(splitting,
% 3.90/0.99                [splitting(split),new_symbols(definition,[])],
% 3.90/0.99                [c_486]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1198,plain,
% 3.90/0.99      ( k1_relat_1(sK4) = sK0
% 3.90/0.99      | v1_relat_1(sK4) != iProver_top
% 3.90/0.99      | sP0_iProver_split = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2340,plain,
% 3.90/0.99      ( k1_relat_1(sK4) = sK0 | sP0_iProver_split = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_2335,c_1198]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_746,plain,
% 3.90/0.99      ( k1_relat_1(sK4) = sK0
% 3.90/0.99      | v1_relat_1(sK4) != iProver_top
% 3.90/0.99      | sP0_iProver_split = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_713,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.90/0.99      | ~ sP0_iProver_split ),
% 3.90/0.99      inference(splitting,
% 3.90/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.90/0.99                [c_486]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1199,plain,
% 3.90/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.90/0.99      | sP0_iProver_split != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1937,plain,
% 3.90/0.99      ( sP0_iProver_split != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_1199]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3317,plain,
% 3.90/0.99      ( k1_relat_1(sK4) = sK0 ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2340,c_38,c_746,c_1660,c_1930,c_1937]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_7,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1220,plain,
% 3.90/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1948,plain,
% 3.90/0.99      ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_1220]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3320,plain,
% 3.90/0.99      ( k1_relset_1(sK0,sK2,sK4) = sK0 ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_3317,c_1948]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_21,plain,
% 3.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.99      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 3.90/0.99      | ~ m1_subset_1(X5,X1)
% 3.90/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_funct_1(X4)
% 3.90/0.99      | ~ v1_funct_1(X0)
% 3.90/0.99      | v1_xboole_0(X2)
% 3.90/0.99      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k7_partfun1(X3,X4,k1_funct_1(X0,X5))
% 3.90/0.99      | k1_xboole_0 = X1 ),
% 3.90/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1211,plain,
% 3.90/0.99      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k7_partfun1(X2,X4,k1_funct_1(X3,X5))
% 3.90/0.99      | k1_xboole_0 = X0
% 3.90/0.99      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.90/0.99      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.90/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X4) != iProver_top
% 3.90/0.99      | v1_funct_1(X3) != iProver_top
% 3.90/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3493,plain,
% 3.90/0.99      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
% 3.90/0.99      | k1_xboole_0 = X0
% 3.90/0.99      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.90/0.99      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.90/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.90/0.99      | v1_funct_1(X1) != iProver_top
% 3.90/0.99      | v1_funct_1(sK4) != iProver_top
% 3.90/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_3320,c_1211]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_31,negated_conjecture,
% 3.90/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_32,plain,
% 3.90/0.99      ( v1_xboole_0(sK0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_26,negated_conjecture,
% 3.90/0.99      ( v1_funct_1(sK4) ),
% 3.90/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_37,plain,
% 3.90/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_7609,plain,
% 3.90/0.99      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.90/0.99      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.90/0.99      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.90/0.99      | k1_xboole_0 = X0
% 3.90/0.99      | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
% 3.90/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_3493,c_32,c_37,c_38]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_7610,plain,
% 3.90/0.99      ( k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))
% 3.90/0.99      | k1_xboole_0 = X0
% 3.90/0.99      | v1_funct_2(X1,X0,sK0) != iProver_top
% 3.90/0.99      | r1_tarski(k2_relset_1(X0,sK0,X1),sK0) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.90/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.90/0.99      inference(renaming,[status(thm)],[c_7609]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_7622,plain,
% 3.90/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 3.90/0.99      | sK1 = k1_xboole_0
% 3.90/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.90/0.99      | r1_tarski(k2_relat_1(sK3),sK0) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.90/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.90/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1830,c_7610]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_29,negated_conjecture,
% 3.90/0.99      ( v1_funct_1(sK3) ),
% 3.90/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_34,plain,
% 3.90/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_28,negated_conjecture,
% 3.90/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_35,plain,
% 3.90/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_36,plain,
% 3.90/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1662,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.90/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.90/0.99      | v1_relat_1(sK3) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_1454]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1663,plain,
% 3.90/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.90/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.90/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_1662]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1939,plain,
% 3.90/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.90/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1940,plain,
% 3.90/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_1939]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_5,plain,
% 3.90/0.99      ( v5_relat_1(X0,X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.90/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3,plain,
% 3.90/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.90/0.99      | ~ v5_relat_1(X0,X1)
% 3.90/0.99      | ~ v1_relat_1(X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_325,plain,
% 3.90/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.90/0.99      | ~ v1_relat_1(X0) ),
% 3.90/0.99      inference(resolution,[status(thm)],[c_5,c_3]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1202,plain,
% 3.90/0.99      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.90/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2552,plain,
% 3.90/0.99      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.90/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1207,c_1202]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9016,plain,
% 3.90/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))
% 3.90/0.99      | sK1 = k1_xboole_0
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_7622,c_34,c_35,c_36,c_1663,c_1940,c_2552]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9026,plain,
% 3.90/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
% 3.90/0.99      | sK1 = k1_xboole_0 ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1210,c_9016]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_13,plain,
% 3.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
% 3.90/0.99      | ~ v1_funct_1(X3)
% 3.90/0.99      | ~ v1_funct_1(X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1217,plain,
% 3.90/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 3.90/0.99      | m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) = iProver_top
% 3.90/0.99      | v1_funct_1(X0) != iProver_top
% 3.90/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_16,plain,
% 3.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.99      | ~ m1_subset_1(X3,X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_funct_1(X0)
% 3.90/0.99      | v1_xboole_0(X1)
% 3.90/0.99      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.90/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1214,plain,
% 3.90/0.99      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 3.90/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X2) != iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2915,plain,
% 3.90/0.99      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.90/0.99      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.90/0.99      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 3.90/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X3) != iProver_top
% 3.90/0.99      | v1_funct_1(X4) != iProver_top
% 3.90/0.99      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1217,c_1214]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_15,plain,
% 3.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_funct_1(X3)
% 3.90/0.99      | ~ v1_funct_1(X0)
% 3.90/0.99      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) ),
% 3.90/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1215,plain,
% 3.90/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) != iProver_top
% 3.90/0.99      | v1_funct_1(X0) != iProver_top
% 3.90/0.99      | v1_funct_1(X3) != iProver_top
% 3.90/0.99      | v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3)) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_14,plain,
% 3.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.99      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3)
% 3.90/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_funct_1(X4)
% 3.90/0.99      | ~ v1_funct_1(X0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1216,plain,
% 3.90/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.90/0.99      | v1_funct_2(k8_funct_2(X1,X2,X3,X0,X4),X1,X3) = iProver_top
% 3.90/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.90/0.99      | v1_funct_1(X4) != iProver_top
% 3.90/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9957,plain,
% 3.90/0.99      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k1_funct_1(k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.90/0.99      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.90/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X4) != iProver_top
% 3.90/0.99      | v1_funct_1(X3) != iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.90/0.99      inference(forward_subsumption_resolution,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2915,c_1215,c_1216]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9964,plain,
% 3.90/0.99      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.90/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(X1) != iProver_top
% 3.90/0.99      | v1_funct_1(sK3) != iProver_top
% 3.90/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1207,c_9957]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_30,negated_conjecture,
% 3.90/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_33,plain,
% 3.90/0.99      ( v1_xboole_0(sK1) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10146,plain,
% 3.90/0.99      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k1_funct_1(k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_9964,c_33,c_34,c_35]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10158,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_10146]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10272,plain,
% 3.90/0.99      ( m1_subset_1(X0,sK1) != iProver_top
% 3.90/0.99      | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_10158,c_37]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10273,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.90/0.99      inference(renaming,[status(thm)],[c_10272]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10281,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1210,c_10273]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_20,plain,
% 3.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.99      | ~ m1_subset_1(X3,X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_funct_1(X0)
% 3.90/0.99      | v1_xboole_0(X2)
% 3.90/0.99      | v1_xboole_0(X1)
% 3.90/0.99      | k3_funct_2(X1,X2,X0,X3) = k7_partfun1(X2,X0,X3) ),
% 3.90/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1212,plain,
% 3.90/0.99      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
% 3.90/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X2) != iProver_top
% 3.90/0.99      | v1_xboole_0(X1) = iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2914,plain,
% 3.90/0.99      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.90/0.99      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.90/0.99      | v1_funct_2(k8_funct_2(X0,X2,X1,X3,X4),X0,X1) != iProver_top
% 3.90/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X3) != iProver_top
% 3.90/0.99      | v1_funct_1(X4) != iProver_top
% 3.90/0.99      | v1_funct_1(k8_funct_2(X0,X2,X1,X3,X4)) != iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top
% 3.90/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1217,c_1212]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9106,plain,
% 3.90/0.99      ( k3_funct_2(X0,X1,k8_funct_2(X0,X2,X1,X3,X4),X5) = k7_partfun1(X1,k8_funct_2(X0,X2,X1,X3,X4),X5)
% 3.90/0.99      | v1_funct_2(X3,X0,X2) != iProver_top
% 3.90/0.99      | m1_subset_1(X5,X0) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X4) != iProver_top
% 3.90/0.99      | v1_funct_1(X3) != iProver_top
% 3.90/0.99      | v1_xboole_0(X1) = iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.90/0.99      inference(forward_subsumption_resolution,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2914,c_1215,c_1216]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9113,plain,
% 3.90/0.99      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.90/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(X1) != iProver_top
% 3.90/0.99      | v1_funct_1(sK3) != iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top
% 3.90/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1207,c_9106]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9409,plain,
% 3.90/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.90/0.99      | k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_9113,c_33,c_34,c_35]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9410,plain,
% 3.90/0.99      ( k3_funct_2(sK1,X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2) = k7_partfun1(X0,k8_funct_2(sK1,sK0,X0,sK3,X1),X2)
% 3.90/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.90/0.99      | m1_subset_1(X2,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(X1) != iProver_top
% 3.90/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.90/0.99      inference(renaming,[status(thm)],[c_9409]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9422,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(sK4) != iProver_top
% 3.90/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_9410]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9,plain,
% 3.90/0.99      ( ~ v1_partfun1(X0,X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_xboole_0(X2)
% 3.90/0.99      | v1_xboole_0(X1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_459,plain,
% 3.90/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_xboole_0(X2)
% 3.90/0.99      | v1_xboole_0(X1)
% 3.90/0.99      | sK4 != X0
% 3.90/0.99      | sK0 != X1 ),
% 3.90/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_460,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.90/0.99      | ~ v1_xboole_0(X0)
% 3.90/0.99      | v1_xboole_0(sK0) ),
% 3.90/0.99      inference(unflattening,[status(thm)],[c_459]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_462,plain,
% 3.90/0.99      ( ~ v1_xboole_0(X0)
% 3.90/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_460,c_31]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_463,plain,
% 3.90/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 3.90/0.99      | ~ v1_xboole_0(X0) ),
% 3.90/0.99      inference(renaming,[status(thm)],[c_462]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1200,plain,
% 3.90/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.90/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1896,plain,
% 3.90/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_1200]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9477,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_9422,c_37,c_1896]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9486,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1210,c_9477]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10300,plain,
% 3.90/0.99      ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_10281,c_9486]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2178,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 3.90/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top
% 3.90/0.99      | v1_funct_1(sK3) != iProver_top
% 3.90/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1207,c_1214]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2422,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
% 3.90/0.99      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2178,c_33,c_34,c_35]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2431,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1210,c_2422]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_22,negated_conjecture,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
% 3.90/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2450,plain,
% 3.90/0.99      ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_2431,c_22]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_9544,plain,
% 3.90/0.99      ( k7_partfun1(sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_9486,c_2450]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10355,plain,
% 3.90/0.99      ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_10300,c_9544]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10362,plain,
% 3.90/0.99      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 3.90/0.99      | sK1 = k1_xboole_0 ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_9026,c_10355]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_12,plain,
% 3.90/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.99      | ~ m1_subset_1(X3,X1)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 3.90/0.99      | ~ v1_funct_1(X0)
% 3.90/0.99      | v1_xboole_0(X1) ),
% 3.90/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1218,plain,
% 3.90/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.90/0.99      | m1_subset_1(X3,X1) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.90/0.99      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 3.90/0.99      | v1_funct_1(X0) != iProver_top
% 3.90/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2451,plain,
% 3.90/0.99      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.90/0.99      | m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top
% 3.90/0.99      | m1_subset_1(sK5,sK1) != iProver_top
% 3.90/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.90/0.99      | v1_funct_1(sK3) != iProver_top
% 3.90/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_2431,c_1218]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_39,plain,
% 3.90/0.99      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3468,plain,
% 3.90/0.99      ( m1_subset_1(k1_funct_1(sK3,sK5),sK0) = iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2451,c_33,c_34,c_35,c_36,c_39]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2815,plain,
% 3.90/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 3.90/0.99      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.90/0.99      | v1_funct_1(sK4) != iProver_top
% 3.90/0.99      | v1_xboole_0(sK0) = iProver_top
% 3.90/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_1212]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_18,plain,
% 3.90/0.99      ( v1_funct_2(X0,X1,X2)
% 3.90/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.99      | ~ v1_funct_1(X0)
% 3.90/0.99      | k1_relset_1(X1,X2,X0) != X1 ),
% 3.90/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1213,plain,
% 3.90/0.99      ( k1_relset_1(X0,X1,X2) != X0
% 3.90/0.99      | v1_funct_2(X2,X0,X1) = iProver_top
% 3.90/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.90/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2061,plain,
% 3.90/0.99      ( k1_relat_1(sK4) != sK0
% 3.90/0.99      | v1_funct_2(sK4,sK0,sK2) = iProver_top
% 3.90/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.90/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1948,c_1213]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3075,plain,
% 3.90/0.99      ( m1_subset_1(X0,sK0) != iProver_top
% 3.90/0.99      | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2815,c_32,c_37,c_38,c_746,c_1660,c_1896,c_1930,c_1937,
% 3.90/0.99                 c_2061]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3076,plain,
% 3.90/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)
% 3.90/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.90/0.99      inference(renaming,[status(thm)],[c_3075]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3473,plain,
% 3.90/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_3468,c_3076]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2177,plain,
% 3.90/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 3.90/0.99      | v1_funct_2(sK4,sK0,sK2) != iProver_top
% 3.90/0.99      | m1_subset_1(X0,sK0) != iProver_top
% 3.90/0.99      | v1_funct_1(sK4) != iProver_top
% 3.90/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_1209,c_1214]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_2381,plain,
% 3.90/0.99      ( k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
% 3.90/0.99      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_2177,c_32,c_37,c_38,c_746,c_1660,c_1930,c_1937,c_2061]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3474,plain,
% 3.90/0.99      ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.90/0.99      inference(superposition,[status(thm)],[c_3468,c_2381]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_3477,plain,
% 3.90/0.99      ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.90/0.99      inference(light_normalisation,[status(thm)],[c_3473,c_3474]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10403,plain,
% 3.90/0.99      ( sK1 = k1_xboole_0 ),
% 3.90/0.99      inference(global_propositional_subsumption,
% 3.90/0.99                [status(thm)],
% 3.90/0.99                [c_10362,c_3477]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_1204,plain,
% 3.90/0.99      ( v1_xboole_0(sK1) != iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_10463,plain,
% 3.90/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.90/0.99      inference(demodulation,[status(thm)],[c_10403,c_1204]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_0,plain,
% 3.90/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.90/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(c_96,plain,
% 3.90/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.90/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.90/0.99  
% 3.90/0.99  cnf(contradiction,plain,
% 3.90/0.99      ( $false ),
% 3.90/0.99      inference(minisat,[status(thm)],[c_10463,c_96]) ).
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/0.99  
% 3.90/0.99  ------                               Statistics
% 3.90/0.99  
% 3.90/0.99  ------ General
% 3.90/0.99  
% 3.90/0.99  abstr_ref_over_cycles:                  0
% 3.90/0.99  abstr_ref_under_cycles:                 0
% 3.90/0.99  gc_basic_clause_elim:                   0
% 3.90/0.99  forced_gc_time:                         0
% 3.90/0.99  parsing_time:                           0.013
% 3.90/0.99  unif_index_cands_time:                  0.
% 3.90/0.99  unif_index_add_time:                    0.
% 3.90/0.99  orderings_time:                         0.
% 3.90/0.99  out_proof_time:                         0.013
% 3.90/0.99  total_time:                             0.388
% 3.90/0.99  num_of_symbols:                         58
% 3.90/0.99  num_of_terms:                           12462
% 3.90/0.99  
% 3.90/0.99  ------ Preprocessing
% 3.90/0.99  
% 3.90/0.99  num_of_splits:                          1
% 3.90/0.99  num_of_split_atoms:                     1
% 3.90/0.99  num_of_reused_defs:                     0
% 3.90/0.99  num_eq_ax_congr_red:                    31
% 3.90/0.99  num_of_sem_filtered_clauses:            1
% 3.90/0.99  num_of_subtypes:                        0
% 3.90/0.99  monotx_restored_types:                  0
% 3.90/0.99  sat_num_of_epr_types:                   0
% 3.90/0.99  sat_num_of_non_cyclic_types:            0
% 3.90/0.99  sat_guarded_non_collapsed_types:        0
% 3.90/0.99  num_pure_diseq_elim:                    0
% 3.90/0.99  simp_replaced_by:                       0
% 3.90/0.99  res_preprocessed:                       141
% 3.90/0.99  prep_upred:                             0
% 3.90/0.99  prep_unflattend:                        14
% 3.90/0.99  smt_new_axioms:                         0
% 3.90/0.99  pred_elim_cands:                        6
% 3.90/0.99  pred_elim:                              3
% 3.90/0.99  pred_elim_cl:                           4
% 3.90/0.99  pred_elim_cycles:                       7
% 3.90/0.99  merged_defs:                            0
% 3.90/0.99  merged_defs_ncl:                        0
% 3.90/0.99  bin_hyper_res:                          0
% 3.90/0.99  prep_cycles:                            4
% 3.90/0.99  pred_elim_time:                         0.005
% 3.90/0.99  splitting_time:                         0.
% 3.90/0.99  sem_filter_time:                        0.
% 3.90/0.99  monotx_time:                            0.
% 3.90/0.99  subtype_inf_time:                       0.
% 3.90/0.99  
% 3.90/0.99  ------ Problem properties
% 3.90/0.99  
% 3.90/0.99  clauses:                                27
% 3.90/0.99  conjectures:                            9
% 3.90/0.99  epr:                                    7
% 3.90/0.99  horn:                                   22
% 3.90/0.99  ground:                                 11
% 3.90/0.99  unary:                                  11
% 3.90/0.99  binary:                                 4
% 3.90/0.99  lits:                                   83
% 3.90/0.99  lits_eq:                                9
% 3.90/0.99  fd_pure:                                0
% 3.90/0.99  fd_pseudo:                              0
% 3.90/0.99  fd_cond:                                1
% 3.90/0.99  fd_pseudo_cond:                         0
% 3.90/0.99  ac_symbols:                             0
% 3.90/0.99  
% 3.90/0.99  ------ Propositional Solver
% 3.90/0.99  
% 3.90/0.99  prop_solver_calls:                      29
% 3.90/0.99  prop_fast_solver_calls:                 1851
% 3.90/0.99  smt_solver_calls:                       0
% 3.90/0.99  smt_fast_solver_calls:                  0
% 3.90/0.99  prop_num_of_clauses:                    3856
% 3.90/0.99  prop_preprocess_simplified:             7922
% 3.90/0.99  prop_fo_subsumed:                       112
% 3.90/0.99  prop_solver_time:                       0.
% 3.90/0.99  smt_solver_time:                        0.
% 3.90/0.99  smt_fast_solver_time:                   0.
% 3.90/0.99  prop_fast_solver_time:                  0.
% 3.90/0.99  prop_unsat_core_time:                   0.
% 3.90/0.99  
% 3.90/0.99  ------ QBF
% 3.90/0.99  
% 3.90/0.99  qbf_q_res:                              0
% 3.90/0.99  qbf_num_tautologies:                    0
% 3.90/0.99  qbf_prep_cycles:                        0
% 3.90/0.99  
% 3.90/0.99  ------ BMC1
% 3.90/0.99  
% 3.90/0.99  bmc1_current_bound:                     -1
% 3.90/0.99  bmc1_last_solved_bound:                 -1
% 3.90/0.99  bmc1_unsat_core_size:                   -1
% 3.90/0.99  bmc1_unsat_core_parents_size:           -1
% 3.90/0.99  bmc1_merge_next_fun:                    0
% 3.90/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.90/0.99  
% 3.90/0.99  ------ Instantiation
% 3.90/0.99  
% 3.90/0.99  inst_num_of_clauses:                    929
% 3.90/0.99  inst_num_in_passive:                    79
% 3.90/0.99  inst_num_in_active:                     649
% 3.90/0.99  inst_num_in_unprocessed:                201
% 3.90/0.99  inst_num_of_loops:                      670
% 3.90/0.99  inst_num_of_learning_restarts:          0
% 3.90/0.99  inst_num_moves_active_passive:          17
% 3.90/0.99  inst_lit_activity:                      0
% 3.90/0.99  inst_lit_activity_moves:                0
% 3.90/0.99  inst_num_tautologies:                   0
% 3.90/0.99  inst_num_prop_implied:                  0
% 3.90/0.99  inst_num_existing_simplified:           0
% 3.90/0.99  inst_num_eq_res_simplified:             0
% 3.90/0.99  inst_num_child_elim:                    0
% 3.90/0.99  inst_num_of_dismatching_blockings:      113
% 3.90/0.99  inst_num_of_non_proper_insts:           755
% 3.90/0.99  inst_num_of_duplicates:                 0
% 3.90/0.99  inst_inst_num_from_inst_to_res:         0
% 3.90/0.99  inst_dismatching_checking_time:         0.
% 3.90/0.99  
% 3.90/0.99  ------ Resolution
% 3.90/0.99  
% 3.90/0.99  res_num_of_clauses:                     0
% 3.90/0.99  res_num_in_passive:                     0
% 3.90/0.99  res_num_in_active:                      0
% 3.90/0.99  res_num_of_loops:                       145
% 3.90/0.99  res_forward_subset_subsumed:            78
% 3.90/0.99  res_backward_subset_subsumed:           0
% 3.90/0.99  res_forward_subsumed:                   0
% 3.90/0.99  res_backward_subsumed:                  0
% 3.90/0.99  res_forward_subsumption_resolution:     1
% 3.90/0.99  res_backward_subsumption_resolution:    0
% 3.90/0.99  res_clause_to_clause_subsumption:       2538
% 3.90/0.99  res_orphan_elimination:                 0
% 3.90/0.99  res_tautology_del:                      92
% 3.90/0.99  res_num_eq_res_simplified:              0
% 3.90/0.99  res_num_sel_changes:                    0
% 3.90/0.99  res_moves_from_active_to_pass:          0
% 3.90/0.99  
% 3.90/0.99  ------ Superposition
% 3.90/0.99  
% 3.90/0.99  sup_time_total:                         0.
% 3.90/0.99  sup_time_generating:                    0.
% 3.90/0.99  sup_time_sim_full:                      0.
% 3.90/0.99  sup_time_sim_immed:                     0.
% 3.90/0.99  
% 3.90/0.99  sup_num_of_clauses:                     224
% 3.90/0.99  sup_num_in_active:                      67
% 3.90/0.99  sup_num_in_passive:                     157
% 3.90/0.99  sup_num_of_loops:                       132
% 3.90/0.99  sup_fw_superposition:                   184
% 3.90/0.99  sup_bw_superposition:                   23
% 3.90/0.99  sup_immediate_simplified:               7
% 3.90/0.99  sup_given_eliminated:                   0
% 3.90/0.99  comparisons_done:                       0
% 3.90/0.99  comparisons_avoided:                    15
% 3.90/0.99  
% 3.90/0.99  ------ Simplifications
% 3.90/0.99  
% 3.90/0.99  
% 3.90/0.99  sim_fw_subset_subsumed:                 2
% 3.90/0.99  sim_bw_subset_subsumed:                 1
% 3.90/0.99  sim_fw_subsumed:                        1
% 3.90/0.99  sim_bw_subsumed:                        0
% 3.90/0.99  sim_fw_subsumption_res:                 31
% 3.90/0.99  sim_bw_subsumption_res:                 0
% 3.90/0.99  sim_tautology_del:                      0
% 3.90/0.99  sim_eq_tautology_del:                   4
% 3.90/0.99  sim_eq_res_simp:                        0
% 3.90/0.99  sim_fw_demodulated:                     0
% 3.90/0.99  sim_bw_demodulated:                     64
% 3.90/0.99  sim_light_normalised:                   5
% 3.90/0.99  sim_joinable_taut:                      0
% 3.90/0.99  sim_joinable_simp:                      0
% 3.90/0.99  sim_ac_normalised:                      0
% 3.90/0.99  sim_smt_subsumption:                    0
% 3.90/0.99  
%------------------------------------------------------------------------------
