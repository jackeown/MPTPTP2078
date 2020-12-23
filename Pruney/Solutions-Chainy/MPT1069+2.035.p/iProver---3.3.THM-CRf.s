%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:49 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 469 expanded)
%              Number of clauses        :   80 ( 124 expanded)
%              Number of leaves         :   17 ( 159 expanded)
%              Depth                    :   18
%              Number of atoms          :  514 (3558 expanded)
%              Number of equality atoms :  210 ( 953 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) != k7_partfun1(X0,X4,k1_funct_1(X3,sK5))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) != k7_partfun1(X0,sK4,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK3,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f39,f38,f37,f36])).

fof(f65,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1885,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | X1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_863,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_862])).

cnf(c_1880,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_4406,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_1880])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2090,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_2202,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2090])).

cnf(c_2203,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_4539,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4406,c_34,c_19,c_2203])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1884,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1890,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2336,plain,
    ( v5_relat_1(sK4,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1884,c_1890])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1882,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1888,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2395,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1882,c_1888])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1886,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2629,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2395,c_1886])).

cnf(c_3,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1894,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v5_relat_1(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3095,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_1894])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2068,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2069,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2068])).

cnf(c_3807,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3095,c_31,c_2069])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1889,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2875,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1884,c_1889])).

cnf(c_3811,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3807,c_2875])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1892,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1887,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3877,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_1887])).

cnf(c_5444,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3811,c_3877])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_824,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_825,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_824])).

cnf(c_827,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_825,c_24])).

cnf(c_2876,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1882,c_1889])).

cnf(c_3262,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_827,c_2876])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_375,plain,
    ( sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_27])).

cnf(c_3346,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3262,c_375])).

cnf(c_5469,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5444,c_3346])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_29,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_32,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2065,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2066,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2065])).

cnf(c_6295,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5469,c_29,c_31,c_32,c_33,c_2066,c_2069])).

cnf(c_6304,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2336,c_6295])).

cnf(c_6312,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_4539,c_6304])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_797,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | sK3 != X2
    | sK2 != X1
    | sK1 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_798,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_797])).

cnf(c_802,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_27,c_26,c_24,c_19])).

cnf(c_803,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
    inference(renaming,[status(thm)],[c_802])).

cnf(c_1876,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_2754,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1876,c_2395])).

cnf(c_2763,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_2754])).

cnf(c_3815,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2763,c_32,c_33])).

cnf(c_3823,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1885,c_3815])).

cnf(c_18,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3916,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3823,c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6312,c_3916])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.26/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.01  
% 2.26/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.26/1.01  
% 2.26/1.01  ------  iProver source info
% 2.26/1.01  
% 2.26/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.26/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.26/1.01  git: non_committed_changes: false
% 2.26/1.01  git: last_make_outside_of_git: false
% 2.26/1.01  
% 2.26/1.01  ------ 
% 2.26/1.01  
% 2.26/1.01  ------ Input Options
% 2.26/1.01  
% 2.26/1.01  --out_options                           all
% 2.26/1.01  --tptp_safe_out                         true
% 2.26/1.01  --problem_path                          ""
% 2.26/1.01  --include_path                          ""
% 2.26/1.01  --clausifier                            res/vclausify_rel
% 2.26/1.01  --clausifier_options                    --mode clausify
% 2.26/1.01  --stdin                                 false
% 2.26/1.01  --stats_out                             all
% 2.26/1.01  
% 2.26/1.01  ------ General Options
% 2.26/1.01  
% 2.26/1.01  --fof                                   false
% 2.26/1.01  --time_out_real                         305.
% 2.26/1.01  --time_out_virtual                      -1.
% 2.26/1.01  --symbol_type_check                     false
% 2.26/1.01  --clausify_out                          false
% 2.26/1.01  --sig_cnt_out                           false
% 2.26/1.01  --trig_cnt_out                          false
% 2.26/1.01  --trig_cnt_out_tolerance                1.
% 2.26/1.01  --trig_cnt_out_sk_spl                   false
% 2.26/1.01  --abstr_cl_out                          false
% 2.26/1.01  
% 2.26/1.01  ------ Global Options
% 2.26/1.01  
% 2.26/1.01  --schedule                              default
% 2.26/1.01  --add_important_lit                     false
% 2.26/1.01  --prop_solver_per_cl                    1000
% 2.26/1.01  --min_unsat_core                        false
% 2.26/1.01  --soft_assumptions                      false
% 2.26/1.01  --soft_lemma_size                       3
% 2.26/1.01  --prop_impl_unit_size                   0
% 2.26/1.01  --prop_impl_unit                        []
% 2.26/1.01  --share_sel_clauses                     true
% 2.26/1.01  --reset_solvers                         false
% 2.26/1.01  --bc_imp_inh                            [conj_cone]
% 2.26/1.01  --conj_cone_tolerance                   3.
% 2.26/1.01  --extra_neg_conj                        none
% 2.26/1.01  --large_theory_mode                     true
% 2.26/1.01  --prolific_symb_bound                   200
% 2.26/1.01  --lt_threshold                          2000
% 2.26/1.01  --clause_weak_htbl                      true
% 2.26/1.01  --gc_record_bc_elim                     false
% 2.26/1.01  
% 2.26/1.01  ------ Preprocessing Options
% 2.26/1.01  
% 2.26/1.01  --preprocessing_flag                    true
% 2.26/1.01  --time_out_prep_mult                    0.1
% 2.26/1.01  --splitting_mode                        input
% 2.26/1.01  --splitting_grd                         true
% 2.26/1.01  --splitting_cvd                         false
% 2.26/1.01  --splitting_cvd_svl                     false
% 2.26/1.01  --splitting_nvd                         32
% 2.26/1.01  --sub_typing                            true
% 2.26/1.01  --prep_gs_sim                           true
% 2.26/1.01  --prep_unflatten                        true
% 2.26/1.01  --prep_res_sim                          true
% 2.26/1.01  --prep_upred                            true
% 2.26/1.01  --prep_sem_filter                       exhaustive
% 2.26/1.01  --prep_sem_filter_out                   false
% 2.26/1.01  --pred_elim                             true
% 2.26/1.01  --res_sim_input                         true
% 2.26/1.01  --eq_ax_congr_red                       true
% 2.26/1.01  --pure_diseq_elim                       true
% 2.26/1.01  --brand_transform                       false
% 2.26/1.01  --non_eq_to_eq                          false
% 2.26/1.01  --prep_def_merge                        true
% 2.26/1.01  --prep_def_merge_prop_impl              false
% 2.26/1.01  --prep_def_merge_mbd                    true
% 2.26/1.01  --prep_def_merge_tr_red                 false
% 2.26/1.01  --prep_def_merge_tr_cl                  false
% 2.26/1.01  --smt_preprocessing                     true
% 2.26/1.01  --smt_ac_axioms                         fast
% 2.26/1.01  --preprocessed_out                      false
% 2.26/1.01  --preprocessed_stats                    false
% 2.26/1.01  
% 2.26/1.01  ------ Abstraction refinement Options
% 2.26/1.01  
% 2.26/1.01  --abstr_ref                             []
% 2.26/1.01  --abstr_ref_prep                        false
% 2.26/1.01  --abstr_ref_until_sat                   false
% 2.26/1.01  --abstr_ref_sig_restrict                funpre
% 2.26/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/1.01  --abstr_ref_under                       []
% 2.26/1.01  
% 2.26/1.01  ------ SAT Options
% 2.26/1.01  
% 2.26/1.01  --sat_mode                              false
% 2.26/1.01  --sat_fm_restart_options                ""
% 2.26/1.01  --sat_gr_def                            false
% 2.26/1.01  --sat_epr_types                         true
% 2.26/1.01  --sat_non_cyclic_types                  false
% 2.26/1.01  --sat_finite_models                     false
% 2.26/1.01  --sat_fm_lemmas                         false
% 2.26/1.01  --sat_fm_prep                           false
% 2.26/1.01  --sat_fm_uc_incr                        true
% 2.26/1.01  --sat_out_model                         small
% 2.26/1.01  --sat_out_clauses                       false
% 2.26/1.01  
% 2.26/1.01  ------ QBF Options
% 2.26/1.01  
% 2.26/1.01  --qbf_mode                              false
% 2.26/1.01  --qbf_elim_univ                         false
% 2.26/1.01  --qbf_dom_inst                          none
% 2.26/1.01  --qbf_dom_pre_inst                      false
% 2.26/1.01  --qbf_sk_in                             false
% 2.26/1.01  --qbf_pred_elim                         true
% 2.26/1.01  --qbf_split                             512
% 2.26/1.01  
% 2.26/1.01  ------ BMC1 Options
% 2.26/1.01  
% 2.26/1.01  --bmc1_incremental                      false
% 2.26/1.01  --bmc1_axioms                           reachable_all
% 2.26/1.01  --bmc1_min_bound                        0
% 2.26/1.01  --bmc1_max_bound                        -1
% 2.26/1.01  --bmc1_max_bound_default                -1
% 2.26/1.01  --bmc1_symbol_reachability              true
% 2.26/1.01  --bmc1_property_lemmas                  false
% 2.26/1.01  --bmc1_k_induction                      false
% 2.26/1.01  --bmc1_non_equiv_states                 false
% 2.26/1.01  --bmc1_deadlock                         false
% 2.26/1.01  --bmc1_ucm                              false
% 2.26/1.01  --bmc1_add_unsat_core                   none
% 2.26/1.01  --bmc1_unsat_core_children              false
% 2.26/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/1.01  --bmc1_out_stat                         full
% 2.26/1.01  --bmc1_ground_init                      false
% 2.26/1.01  --bmc1_pre_inst_next_state              false
% 2.26/1.01  --bmc1_pre_inst_state                   false
% 2.26/1.01  --bmc1_pre_inst_reach_state             false
% 2.26/1.01  --bmc1_out_unsat_core                   false
% 2.26/1.01  --bmc1_aig_witness_out                  false
% 2.26/1.01  --bmc1_verbose                          false
% 2.26/1.01  --bmc1_dump_clauses_tptp                false
% 2.26/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.26/1.01  --bmc1_dump_file                        -
% 2.26/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.26/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.26/1.01  --bmc1_ucm_extend_mode                  1
% 2.26/1.01  --bmc1_ucm_init_mode                    2
% 2.26/1.01  --bmc1_ucm_cone_mode                    none
% 2.26/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.26/1.01  --bmc1_ucm_relax_model                  4
% 2.26/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.26/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/1.01  --bmc1_ucm_layered_model                none
% 2.26/1.01  --bmc1_ucm_max_lemma_size               10
% 2.26/1.01  
% 2.26/1.01  ------ AIG Options
% 2.26/1.01  
% 2.26/1.01  --aig_mode                              false
% 2.26/1.01  
% 2.26/1.01  ------ Instantiation Options
% 2.26/1.01  
% 2.26/1.01  --instantiation_flag                    true
% 2.26/1.01  --inst_sos_flag                         false
% 2.26/1.01  --inst_sos_phase                        true
% 2.26/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/1.01  --inst_lit_sel_side                     num_symb
% 2.26/1.01  --inst_solver_per_active                1400
% 2.26/1.01  --inst_solver_calls_frac                1.
% 2.26/1.01  --inst_passive_queue_type               priority_queues
% 2.26/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/1.01  --inst_passive_queues_freq              [25;2]
% 2.26/1.01  --inst_dismatching                      true
% 2.26/1.01  --inst_eager_unprocessed_to_passive     true
% 2.26/1.01  --inst_prop_sim_given                   true
% 2.26/1.01  --inst_prop_sim_new                     false
% 2.26/1.01  --inst_subs_new                         false
% 2.26/1.01  --inst_eq_res_simp                      false
% 2.26/1.01  --inst_subs_given                       false
% 2.26/1.01  --inst_orphan_elimination               true
% 2.26/1.01  --inst_learning_loop_flag               true
% 2.26/1.01  --inst_learning_start                   3000
% 2.26/1.01  --inst_learning_factor                  2
% 2.26/1.01  --inst_start_prop_sim_after_learn       3
% 2.26/1.01  --inst_sel_renew                        solver
% 2.26/1.01  --inst_lit_activity_flag                true
% 2.26/1.01  --inst_restr_to_given                   false
% 2.26/1.01  --inst_activity_threshold               500
% 2.26/1.01  --inst_out_proof                        true
% 2.26/1.01  
% 2.26/1.01  ------ Resolution Options
% 2.26/1.01  
% 2.26/1.01  --resolution_flag                       true
% 2.26/1.01  --res_lit_sel                           adaptive
% 2.26/1.01  --res_lit_sel_side                      none
% 2.26/1.01  --res_ordering                          kbo
% 2.26/1.01  --res_to_prop_solver                    active
% 2.26/1.01  --res_prop_simpl_new                    false
% 2.26/1.01  --res_prop_simpl_given                  true
% 2.26/1.01  --res_passive_queue_type                priority_queues
% 2.26/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/1.01  --res_passive_queues_freq               [15;5]
% 2.26/1.01  --res_forward_subs                      full
% 2.26/1.01  --res_backward_subs                     full
% 2.26/1.01  --res_forward_subs_resolution           true
% 2.26/1.01  --res_backward_subs_resolution          true
% 2.26/1.01  --res_orphan_elimination                true
% 2.26/1.01  --res_time_limit                        2.
% 2.26/1.01  --res_out_proof                         true
% 2.26/1.01  
% 2.26/1.01  ------ Superposition Options
% 2.26/1.01  
% 2.26/1.01  --superposition_flag                    true
% 2.26/1.01  --sup_passive_queue_type                priority_queues
% 2.26/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.26/1.01  --demod_completeness_check              fast
% 2.26/1.01  --demod_use_ground                      true
% 2.26/1.01  --sup_to_prop_solver                    passive
% 2.26/1.01  --sup_prop_simpl_new                    true
% 2.26/1.01  --sup_prop_simpl_given                  true
% 2.26/1.01  --sup_fun_splitting                     false
% 2.26/1.01  --sup_smt_interval                      50000
% 2.26/1.01  
% 2.26/1.01  ------ Superposition Simplification Setup
% 2.26/1.01  
% 2.26/1.01  --sup_indices_passive                   []
% 2.26/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.01  --sup_full_bw                           [BwDemod]
% 2.26/1.01  --sup_immed_triv                        [TrivRules]
% 2.26/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.01  --sup_immed_bw_main                     []
% 2.26/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.01  
% 2.26/1.01  ------ Combination Options
% 2.26/1.01  
% 2.26/1.01  --comb_res_mult                         3
% 2.26/1.01  --comb_sup_mult                         2
% 2.26/1.01  --comb_inst_mult                        10
% 2.26/1.01  
% 2.26/1.01  ------ Debug Options
% 2.26/1.01  
% 2.26/1.01  --dbg_backtrace                         false
% 2.26/1.01  --dbg_dump_prop_clauses                 false
% 2.26/1.01  --dbg_dump_prop_clauses_file            -
% 2.26/1.01  --dbg_out_stat                          false
% 2.26/1.01  ------ Parsing...
% 2.26/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.26/1.01  
% 2.26/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.26/1.01  
% 2.26/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.26/1.01  
% 2.26/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.26/1.01  ------ Proving...
% 2.26/1.01  ------ Problem Properties 
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  clauses                                 23
% 2.26/1.01  conjectures                             8
% 2.26/1.01  EPR                                     7
% 2.26/1.01  Horn                                    20
% 2.26/1.01  unary                                   9
% 2.26/1.01  binary                                  6
% 2.26/1.01  lits                                    58
% 2.26/1.01  lits eq                                 16
% 2.26/1.01  fd_pure                                 0
% 2.26/1.01  fd_pseudo                               0
% 2.26/1.01  fd_cond                                 2
% 2.26/1.01  fd_pseudo_cond                          0
% 2.26/1.01  AC symbols                              0
% 2.26/1.01  
% 2.26/1.01  ------ Schedule dynamic 5 is on 
% 2.26/1.01  
% 2.26/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  ------ 
% 2.26/1.01  Current options:
% 2.26/1.01  ------ 
% 2.26/1.01  
% 2.26/1.01  ------ Input Options
% 2.26/1.01  
% 2.26/1.01  --out_options                           all
% 2.26/1.01  --tptp_safe_out                         true
% 2.26/1.01  --problem_path                          ""
% 2.26/1.01  --include_path                          ""
% 2.26/1.01  --clausifier                            res/vclausify_rel
% 2.26/1.01  --clausifier_options                    --mode clausify
% 2.26/1.01  --stdin                                 false
% 2.26/1.01  --stats_out                             all
% 2.26/1.01  
% 2.26/1.01  ------ General Options
% 2.26/1.01  
% 2.26/1.01  --fof                                   false
% 2.26/1.01  --time_out_real                         305.
% 2.26/1.01  --time_out_virtual                      -1.
% 2.26/1.01  --symbol_type_check                     false
% 2.26/1.01  --clausify_out                          false
% 2.26/1.01  --sig_cnt_out                           false
% 2.26/1.01  --trig_cnt_out                          false
% 2.26/1.01  --trig_cnt_out_tolerance                1.
% 2.26/1.01  --trig_cnt_out_sk_spl                   false
% 2.26/1.01  --abstr_cl_out                          false
% 2.26/1.01  
% 2.26/1.01  ------ Global Options
% 2.26/1.01  
% 2.26/1.01  --schedule                              default
% 2.26/1.01  --add_important_lit                     false
% 2.26/1.01  --prop_solver_per_cl                    1000
% 2.26/1.01  --min_unsat_core                        false
% 2.26/1.01  --soft_assumptions                      false
% 2.26/1.01  --soft_lemma_size                       3
% 2.26/1.01  --prop_impl_unit_size                   0
% 2.26/1.01  --prop_impl_unit                        []
% 2.26/1.01  --share_sel_clauses                     true
% 2.26/1.01  --reset_solvers                         false
% 2.26/1.01  --bc_imp_inh                            [conj_cone]
% 2.26/1.01  --conj_cone_tolerance                   3.
% 2.26/1.01  --extra_neg_conj                        none
% 2.26/1.01  --large_theory_mode                     true
% 2.26/1.01  --prolific_symb_bound                   200
% 2.26/1.01  --lt_threshold                          2000
% 2.26/1.01  --clause_weak_htbl                      true
% 2.26/1.01  --gc_record_bc_elim                     false
% 2.26/1.01  
% 2.26/1.01  ------ Preprocessing Options
% 2.26/1.01  
% 2.26/1.01  --preprocessing_flag                    true
% 2.26/1.01  --time_out_prep_mult                    0.1
% 2.26/1.01  --splitting_mode                        input
% 2.26/1.01  --splitting_grd                         true
% 2.26/1.01  --splitting_cvd                         false
% 2.26/1.01  --splitting_cvd_svl                     false
% 2.26/1.01  --splitting_nvd                         32
% 2.26/1.01  --sub_typing                            true
% 2.26/1.01  --prep_gs_sim                           true
% 2.26/1.01  --prep_unflatten                        true
% 2.26/1.01  --prep_res_sim                          true
% 2.26/1.01  --prep_upred                            true
% 2.26/1.01  --prep_sem_filter                       exhaustive
% 2.26/1.01  --prep_sem_filter_out                   false
% 2.26/1.01  --pred_elim                             true
% 2.26/1.01  --res_sim_input                         true
% 2.26/1.01  --eq_ax_congr_red                       true
% 2.26/1.01  --pure_diseq_elim                       true
% 2.26/1.01  --brand_transform                       false
% 2.26/1.01  --non_eq_to_eq                          false
% 2.26/1.01  --prep_def_merge                        true
% 2.26/1.01  --prep_def_merge_prop_impl              false
% 2.26/1.01  --prep_def_merge_mbd                    true
% 2.26/1.01  --prep_def_merge_tr_red                 false
% 2.26/1.01  --prep_def_merge_tr_cl                  false
% 2.26/1.01  --smt_preprocessing                     true
% 2.26/1.01  --smt_ac_axioms                         fast
% 2.26/1.01  --preprocessed_out                      false
% 2.26/1.01  --preprocessed_stats                    false
% 2.26/1.01  
% 2.26/1.01  ------ Abstraction refinement Options
% 2.26/1.01  
% 2.26/1.01  --abstr_ref                             []
% 2.26/1.01  --abstr_ref_prep                        false
% 2.26/1.01  --abstr_ref_until_sat                   false
% 2.26/1.01  --abstr_ref_sig_restrict                funpre
% 2.26/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/1.01  --abstr_ref_under                       []
% 2.26/1.01  
% 2.26/1.01  ------ SAT Options
% 2.26/1.01  
% 2.26/1.01  --sat_mode                              false
% 2.26/1.01  --sat_fm_restart_options                ""
% 2.26/1.01  --sat_gr_def                            false
% 2.26/1.01  --sat_epr_types                         true
% 2.26/1.01  --sat_non_cyclic_types                  false
% 2.26/1.01  --sat_finite_models                     false
% 2.26/1.01  --sat_fm_lemmas                         false
% 2.26/1.01  --sat_fm_prep                           false
% 2.26/1.01  --sat_fm_uc_incr                        true
% 2.26/1.01  --sat_out_model                         small
% 2.26/1.01  --sat_out_clauses                       false
% 2.26/1.01  
% 2.26/1.01  ------ QBF Options
% 2.26/1.01  
% 2.26/1.01  --qbf_mode                              false
% 2.26/1.01  --qbf_elim_univ                         false
% 2.26/1.01  --qbf_dom_inst                          none
% 2.26/1.01  --qbf_dom_pre_inst                      false
% 2.26/1.01  --qbf_sk_in                             false
% 2.26/1.01  --qbf_pred_elim                         true
% 2.26/1.01  --qbf_split                             512
% 2.26/1.01  
% 2.26/1.01  ------ BMC1 Options
% 2.26/1.01  
% 2.26/1.01  --bmc1_incremental                      false
% 2.26/1.01  --bmc1_axioms                           reachable_all
% 2.26/1.01  --bmc1_min_bound                        0
% 2.26/1.01  --bmc1_max_bound                        -1
% 2.26/1.01  --bmc1_max_bound_default                -1
% 2.26/1.01  --bmc1_symbol_reachability              true
% 2.26/1.01  --bmc1_property_lemmas                  false
% 2.26/1.01  --bmc1_k_induction                      false
% 2.26/1.01  --bmc1_non_equiv_states                 false
% 2.26/1.01  --bmc1_deadlock                         false
% 2.26/1.01  --bmc1_ucm                              false
% 2.26/1.01  --bmc1_add_unsat_core                   none
% 2.26/1.01  --bmc1_unsat_core_children              false
% 2.26/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/1.01  --bmc1_out_stat                         full
% 2.26/1.01  --bmc1_ground_init                      false
% 2.26/1.01  --bmc1_pre_inst_next_state              false
% 2.26/1.01  --bmc1_pre_inst_state                   false
% 2.26/1.01  --bmc1_pre_inst_reach_state             false
% 2.26/1.01  --bmc1_out_unsat_core                   false
% 2.26/1.01  --bmc1_aig_witness_out                  false
% 2.26/1.01  --bmc1_verbose                          false
% 2.26/1.01  --bmc1_dump_clauses_tptp                false
% 2.26/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.26/1.01  --bmc1_dump_file                        -
% 2.26/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.26/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.26/1.01  --bmc1_ucm_extend_mode                  1
% 2.26/1.01  --bmc1_ucm_init_mode                    2
% 2.26/1.01  --bmc1_ucm_cone_mode                    none
% 2.26/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.26/1.01  --bmc1_ucm_relax_model                  4
% 2.26/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.26/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/1.01  --bmc1_ucm_layered_model                none
% 2.26/1.01  --bmc1_ucm_max_lemma_size               10
% 2.26/1.01  
% 2.26/1.01  ------ AIG Options
% 2.26/1.01  
% 2.26/1.01  --aig_mode                              false
% 2.26/1.01  
% 2.26/1.01  ------ Instantiation Options
% 2.26/1.01  
% 2.26/1.01  --instantiation_flag                    true
% 2.26/1.01  --inst_sos_flag                         false
% 2.26/1.01  --inst_sos_phase                        true
% 2.26/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/1.01  --inst_lit_sel_side                     none
% 2.26/1.01  --inst_solver_per_active                1400
% 2.26/1.01  --inst_solver_calls_frac                1.
% 2.26/1.01  --inst_passive_queue_type               priority_queues
% 2.26/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/1.01  --inst_passive_queues_freq              [25;2]
% 2.26/1.01  --inst_dismatching                      true
% 2.26/1.01  --inst_eager_unprocessed_to_passive     true
% 2.26/1.01  --inst_prop_sim_given                   true
% 2.26/1.01  --inst_prop_sim_new                     false
% 2.26/1.01  --inst_subs_new                         false
% 2.26/1.01  --inst_eq_res_simp                      false
% 2.26/1.01  --inst_subs_given                       false
% 2.26/1.01  --inst_orphan_elimination               true
% 2.26/1.01  --inst_learning_loop_flag               true
% 2.26/1.01  --inst_learning_start                   3000
% 2.26/1.01  --inst_learning_factor                  2
% 2.26/1.01  --inst_start_prop_sim_after_learn       3
% 2.26/1.01  --inst_sel_renew                        solver
% 2.26/1.01  --inst_lit_activity_flag                true
% 2.26/1.01  --inst_restr_to_given                   false
% 2.26/1.01  --inst_activity_threshold               500
% 2.26/1.01  --inst_out_proof                        true
% 2.26/1.01  
% 2.26/1.01  ------ Resolution Options
% 2.26/1.01  
% 2.26/1.01  --resolution_flag                       false
% 2.26/1.01  --res_lit_sel                           adaptive
% 2.26/1.01  --res_lit_sel_side                      none
% 2.26/1.01  --res_ordering                          kbo
% 2.26/1.01  --res_to_prop_solver                    active
% 2.26/1.01  --res_prop_simpl_new                    false
% 2.26/1.01  --res_prop_simpl_given                  true
% 2.26/1.01  --res_passive_queue_type                priority_queues
% 2.26/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/1.01  --res_passive_queues_freq               [15;5]
% 2.26/1.01  --res_forward_subs                      full
% 2.26/1.01  --res_backward_subs                     full
% 2.26/1.01  --res_forward_subs_resolution           true
% 2.26/1.01  --res_backward_subs_resolution          true
% 2.26/1.01  --res_orphan_elimination                true
% 2.26/1.01  --res_time_limit                        2.
% 2.26/1.01  --res_out_proof                         true
% 2.26/1.01  
% 2.26/1.01  ------ Superposition Options
% 2.26/1.01  
% 2.26/1.01  --superposition_flag                    true
% 2.26/1.01  --sup_passive_queue_type                priority_queues
% 2.26/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.26/1.01  --demod_completeness_check              fast
% 2.26/1.01  --demod_use_ground                      true
% 2.26/1.01  --sup_to_prop_solver                    passive
% 2.26/1.01  --sup_prop_simpl_new                    true
% 2.26/1.01  --sup_prop_simpl_given                  true
% 2.26/1.01  --sup_fun_splitting                     false
% 2.26/1.01  --sup_smt_interval                      50000
% 2.26/1.01  
% 2.26/1.01  ------ Superposition Simplification Setup
% 2.26/1.01  
% 2.26/1.01  --sup_indices_passive                   []
% 2.26/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.01  --sup_full_bw                           [BwDemod]
% 2.26/1.01  --sup_immed_triv                        [TrivRules]
% 2.26/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.01  --sup_immed_bw_main                     []
% 2.26/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/1.01  
% 2.26/1.01  ------ Combination Options
% 2.26/1.01  
% 2.26/1.01  --comb_res_mult                         3
% 2.26/1.01  --comb_sup_mult                         2
% 2.26/1.01  --comb_inst_mult                        10
% 2.26/1.01  
% 2.26/1.01  ------ Debug Options
% 2.26/1.01  
% 2.26/1.01  --dbg_backtrace                         false
% 2.26/1.01  --dbg_dump_prop_clauses                 false
% 2.26/1.01  --dbg_dump_prop_clauses_file            -
% 2.26/1.01  --dbg_out_stat                          false
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  ------ Proving...
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  % SZS status Theorem for theBenchmark.p
% 2.26/1.01  
% 2.26/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.26/1.01  
% 2.26/1.01  fof(f13,conjecture,(
% 2.26/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f14,negated_conjecture,(
% 2.26/1.01    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.26/1.01    inference(negated_conjecture,[],[f13])).
% 2.26/1.01  
% 2.26/1.01  fof(f32,plain,(
% 2.26/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.26/1.01    inference(ennf_transformation,[],[f14])).
% 2.26/1.01  
% 2.26/1.01  fof(f33,plain,(
% 2.26/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.26/1.01    inference(flattening,[],[f32])).
% 2.26/1.01  
% 2.26/1.01  fof(f39,plain,(
% 2.26/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) != k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.26/1.01    introduced(choice_axiom,[])).
% 2.26/1.01  
% 2.26/1.01  fof(f38,plain,(
% 2.26/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) != k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.26/1.01    introduced(choice_axiom,[])).
% 2.26/1.01  
% 2.26/1.01  fof(f37,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.26/1.01    introduced(choice_axiom,[])).
% 2.26/1.01  
% 2.26/1.01  fof(f36,plain,(
% 2.26/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.26/1.01    introduced(choice_axiom,[])).
% 2.26/1.01  
% 2.26/1.01  fof(f40,plain,(
% 2.26/1.01    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.26/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f39,f38,f37,f36])).
% 2.26/1.01  
% 2.26/1.01  fof(f65,plain,(
% 2.26/1.01    m1_subset_1(sK5,sK1)),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f2,axiom,(
% 2.26/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f16,plain,(
% 2.26/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.26/1.01    inference(ennf_transformation,[],[f2])).
% 2.26/1.01  
% 2.26/1.01  fof(f42,plain,(
% 2.26/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.26/1.01    inference(cnf_transformation,[],[f16])).
% 2.26/1.01  
% 2.26/1.01  fof(f3,axiom,(
% 2.26/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f17,plain,(
% 2.26/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.26/1.01    inference(ennf_transformation,[],[f3])).
% 2.26/1.01  
% 2.26/1.01  fof(f18,plain,(
% 2.26/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.26/1.01    inference(flattening,[],[f17])).
% 2.26/1.01  
% 2.26/1.01  fof(f43,plain,(
% 2.26/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.26/1.01    inference(cnf_transformation,[],[f18])).
% 2.26/1.01  
% 2.26/1.01  fof(f67,plain,(
% 2.26/1.01    k1_xboole_0 != sK1),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f64,plain,(
% 2.26/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f7,axiom,(
% 2.26/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f15,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.26/1.01    inference(pure_predicate_removal,[],[f7])).
% 2.26/1.01  
% 2.26/1.01  fof(f23,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/1.01    inference(ennf_transformation,[],[f15])).
% 2.26/1.01  
% 2.26/1.01  fof(f48,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/1.01    inference(cnf_transformation,[],[f23])).
% 2.26/1.01  
% 2.26/1.01  fof(f62,plain,(
% 2.26/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f9,axiom,(
% 2.26/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f25,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/1.01    inference(ennf_transformation,[],[f9])).
% 2.26/1.01  
% 2.26/1.01  fof(f50,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/1.01    inference(cnf_transformation,[],[f25])).
% 2.26/1.01  
% 2.26/1.01  fof(f66,plain,(
% 2.26/1.01    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f4,axiom,(
% 2.26/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f19,plain,(
% 2.26/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.26/1.01    inference(ennf_transformation,[],[f4])).
% 2.26/1.01  
% 2.26/1.01  fof(f34,plain,(
% 2.26/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.26/1.01    inference(nnf_transformation,[],[f19])).
% 2.26/1.01  
% 2.26/1.01  fof(f45,plain,(
% 2.26/1.01    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.26/1.01    inference(cnf_transformation,[],[f34])).
% 2.26/1.01  
% 2.26/1.01  fof(f6,axiom,(
% 2.26/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f22,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/1.01    inference(ennf_transformation,[],[f6])).
% 2.26/1.01  
% 2.26/1.01  fof(f47,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/1.01    inference(cnf_transformation,[],[f22])).
% 2.26/1.01  
% 2.26/1.01  fof(f8,axiom,(
% 2.26/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f24,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/1.01    inference(ennf_transformation,[],[f8])).
% 2.26/1.01  
% 2.26/1.01  fof(f49,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/1.01    inference(cnf_transformation,[],[f24])).
% 2.26/1.01  
% 2.26/1.01  fof(f5,axiom,(
% 2.26/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f20,plain,(
% 2.26/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.26/1.01    inference(ennf_transformation,[],[f5])).
% 2.26/1.01  
% 2.26/1.01  fof(f21,plain,(
% 2.26/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.26/1.01    inference(flattening,[],[f20])).
% 2.26/1.01  
% 2.26/1.01  fof(f46,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.26/1.01    inference(cnf_transformation,[],[f21])).
% 2.26/1.01  
% 2.26/1.01  fof(f11,axiom,(
% 2.26/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f28,plain,(
% 2.26/1.01    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.26/1.01    inference(ennf_transformation,[],[f11])).
% 2.26/1.01  
% 2.26/1.01  fof(f29,plain,(
% 2.26/1.01    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.26/1.01    inference(flattening,[],[f28])).
% 2.26/1.01  
% 2.26/1.01  fof(f57,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.26/1.01    inference(cnf_transformation,[],[f29])).
% 2.26/1.01  
% 2.26/1.01  fof(f10,axiom,(
% 2.26/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f26,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/1.01    inference(ennf_transformation,[],[f10])).
% 2.26/1.01  
% 2.26/1.01  fof(f27,plain,(
% 2.26/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/1.01    inference(flattening,[],[f26])).
% 2.26/1.01  
% 2.26/1.01  fof(f35,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/1.01    inference(nnf_transformation,[],[f27])).
% 2.26/1.01  
% 2.26/1.01  fof(f51,plain,(
% 2.26/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/1.01    inference(cnf_transformation,[],[f35])).
% 2.26/1.01  
% 2.26/1.01  fof(f61,plain,(
% 2.26/1.01    v1_funct_2(sK3,sK1,sK2)),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f1,axiom,(
% 2.26/1.01    v1_xboole_0(k1_xboole_0)),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f41,plain,(
% 2.26/1.01    v1_xboole_0(k1_xboole_0)),
% 2.26/1.01    inference(cnf_transformation,[],[f1])).
% 2.26/1.01  
% 2.26/1.01  fof(f59,plain,(
% 2.26/1.01    ~v1_xboole_0(sK2)),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f60,plain,(
% 2.26/1.01    v1_funct_1(sK3)),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f63,plain,(
% 2.26/1.01    v1_funct_1(sK4)),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  fof(f12,axiom,(
% 2.26/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.26/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.26/1.01  
% 2.26/1.01  fof(f30,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.26/1.01    inference(ennf_transformation,[],[f12])).
% 2.26/1.01  
% 2.26/1.01  fof(f31,plain,(
% 2.26/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.26/1.01    inference(flattening,[],[f30])).
% 2.26/1.01  
% 2.26/1.01  fof(f58,plain,(
% 2.26/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.26/1.01    inference(cnf_transformation,[],[f31])).
% 2.26/1.01  
% 2.26/1.01  fof(f68,plain,(
% 2.26/1.01    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 2.26/1.01    inference(cnf_transformation,[],[f40])).
% 2.26/1.01  
% 2.26/1.01  cnf(c_21,negated_conjecture,
% 2.26/1.01      ( m1_subset_1(sK5,sK1) ),
% 2.26/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1885,plain,
% 2.26/1.01      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1,plain,
% 2.26/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.26/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.26/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_862,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,X1)
% 2.26/1.01      | r2_hidden(X0,X1)
% 2.26/1.01      | X1 != X2
% 2.26/1.01      | k1_xboole_0 = X2 ),
% 2.26/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_863,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1 ),
% 2.26/1.01      inference(unflattening,[status(thm)],[c_862]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1880,plain,
% 2.26/1.01      ( k1_xboole_0 = X0
% 2.26/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.26/1.01      | r2_hidden(X1,X0) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_4406,plain,
% 2.26/1.01      ( sK1 = k1_xboole_0 | r2_hidden(sK5,sK1) = iProver_top ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_1885,c_1880]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_34,plain,
% 2.26/1.01      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_19,negated_conjecture,
% 2.26/1.01      ( k1_xboole_0 != sK1 ),
% 2.26/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2090,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) | k1_xboole_0 = sK1 ),
% 2.26/1.01      inference(instantiation,[status(thm)],[c_863]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2202,plain,
% 2.26/1.01      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | k1_xboole_0 = sK1 ),
% 2.26/1.01      inference(instantiation,[status(thm)],[c_2090]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2203,plain,
% 2.26/1.01      ( k1_xboole_0 = sK1
% 2.26/1.01      | m1_subset_1(sK5,sK1) != iProver_top
% 2.26/1.01      | r2_hidden(sK5,sK1) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_2202]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_4539,plain,
% 2.26/1.01      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.26/1.01      inference(global_propositional_subsumption,
% 2.26/1.01                [status(thm)],
% 2.26/1.01                [c_4406,c_34,c_19,c_2203]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_22,negated_conjecture,
% 2.26/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.26/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1884,plain,
% 2.26/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_7,plain,
% 2.26/1.01      ( v5_relat_1(X0,X1)
% 2.26/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.26/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1890,plain,
% 2.26/1.01      ( v5_relat_1(X0,X1) = iProver_top
% 2.26/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2336,plain,
% 2.26/1.01      ( v5_relat_1(sK4,sK0) = iProver_top ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_1884,c_1890]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_24,negated_conjecture,
% 2.26/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.26/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1882,plain,
% 2.26/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_9,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.26/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1888,plain,
% 2.26/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.26/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2395,plain,
% 2.26/1.01      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_1882,c_1888]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_20,negated_conjecture,
% 2.26/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.26/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1886,plain,
% 2.26/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2629,plain,
% 2.26/1.01      ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.26/1.01      inference(demodulation,[status(thm)],[c_2395,c_1886]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3,plain,
% 2.26/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.26/1.01      | v5_relat_1(X0,X1)
% 2.26/1.01      | ~ v1_relat_1(X0) ),
% 2.26/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1894,plain,
% 2.26/1.01      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.26/1.01      | v5_relat_1(X0,X1) = iProver_top
% 2.26/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3095,plain,
% 2.26/1.01      ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.26/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_2629,c_1894]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_31,plain,
% 2.26/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_6,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/1.01      | v1_relat_1(X0) ),
% 2.26/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2068,plain,
% 2.26/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.26/1.01      | v1_relat_1(sK3) ),
% 2.26/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2069,plain,
% 2.26/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.26/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_2068]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3807,plain,
% 2.26/1.01      ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.26/1.01      inference(global_propositional_subsumption,
% 2.26/1.01                [status(thm)],
% 2.26/1.01                [c_3095,c_31,c_2069]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_8,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.26/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1889,plain,
% 2.26/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.26/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2875,plain,
% 2.26/1.01      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_1884,c_1889]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3811,plain,
% 2.26/1.01      ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
% 2.26/1.01      inference(light_normalisation,[status(thm)],[c_3807,c_2875]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_5,plain,
% 2.26/1.01      ( ~ v5_relat_1(X0,X1)
% 2.26/1.01      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.26/1.01      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.26/1.01      | ~ v1_funct_1(X0)
% 2.26/1.01      | ~ v1_relat_1(X0) ),
% 2.26/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1892,plain,
% 2.26/1.01      ( v5_relat_1(X0,X1) != iProver_top
% 2.26/1.01      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 2.26/1.01      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 2.26/1.01      | v1_funct_1(X0) != iProver_top
% 2.26/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_16,plain,
% 2.26/1.01      ( ~ v5_relat_1(X0,X1)
% 2.26/1.01      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.26/1.01      | ~ v1_funct_1(X0)
% 2.26/1.01      | ~ v1_relat_1(X0)
% 2.26/1.01      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.26/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1887,plain,
% 2.26/1.01      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.26/1.01      | v5_relat_1(X1,X0) != iProver_top
% 2.26/1.01      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.26/1.01      | v1_funct_1(X1) != iProver_top
% 2.26/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3877,plain,
% 2.26/1.01      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 2.26/1.01      | v5_relat_1(X1,X0) != iProver_top
% 2.26/1.01      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 2.26/1.01      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 2.26/1.01      | v1_funct_1(X2) != iProver_top
% 2.26/1.01      | v1_funct_1(X1) != iProver_top
% 2.26/1.01      | v1_relat_1(X2) != iProver_top
% 2.26/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_1892,c_1887]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_5444,plain,
% 2.26/1.01      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.26/1.01      | v5_relat_1(sK4,X0) != iProver_top
% 2.26/1.01      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 2.26/1.01      | v1_funct_1(sK4) != iProver_top
% 2.26/1.01      | v1_funct_1(sK3) != iProver_top
% 2.26/1.01      | v1_relat_1(sK4) != iProver_top
% 2.26/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_3811,c_3877]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_15,plain,
% 2.26/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.26/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.26/1.01      | k1_xboole_0 = X2 ),
% 2.26/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_25,negated_conjecture,
% 2.26/1.01      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.26/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_824,plain,
% 2.26/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.26/1.01      | sK3 != X0
% 2.26/1.01      | sK2 != X2
% 2.26/1.01      | sK1 != X1
% 2.26/1.01      | k1_xboole_0 = X2 ),
% 2.26/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_825,plain,
% 2.26/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.26/1.01      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.26/1.01      | k1_xboole_0 = sK2 ),
% 2.26/1.01      inference(unflattening,[status(thm)],[c_824]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_827,plain,
% 2.26/1.01      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.26/1.01      inference(global_propositional_subsumption,
% 2.26/1.01                [status(thm)],
% 2.26/1.01                [c_825,c_24]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2876,plain,
% 2.26/1.01      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_1882,c_1889]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3262,plain,
% 2.26/1.01      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_827,c_2876]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_0,plain,
% 2.26/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.26/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_27,negated_conjecture,
% 2.26/1.01      ( ~ v1_xboole_0(sK2) ),
% 2.26/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_375,plain,
% 2.26/1.01      ( sK2 != k1_xboole_0 ),
% 2.26/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_27]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3346,plain,
% 2.26/1.01      ( k1_relat_1(sK3) = sK1 ),
% 2.26/1.01      inference(global_propositional_subsumption,
% 2.26/1.01                [status(thm)],
% 2.26/1.01                [c_3262,c_375]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_5469,plain,
% 2.26/1.01      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.26/1.01      | v5_relat_1(sK4,X0) != iProver_top
% 2.26/1.01      | r2_hidden(X1,sK1) != iProver_top
% 2.26/1.01      | v1_funct_1(sK4) != iProver_top
% 2.26/1.01      | v1_funct_1(sK3) != iProver_top
% 2.26/1.01      | v1_relat_1(sK4) != iProver_top
% 2.26/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.26/1.01      inference(light_normalisation,[status(thm)],[c_5444,c_3346]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_26,negated_conjecture,
% 2.26/1.01      ( v1_funct_1(sK3) ),
% 2.26/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_29,plain,
% 2.26/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_23,negated_conjecture,
% 2.26/1.01      ( v1_funct_1(sK4) ),
% 2.26/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_32,plain,
% 2.26/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_33,plain,
% 2.26/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2065,plain,
% 2.26/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 2.26/1.01      | v1_relat_1(sK4) ),
% 2.26/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2066,plain,
% 2.26/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.26/1.01      | v1_relat_1(sK4) = iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_2065]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_6295,plain,
% 2.26/1.01      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.26/1.01      | v5_relat_1(sK4,X0) != iProver_top
% 2.26/1.01      | r2_hidden(X1,sK1) != iProver_top ),
% 2.26/1.01      inference(global_propositional_subsumption,
% 2.26/1.01                [status(thm)],
% 2.26/1.01                [c_5469,c_29,c_31,c_32,c_33,c_2066,c_2069]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_6304,plain,
% 2.26/1.01      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.26/1.01      | r2_hidden(X0,sK1) != iProver_top ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_2336,c_6295]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_6312,plain,
% 2.26/1.01      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_4539,c_6304]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_17,plain,
% 2.26/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.26/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.26/1.01      | ~ m1_subset_1(X5,X1)
% 2.26/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.26/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/1.01      | ~ v1_funct_1(X4)
% 2.26/1.01      | ~ v1_funct_1(X0)
% 2.26/1.01      | v1_xboole_0(X2)
% 2.26/1.01      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.26/1.01      | k1_xboole_0 = X1 ),
% 2.26/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_797,plain,
% 2.26/1.01      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 2.26/1.01      | ~ m1_subset_1(X5,X0)
% 2.26/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.26/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.26/1.01      | ~ v1_funct_1(X2)
% 2.26/1.01      | ~ v1_funct_1(X4)
% 2.26/1.01      | v1_xboole_0(X1)
% 2.26/1.01      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.26/1.01      | sK3 != X2
% 2.26/1.01      | sK2 != X1
% 2.26/1.01      | sK1 != X0
% 2.26/1.01      | k1_xboole_0 = X0 ),
% 2.26/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_798,plain,
% 2.26/1.01      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.26/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.26/1.01      | ~ m1_subset_1(X2,sK1)
% 2.26/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.26/1.01      | ~ v1_funct_1(X1)
% 2.26/1.01      | ~ v1_funct_1(sK3)
% 2.26/1.01      | v1_xboole_0(sK2)
% 2.26/1.01      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.26/1.01      | k1_xboole_0 = sK1 ),
% 2.26/1.01      inference(unflattening,[status(thm)],[c_797]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_802,plain,
% 2.26/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.26/1.01      | ~ v1_funct_1(X1)
% 2.26/1.01      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.26/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.26/1.01      | ~ m1_subset_1(X2,sK1) ),
% 2.26/1.01      inference(global_propositional_subsumption,
% 2.26/1.01                [status(thm)],
% 2.26/1.01                [c_798,c_27,c_26,c_24,c_19]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_803,plain,
% 2.26/1.01      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.26/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.26/1.01      | ~ m1_subset_1(X2,sK1)
% 2.26/1.01      | ~ v1_funct_1(X1)
% 2.26/1.01      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
% 2.26/1.01      inference(renaming,[status(thm)],[c_802]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_1876,plain,
% 2.26/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.26/1.01      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
% 2.26/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.26/1.01      | m1_subset_1(X2,sK1) != iProver_top
% 2.26/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.26/1.01      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2754,plain,
% 2.26/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.26/1.01      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
% 2.26/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.26/1.01      | m1_subset_1(X2,sK1) != iProver_top
% 2.26/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.26/1.01      inference(light_normalisation,[status(thm)],[c_1876,c_2395]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_2763,plain,
% 2.26/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.26/1.01      | m1_subset_1(X0,sK1) != iProver_top
% 2.26/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.26/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_2629,c_2754]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3815,plain,
% 2.26/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.26/1.01      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.26/1.01      inference(global_propositional_subsumption,
% 2.26/1.01                [status(thm)],
% 2.26/1.01                [c_2763,c_32,c_33]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3823,plain,
% 2.26/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.26/1.01      inference(superposition,[status(thm)],[c_1885,c_3815]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_18,negated_conjecture,
% 2.26/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
% 2.26/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(c_3916,plain,
% 2.26/1.01      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.26/1.01      inference(demodulation,[status(thm)],[c_3823,c_18]) ).
% 2.26/1.01  
% 2.26/1.01  cnf(contradiction,plain,
% 2.26/1.01      ( $false ),
% 2.26/1.01      inference(minisat,[status(thm)],[c_6312,c_3916]) ).
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.26/1.01  
% 2.26/1.01  ------                               Statistics
% 2.26/1.01  
% 2.26/1.01  ------ General
% 2.26/1.01  
% 2.26/1.01  abstr_ref_over_cycles:                  0
% 2.26/1.01  abstr_ref_under_cycles:                 0
% 2.26/1.01  gc_basic_clause_elim:                   0
% 2.26/1.01  forced_gc_time:                         0
% 2.26/1.01  parsing_time:                           0.017
% 2.26/1.01  unif_index_cands_time:                  0.
% 2.26/1.01  unif_index_add_time:                    0.
% 2.26/1.01  orderings_time:                         0.
% 2.26/1.01  out_proof_time:                         0.014
% 2.26/1.01  total_time:                             0.319
% 2.26/1.01  num_of_symbols:                         55
% 2.26/1.01  num_of_terms:                           14298
% 2.26/1.01  
% 2.26/1.01  ------ Preprocessing
% 2.26/1.01  
% 2.26/1.01  num_of_splits:                          0
% 2.26/1.01  num_of_split_atoms:                     0
% 2.26/1.01  num_of_reused_defs:                     0
% 2.26/1.01  num_eq_ax_congr_red:                    15
% 2.26/1.01  num_of_sem_filtered_clauses:            1
% 2.26/1.01  num_of_subtypes:                        0
% 2.26/1.01  monotx_restored_types:                  0
% 2.26/1.01  sat_num_of_epr_types:                   0
% 2.26/1.01  sat_num_of_non_cyclic_types:            0
% 2.26/1.01  sat_guarded_non_collapsed_types:        0
% 2.26/1.01  num_pure_diseq_elim:                    0
% 2.26/1.01  simp_replaced_by:                       0
% 2.26/1.01  res_preprocessed:                       124
% 2.26/1.01  prep_upred:                             0
% 2.26/1.01  prep_unflattend:                        52
% 2.26/1.01  smt_new_axioms:                         0
% 2.26/1.01  pred_elim_cands:                        6
% 2.26/1.01  pred_elim:                              2
% 2.26/1.01  pred_elim_cl:                           5
% 2.26/1.01  pred_elim_cycles:                       10
% 2.26/1.01  merged_defs:                            0
% 2.26/1.01  merged_defs_ncl:                        0
% 2.26/1.01  bin_hyper_res:                          0
% 2.26/1.01  prep_cycles:                            4
% 2.26/1.01  pred_elim_time:                         0.025
% 2.26/1.01  splitting_time:                         0.
% 2.26/1.01  sem_filter_time:                        0.
% 2.26/1.01  monotx_time:                            0.
% 2.26/1.01  subtype_inf_time:                       0.
% 2.26/1.01  
% 2.26/1.01  ------ Problem properties
% 2.26/1.01  
% 2.26/1.01  clauses:                                23
% 2.26/1.01  conjectures:                            8
% 2.26/1.01  epr:                                    7
% 2.26/1.01  horn:                                   20
% 2.26/1.01  ground:                                 11
% 2.26/1.01  unary:                                  9
% 2.26/1.01  binary:                                 6
% 2.26/1.01  lits:                                   58
% 2.26/1.01  lits_eq:                                16
% 2.26/1.01  fd_pure:                                0
% 2.26/1.01  fd_pseudo:                              0
% 2.26/1.01  fd_cond:                                2
% 2.26/1.01  fd_pseudo_cond:                         0
% 2.26/1.01  ac_symbols:                             0
% 2.26/1.01  
% 2.26/1.01  ------ Propositional Solver
% 2.26/1.01  
% 2.26/1.01  prop_solver_calls:                      27
% 2.26/1.01  prop_fast_solver_calls:                 1197
% 2.26/1.01  smt_solver_calls:                       0
% 2.26/1.01  smt_fast_solver_calls:                  0
% 2.26/1.01  prop_num_of_clauses:                    2338
% 2.26/1.01  prop_preprocess_simplified:             6057
% 2.26/1.01  prop_fo_subsumed:                       43
% 2.26/1.01  prop_solver_time:                       0.
% 2.26/1.01  smt_solver_time:                        0.
% 2.26/1.01  smt_fast_solver_time:                   0.
% 2.26/1.01  prop_fast_solver_time:                  0.
% 2.26/1.01  prop_unsat_core_time:                   0.
% 2.26/1.01  
% 2.26/1.01  ------ QBF
% 2.26/1.01  
% 2.26/1.01  qbf_q_res:                              0
% 2.26/1.01  qbf_num_tautologies:                    0
% 2.26/1.01  qbf_prep_cycles:                        0
% 2.26/1.01  
% 2.26/1.01  ------ BMC1
% 2.26/1.01  
% 2.26/1.01  bmc1_current_bound:                     -1
% 2.26/1.01  bmc1_last_solved_bound:                 -1
% 2.26/1.01  bmc1_unsat_core_size:                   -1
% 2.26/1.01  bmc1_unsat_core_parents_size:           -1
% 2.26/1.01  bmc1_merge_next_fun:                    0
% 2.26/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.26/1.01  
% 2.26/1.01  ------ Instantiation
% 2.26/1.01  
% 2.26/1.01  inst_num_of_clauses:                    615
% 2.26/1.01  inst_num_in_passive:                    266
% 2.26/1.01  inst_num_in_active:                     347
% 2.26/1.01  inst_num_in_unprocessed:                2
% 2.26/1.01  inst_num_of_loops:                      350
% 2.26/1.01  inst_num_of_learning_restarts:          0
% 2.26/1.01  inst_num_moves_active_passive:          0
% 2.26/1.01  inst_lit_activity:                      0
% 2.26/1.01  inst_lit_activity_moves:                0
% 2.26/1.01  inst_num_tautologies:                   0
% 2.26/1.01  inst_num_prop_implied:                  0
% 2.26/1.01  inst_num_existing_simplified:           0
% 2.26/1.01  inst_num_eq_res_simplified:             0
% 2.26/1.01  inst_num_child_elim:                    0
% 2.26/1.01  inst_num_of_dismatching_blockings:      28
% 2.26/1.01  inst_num_of_non_proper_insts:           534
% 2.26/1.01  inst_num_of_duplicates:                 0
% 2.26/1.01  inst_inst_num_from_inst_to_res:         0
% 2.26/1.01  inst_dismatching_checking_time:         0.
% 2.26/1.01  
% 2.26/1.01  ------ Resolution
% 2.26/1.01  
% 2.26/1.01  res_num_of_clauses:                     0
% 2.26/1.01  res_num_in_passive:                     0
% 2.26/1.01  res_num_in_active:                      0
% 2.26/1.01  res_num_of_loops:                       128
% 2.26/1.01  res_forward_subset_subsumed:            55
% 2.26/1.01  res_backward_subset_subsumed:           0
% 2.26/1.01  res_forward_subsumed:                   0
% 2.26/1.01  res_backward_subsumed:                  0
% 2.26/1.01  res_forward_subsumption_resolution:     2
% 2.26/1.01  res_backward_subsumption_resolution:    0
% 2.26/1.01  res_clause_to_clause_subsumption:       445
% 2.26/1.01  res_orphan_elimination:                 0
% 2.26/1.01  res_tautology_del:                      56
% 2.26/1.01  res_num_eq_res_simplified:              0
% 2.26/1.01  res_num_sel_changes:                    0
% 2.26/1.01  res_moves_from_active_to_pass:          0
% 2.26/1.01  
% 2.26/1.01  ------ Superposition
% 2.26/1.01  
% 2.26/1.01  sup_time_total:                         0.
% 2.26/1.01  sup_time_generating:                    0.
% 2.26/1.01  sup_time_sim_full:                      0.
% 2.26/1.01  sup_time_sim_immed:                     0.
% 2.26/1.01  
% 2.26/1.01  sup_num_of_clauses:                     75
% 2.26/1.01  sup_num_in_active:                      64
% 2.26/1.01  sup_num_in_passive:                     11
% 2.26/1.01  sup_num_of_loops:                       68
% 2.26/1.01  sup_fw_superposition:                   51
% 2.26/1.01  sup_bw_superposition:                   8
% 2.26/1.01  sup_immediate_simplified:               4
% 2.26/1.01  sup_given_eliminated:                   0
% 2.26/1.01  comparisons_done:                       0
% 2.26/1.01  comparisons_avoided:                    0
% 2.26/1.01  
% 2.26/1.01  ------ Simplifications
% 2.26/1.01  
% 2.26/1.01  
% 2.26/1.01  sim_fw_subset_subsumed:                 0
% 2.26/1.01  sim_bw_subset_subsumed:                 2
% 2.26/1.01  sim_fw_subsumed:                        2
% 2.26/1.01  sim_bw_subsumed:                        0
% 2.26/1.01  sim_fw_subsumption_res:                 0
% 2.26/1.01  sim_bw_subsumption_res:                 0
% 2.26/1.01  sim_tautology_del:                      1
% 2.26/1.01  sim_eq_tautology_del:                   0
% 2.26/1.01  sim_eq_res_simp:                        0
% 2.26/1.01  sim_fw_demodulated:                     0
% 2.26/1.01  sim_bw_demodulated:                     4
% 2.26/1.01  sim_light_normalised:                   5
% 2.26/1.01  sim_joinable_taut:                      0
% 2.26/1.01  sim_joinable_simp:                      0
% 2.26/1.01  sim_ac_normalised:                      0
% 2.26/1.01  sim_smt_subsumption:                    0
% 2.26/1.01  
%------------------------------------------------------------------------------
