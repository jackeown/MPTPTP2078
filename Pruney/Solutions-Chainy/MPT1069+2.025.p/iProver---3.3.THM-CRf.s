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
% DateTime   : Thu Dec  3 12:09:47 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 828 expanded)
%              Number of clauses        :  110 ( 232 expanded)
%              Number of leaves         :   21 ( 279 expanded)
%              Depth                    :   22
%              Number of atoms          :  670 (6206 expanded)
%              Number of equality atoms :  280 (1700 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
                   => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
                     => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f38])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                ( k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                  ( k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
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

fof(f45,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f44,f43,f42,f41])).

fof(f75,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2110,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2123,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3306,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2110,c_2123])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2360,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2361,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2360])).

cnf(c_2516,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2709,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2516])).

cnf(c_2710,plain,
    ( m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_3862,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3306,c_39,c_24,c_2361,c_2710])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2119,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3150,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2107,c_2119])).

cnf(c_19,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_445,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | k1_relset_1(sK2,sK0,sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_2100,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_3384,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3150,c_2100])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2109,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2120,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3158,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2109,c_2120])).

cnf(c_4397,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3384,c_3158])).

cnf(c_4405,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4397])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2369,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2370,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2369])).

cnf(c_5379,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4405,c_34,c_36,c_2370])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2112,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4459,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2107,c_2112])).

cnf(c_3159,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2107,c_2120])).

cnf(c_4463,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3159])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1637,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2372,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_2374,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_4813,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4463,c_32,c_35,c_0,c_2374])).

cnf(c_5383,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5379,c_4813])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2111,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5393,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5383,c_2111])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_427,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | k1_relset_1(sK2,sK0,sK4) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_428,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_2101,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_3383,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3150,c_2101])).

cnf(c_4328,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK3)
    | v1_funct_2(X0,k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3383,c_3158])).

cnf(c_4336,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4328])).

cnf(c_5128,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4336,c_34,c_36,c_2370])).

cnf(c_5132,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5128,c_4813])).

cnf(c_5780,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5393,c_34,c_5132])).

cnf(c_5781,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5780])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_4,c_17])).

cnf(c_325,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_321,c_3])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_2103,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_2993,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2109,c_2103])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3674,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2993,c_37])).

cnf(c_3675,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3674])).

cnf(c_5789,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5781,c_3675])).

cnf(c_5797,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3862,c_5789])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_391,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X2)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(X2,X5,X4) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_2102,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(X1,X3,X4) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_2785,plain,
    ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2102])).

cnf(c_33,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_95,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1636,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2406,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_2407,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(c_2790,plain,
    ( m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2785,c_33,c_34,c_35,c_36,c_24,c_95,c_0,c_2407])).

cnf(c_2791,plain,
    ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2790])).

cnf(c_2801,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2791])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2855,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_37,c_38])).

cnf(c_2863,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_2110,c_2855])).

cnf(c_23,negated_conjecture,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2865,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_2863,c_23])).

cnf(c_5880,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5797,c_2865])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5391,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5383,c_2121])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_689,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | sK2 != X2
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_690,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_692,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_690,c_32,c_31,c_29])).

cnf(c_694,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_5496,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5391,c_24,c_694,c_2361])).

cnf(c_5889,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5880,c_5496])).

cnf(c_97,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5889,c_97])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.01  
% 2.97/1.01  ------  iProver source info
% 2.97/1.01  
% 2.97/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.01  git: non_committed_changes: false
% 2.97/1.01  git: last_make_outside_of_git: false
% 2.97/1.01  
% 2.97/1.01  ------ 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options
% 2.97/1.01  
% 2.97/1.01  --out_options                           all
% 2.97/1.01  --tptp_safe_out                         true
% 2.97/1.01  --problem_path                          ""
% 2.97/1.01  --include_path                          ""
% 2.97/1.01  --clausifier                            res/vclausify_rel
% 2.97/1.01  --clausifier_options                    --mode clausify
% 2.97/1.01  --stdin                                 false
% 2.97/1.01  --stats_out                             all
% 2.97/1.01  
% 2.97/1.01  ------ General Options
% 2.97/1.01  
% 2.97/1.01  --fof                                   false
% 2.97/1.01  --time_out_real                         305.
% 2.97/1.01  --time_out_virtual                      -1.
% 2.97/1.01  --symbol_type_check                     false
% 2.97/1.01  --clausify_out                          false
% 2.97/1.01  --sig_cnt_out                           false
% 2.97/1.01  --trig_cnt_out                          false
% 2.97/1.01  --trig_cnt_out_tolerance                1.
% 2.97/1.01  --trig_cnt_out_sk_spl                   false
% 2.97/1.01  --abstr_cl_out                          false
% 2.97/1.01  
% 2.97/1.01  ------ Global Options
% 2.97/1.01  
% 2.97/1.01  --schedule                              default
% 2.97/1.01  --add_important_lit                     false
% 2.97/1.01  --prop_solver_per_cl                    1000
% 2.97/1.01  --min_unsat_core                        false
% 2.97/1.01  --soft_assumptions                      false
% 2.97/1.01  --soft_lemma_size                       3
% 2.97/1.01  --prop_impl_unit_size                   0
% 2.97/1.01  --prop_impl_unit                        []
% 2.97/1.01  --share_sel_clauses                     true
% 2.97/1.01  --reset_solvers                         false
% 2.97/1.01  --bc_imp_inh                            [conj_cone]
% 2.97/1.01  --conj_cone_tolerance                   3.
% 2.97/1.01  --extra_neg_conj                        none
% 2.97/1.01  --large_theory_mode                     true
% 2.97/1.01  --prolific_symb_bound                   200
% 2.97/1.01  --lt_threshold                          2000
% 2.97/1.01  --clause_weak_htbl                      true
% 2.97/1.01  --gc_record_bc_elim                     false
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing Options
% 2.97/1.01  
% 2.97/1.01  --preprocessing_flag                    true
% 2.97/1.01  --time_out_prep_mult                    0.1
% 2.97/1.01  --splitting_mode                        input
% 2.97/1.01  --splitting_grd                         true
% 2.97/1.01  --splitting_cvd                         false
% 2.97/1.01  --splitting_cvd_svl                     false
% 2.97/1.01  --splitting_nvd                         32
% 2.97/1.01  --sub_typing                            true
% 2.97/1.01  --prep_gs_sim                           true
% 2.97/1.01  --prep_unflatten                        true
% 2.97/1.01  --prep_res_sim                          true
% 2.97/1.01  --prep_upred                            true
% 2.97/1.01  --prep_sem_filter                       exhaustive
% 2.97/1.01  --prep_sem_filter_out                   false
% 2.97/1.01  --pred_elim                             true
% 2.97/1.01  --res_sim_input                         true
% 2.97/1.01  --eq_ax_congr_red                       true
% 2.97/1.01  --pure_diseq_elim                       true
% 2.97/1.01  --brand_transform                       false
% 2.97/1.01  --non_eq_to_eq                          false
% 2.97/1.01  --prep_def_merge                        true
% 2.97/1.01  --prep_def_merge_prop_impl              false
% 2.97/1.01  --prep_def_merge_mbd                    true
% 2.97/1.01  --prep_def_merge_tr_red                 false
% 2.97/1.01  --prep_def_merge_tr_cl                  false
% 2.97/1.01  --smt_preprocessing                     true
% 2.97/1.01  --smt_ac_axioms                         fast
% 2.97/1.01  --preprocessed_out                      false
% 2.97/1.01  --preprocessed_stats                    false
% 2.97/1.01  
% 2.97/1.01  ------ Abstraction refinement Options
% 2.97/1.01  
% 2.97/1.01  --abstr_ref                             []
% 2.97/1.01  --abstr_ref_prep                        false
% 2.97/1.01  --abstr_ref_until_sat                   false
% 2.97/1.01  --abstr_ref_sig_restrict                funpre
% 2.97/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.01  --abstr_ref_under                       []
% 2.97/1.01  
% 2.97/1.01  ------ SAT Options
% 2.97/1.01  
% 2.97/1.01  --sat_mode                              false
% 2.97/1.01  --sat_fm_restart_options                ""
% 2.97/1.01  --sat_gr_def                            false
% 2.97/1.01  --sat_epr_types                         true
% 2.97/1.01  --sat_non_cyclic_types                  false
% 2.97/1.01  --sat_finite_models                     false
% 2.97/1.01  --sat_fm_lemmas                         false
% 2.97/1.01  --sat_fm_prep                           false
% 2.97/1.01  --sat_fm_uc_incr                        true
% 2.97/1.01  --sat_out_model                         small
% 2.97/1.01  --sat_out_clauses                       false
% 2.97/1.01  
% 2.97/1.01  ------ QBF Options
% 2.97/1.01  
% 2.97/1.01  --qbf_mode                              false
% 2.97/1.01  --qbf_elim_univ                         false
% 2.97/1.01  --qbf_dom_inst                          none
% 2.97/1.01  --qbf_dom_pre_inst                      false
% 2.97/1.01  --qbf_sk_in                             false
% 2.97/1.01  --qbf_pred_elim                         true
% 2.97/1.01  --qbf_split                             512
% 2.97/1.01  
% 2.97/1.01  ------ BMC1 Options
% 2.97/1.01  
% 2.97/1.01  --bmc1_incremental                      false
% 2.97/1.01  --bmc1_axioms                           reachable_all
% 2.97/1.01  --bmc1_min_bound                        0
% 2.97/1.01  --bmc1_max_bound                        -1
% 2.97/1.01  --bmc1_max_bound_default                -1
% 2.97/1.01  --bmc1_symbol_reachability              true
% 2.97/1.01  --bmc1_property_lemmas                  false
% 2.97/1.01  --bmc1_k_induction                      false
% 2.97/1.01  --bmc1_non_equiv_states                 false
% 2.97/1.01  --bmc1_deadlock                         false
% 2.97/1.01  --bmc1_ucm                              false
% 2.97/1.01  --bmc1_add_unsat_core                   none
% 2.97/1.01  --bmc1_unsat_core_children              false
% 2.97/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.01  --bmc1_out_stat                         full
% 2.97/1.01  --bmc1_ground_init                      false
% 2.97/1.01  --bmc1_pre_inst_next_state              false
% 2.97/1.01  --bmc1_pre_inst_state                   false
% 2.97/1.01  --bmc1_pre_inst_reach_state             false
% 2.97/1.01  --bmc1_out_unsat_core                   false
% 2.97/1.01  --bmc1_aig_witness_out                  false
% 2.97/1.01  --bmc1_verbose                          false
% 2.97/1.01  --bmc1_dump_clauses_tptp                false
% 2.97/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.01  --bmc1_dump_file                        -
% 2.97/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.01  --bmc1_ucm_extend_mode                  1
% 2.97/1.01  --bmc1_ucm_init_mode                    2
% 2.97/1.01  --bmc1_ucm_cone_mode                    none
% 2.97/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.01  --bmc1_ucm_relax_model                  4
% 2.97/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.01  --bmc1_ucm_layered_model                none
% 2.97/1.01  --bmc1_ucm_max_lemma_size               10
% 2.97/1.01  
% 2.97/1.01  ------ AIG Options
% 2.97/1.01  
% 2.97/1.01  --aig_mode                              false
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation Options
% 2.97/1.01  
% 2.97/1.01  --instantiation_flag                    true
% 2.97/1.01  --inst_sos_flag                         false
% 2.97/1.01  --inst_sos_phase                        true
% 2.97/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel_side                     num_symb
% 2.97/1.01  --inst_solver_per_active                1400
% 2.97/1.01  --inst_solver_calls_frac                1.
% 2.97/1.01  --inst_passive_queue_type               priority_queues
% 2.97/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.01  --inst_passive_queues_freq              [25;2]
% 2.97/1.01  --inst_dismatching                      true
% 2.97/1.01  --inst_eager_unprocessed_to_passive     true
% 2.97/1.01  --inst_prop_sim_given                   true
% 2.97/1.01  --inst_prop_sim_new                     false
% 2.97/1.01  --inst_subs_new                         false
% 2.97/1.01  --inst_eq_res_simp                      false
% 2.97/1.01  --inst_subs_given                       false
% 2.97/1.01  --inst_orphan_elimination               true
% 2.97/1.01  --inst_learning_loop_flag               true
% 2.97/1.01  --inst_learning_start                   3000
% 2.97/1.01  --inst_learning_factor                  2
% 2.97/1.01  --inst_start_prop_sim_after_learn       3
% 2.97/1.01  --inst_sel_renew                        solver
% 2.97/1.01  --inst_lit_activity_flag                true
% 2.97/1.01  --inst_restr_to_given                   false
% 2.97/1.01  --inst_activity_threshold               500
% 2.97/1.01  --inst_out_proof                        true
% 2.97/1.01  
% 2.97/1.01  ------ Resolution Options
% 2.97/1.01  
% 2.97/1.01  --resolution_flag                       true
% 2.97/1.01  --res_lit_sel                           adaptive
% 2.97/1.01  --res_lit_sel_side                      none
% 2.97/1.01  --res_ordering                          kbo
% 2.97/1.01  --res_to_prop_solver                    active
% 2.97/1.01  --res_prop_simpl_new                    false
% 2.97/1.01  --res_prop_simpl_given                  true
% 2.97/1.01  --res_passive_queue_type                priority_queues
% 2.97/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.01  --res_passive_queues_freq               [15;5]
% 2.97/1.01  --res_forward_subs                      full
% 2.97/1.01  --res_backward_subs                     full
% 2.97/1.01  --res_forward_subs_resolution           true
% 2.97/1.01  --res_backward_subs_resolution          true
% 2.97/1.01  --res_orphan_elimination                true
% 2.97/1.01  --res_time_limit                        2.
% 2.97/1.01  --res_out_proof                         true
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Options
% 2.97/1.01  
% 2.97/1.01  --superposition_flag                    true
% 2.97/1.01  --sup_passive_queue_type                priority_queues
% 2.97/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.01  --demod_completeness_check              fast
% 2.97/1.01  --demod_use_ground                      true
% 2.97/1.01  --sup_to_prop_solver                    passive
% 2.97/1.01  --sup_prop_simpl_new                    true
% 2.97/1.01  --sup_prop_simpl_given                  true
% 2.97/1.01  --sup_fun_splitting                     false
% 2.97/1.01  --sup_smt_interval                      50000
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Simplification Setup
% 2.97/1.01  
% 2.97/1.01  --sup_indices_passive                   []
% 2.97/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_full_bw                           [BwDemod]
% 2.97/1.01  --sup_immed_triv                        [TrivRules]
% 2.97/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_immed_bw_main                     []
% 2.97/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  
% 2.97/1.01  ------ Combination Options
% 2.97/1.01  
% 2.97/1.01  --comb_res_mult                         3
% 2.97/1.01  --comb_sup_mult                         2
% 2.97/1.01  --comb_inst_mult                        10
% 2.97/1.01  
% 2.97/1.01  ------ Debug Options
% 2.97/1.01  
% 2.97/1.01  --dbg_backtrace                         false
% 2.97/1.01  --dbg_dump_prop_clauses                 false
% 2.97/1.01  --dbg_dump_prop_clauses_file            -
% 2.97/1.01  --dbg_out_stat                          false
% 2.97/1.01  ------ Parsing...
% 2.97/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.01  ------ Proving...
% 2.97/1.01  ------ Problem Properties 
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  clauses                                 28
% 2.97/1.01  conjectures                             9
% 2.97/1.01  EPR                                     9
% 2.97/1.01  Horn                                    20
% 2.97/1.01  unary                                   10
% 2.97/1.01  binary                                  4
% 2.97/1.01  lits                                    80
% 2.97/1.01  lits eq                                 22
% 2.97/1.01  fd_pure                                 0
% 2.97/1.01  fd_pseudo                               0
% 2.97/1.01  fd_cond                                 6
% 2.97/1.01  fd_pseudo_cond                          0
% 2.97/1.01  AC symbols                              0
% 2.97/1.01  
% 2.97/1.01  ------ Schedule dynamic 5 is on 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  ------ 
% 2.97/1.01  Current options:
% 2.97/1.01  ------ 
% 2.97/1.01  
% 2.97/1.01  ------ Input Options
% 2.97/1.01  
% 2.97/1.01  --out_options                           all
% 2.97/1.01  --tptp_safe_out                         true
% 2.97/1.01  --problem_path                          ""
% 2.97/1.01  --include_path                          ""
% 2.97/1.01  --clausifier                            res/vclausify_rel
% 2.97/1.01  --clausifier_options                    --mode clausify
% 2.97/1.01  --stdin                                 false
% 2.97/1.01  --stats_out                             all
% 2.97/1.01  
% 2.97/1.01  ------ General Options
% 2.97/1.01  
% 2.97/1.01  --fof                                   false
% 2.97/1.01  --time_out_real                         305.
% 2.97/1.01  --time_out_virtual                      -1.
% 2.97/1.01  --symbol_type_check                     false
% 2.97/1.01  --clausify_out                          false
% 2.97/1.01  --sig_cnt_out                           false
% 2.97/1.01  --trig_cnt_out                          false
% 2.97/1.01  --trig_cnt_out_tolerance                1.
% 2.97/1.01  --trig_cnt_out_sk_spl                   false
% 2.97/1.01  --abstr_cl_out                          false
% 2.97/1.01  
% 2.97/1.01  ------ Global Options
% 2.97/1.01  
% 2.97/1.01  --schedule                              default
% 2.97/1.01  --add_important_lit                     false
% 2.97/1.01  --prop_solver_per_cl                    1000
% 2.97/1.01  --min_unsat_core                        false
% 2.97/1.01  --soft_assumptions                      false
% 2.97/1.01  --soft_lemma_size                       3
% 2.97/1.01  --prop_impl_unit_size                   0
% 2.97/1.01  --prop_impl_unit                        []
% 2.97/1.01  --share_sel_clauses                     true
% 2.97/1.01  --reset_solvers                         false
% 2.97/1.01  --bc_imp_inh                            [conj_cone]
% 2.97/1.01  --conj_cone_tolerance                   3.
% 2.97/1.01  --extra_neg_conj                        none
% 2.97/1.01  --large_theory_mode                     true
% 2.97/1.01  --prolific_symb_bound                   200
% 2.97/1.01  --lt_threshold                          2000
% 2.97/1.01  --clause_weak_htbl                      true
% 2.97/1.01  --gc_record_bc_elim                     false
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing Options
% 2.97/1.01  
% 2.97/1.01  --preprocessing_flag                    true
% 2.97/1.01  --time_out_prep_mult                    0.1
% 2.97/1.01  --splitting_mode                        input
% 2.97/1.01  --splitting_grd                         true
% 2.97/1.01  --splitting_cvd                         false
% 2.97/1.01  --splitting_cvd_svl                     false
% 2.97/1.01  --splitting_nvd                         32
% 2.97/1.01  --sub_typing                            true
% 2.97/1.01  --prep_gs_sim                           true
% 2.97/1.01  --prep_unflatten                        true
% 2.97/1.01  --prep_res_sim                          true
% 2.97/1.01  --prep_upred                            true
% 2.97/1.01  --prep_sem_filter                       exhaustive
% 2.97/1.01  --prep_sem_filter_out                   false
% 2.97/1.01  --pred_elim                             true
% 2.97/1.01  --res_sim_input                         true
% 2.97/1.01  --eq_ax_congr_red                       true
% 2.97/1.01  --pure_diseq_elim                       true
% 2.97/1.01  --brand_transform                       false
% 2.97/1.01  --non_eq_to_eq                          false
% 2.97/1.01  --prep_def_merge                        true
% 2.97/1.01  --prep_def_merge_prop_impl              false
% 2.97/1.01  --prep_def_merge_mbd                    true
% 2.97/1.01  --prep_def_merge_tr_red                 false
% 2.97/1.01  --prep_def_merge_tr_cl                  false
% 2.97/1.01  --smt_preprocessing                     true
% 2.97/1.01  --smt_ac_axioms                         fast
% 2.97/1.01  --preprocessed_out                      false
% 2.97/1.01  --preprocessed_stats                    false
% 2.97/1.01  
% 2.97/1.01  ------ Abstraction refinement Options
% 2.97/1.01  
% 2.97/1.01  --abstr_ref                             []
% 2.97/1.01  --abstr_ref_prep                        false
% 2.97/1.01  --abstr_ref_until_sat                   false
% 2.97/1.01  --abstr_ref_sig_restrict                funpre
% 2.97/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.01  --abstr_ref_under                       []
% 2.97/1.01  
% 2.97/1.01  ------ SAT Options
% 2.97/1.01  
% 2.97/1.01  --sat_mode                              false
% 2.97/1.01  --sat_fm_restart_options                ""
% 2.97/1.01  --sat_gr_def                            false
% 2.97/1.01  --sat_epr_types                         true
% 2.97/1.01  --sat_non_cyclic_types                  false
% 2.97/1.01  --sat_finite_models                     false
% 2.97/1.01  --sat_fm_lemmas                         false
% 2.97/1.01  --sat_fm_prep                           false
% 2.97/1.01  --sat_fm_uc_incr                        true
% 2.97/1.01  --sat_out_model                         small
% 2.97/1.01  --sat_out_clauses                       false
% 2.97/1.01  
% 2.97/1.01  ------ QBF Options
% 2.97/1.01  
% 2.97/1.01  --qbf_mode                              false
% 2.97/1.01  --qbf_elim_univ                         false
% 2.97/1.01  --qbf_dom_inst                          none
% 2.97/1.01  --qbf_dom_pre_inst                      false
% 2.97/1.01  --qbf_sk_in                             false
% 2.97/1.01  --qbf_pred_elim                         true
% 2.97/1.01  --qbf_split                             512
% 2.97/1.01  
% 2.97/1.01  ------ BMC1 Options
% 2.97/1.01  
% 2.97/1.01  --bmc1_incremental                      false
% 2.97/1.01  --bmc1_axioms                           reachable_all
% 2.97/1.01  --bmc1_min_bound                        0
% 2.97/1.01  --bmc1_max_bound                        -1
% 2.97/1.01  --bmc1_max_bound_default                -1
% 2.97/1.01  --bmc1_symbol_reachability              true
% 2.97/1.01  --bmc1_property_lemmas                  false
% 2.97/1.01  --bmc1_k_induction                      false
% 2.97/1.01  --bmc1_non_equiv_states                 false
% 2.97/1.01  --bmc1_deadlock                         false
% 2.97/1.01  --bmc1_ucm                              false
% 2.97/1.01  --bmc1_add_unsat_core                   none
% 2.97/1.01  --bmc1_unsat_core_children              false
% 2.97/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.01  --bmc1_out_stat                         full
% 2.97/1.01  --bmc1_ground_init                      false
% 2.97/1.01  --bmc1_pre_inst_next_state              false
% 2.97/1.01  --bmc1_pre_inst_state                   false
% 2.97/1.01  --bmc1_pre_inst_reach_state             false
% 2.97/1.01  --bmc1_out_unsat_core                   false
% 2.97/1.01  --bmc1_aig_witness_out                  false
% 2.97/1.01  --bmc1_verbose                          false
% 2.97/1.01  --bmc1_dump_clauses_tptp                false
% 2.97/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.01  --bmc1_dump_file                        -
% 2.97/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.01  --bmc1_ucm_extend_mode                  1
% 2.97/1.01  --bmc1_ucm_init_mode                    2
% 2.97/1.01  --bmc1_ucm_cone_mode                    none
% 2.97/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.01  --bmc1_ucm_relax_model                  4
% 2.97/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.01  --bmc1_ucm_layered_model                none
% 2.97/1.01  --bmc1_ucm_max_lemma_size               10
% 2.97/1.01  
% 2.97/1.01  ------ AIG Options
% 2.97/1.01  
% 2.97/1.01  --aig_mode                              false
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation Options
% 2.97/1.01  
% 2.97/1.01  --instantiation_flag                    true
% 2.97/1.01  --inst_sos_flag                         false
% 2.97/1.01  --inst_sos_phase                        true
% 2.97/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.01  --inst_lit_sel_side                     none
% 2.97/1.01  --inst_solver_per_active                1400
% 2.97/1.01  --inst_solver_calls_frac                1.
% 2.97/1.01  --inst_passive_queue_type               priority_queues
% 2.97/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.01  --inst_passive_queues_freq              [25;2]
% 2.97/1.01  --inst_dismatching                      true
% 2.97/1.01  --inst_eager_unprocessed_to_passive     true
% 2.97/1.01  --inst_prop_sim_given                   true
% 2.97/1.01  --inst_prop_sim_new                     false
% 2.97/1.01  --inst_subs_new                         false
% 2.97/1.01  --inst_eq_res_simp                      false
% 2.97/1.01  --inst_subs_given                       false
% 2.97/1.01  --inst_orphan_elimination               true
% 2.97/1.01  --inst_learning_loop_flag               true
% 2.97/1.01  --inst_learning_start                   3000
% 2.97/1.01  --inst_learning_factor                  2
% 2.97/1.01  --inst_start_prop_sim_after_learn       3
% 2.97/1.01  --inst_sel_renew                        solver
% 2.97/1.01  --inst_lit_activity_flag                true
% 2.97/1.01  --inst_restr_to_given                   false
% 2.97/1.01  --inst_activity_threshold               500
% 2.97/1.01  --inst_out_proof                        true
% 2.97/1.01  
% 2.97/1.01  ------ Resolution Options
% 2.97/1.01  
% 2.97/1.01  --resolution_flag                       false
% 2.97/1.01  --res_lit_sel                           adaptive
% 2.97/1.01  --res_lit_sel_side                      none
% 2.97/1.01  --res_ordering                          kbo
% 2.97/1.01  --res_to_prop_solver                    active
% 2.97/1.01  --res_prop_simpl_new                    false
% 2.97/1.01  --res_prop_simpl_given                  true
% 2.97/1.01  --res_passive_queue_type                priority_queues
% 2.97/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.01  --res_passive_queues_freq               [15;5]
% 2.97/1.01  --res_forward_subs                      full
% 2.97/1.01  --res_backward_subs                     full
% 2.97/1.01  --res_forward_subs_resolution           true
% 2.97/1.01  --res_backward_subs_resolution          true
% 2.97/1.01  --res_orphan_elimination                true
% 2.97/1.01  --res_time_limit                        2.
% 2.97/1.01  --res_out_proof                         true
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Options
% 2.97/1.01  
% 2.97/1.01  --superposition_flag                    true
% 2.97/1.01  --sup_passive_queue_type                priority_queues
% 2.97/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.01  --demod_completeness_check              fast
% 2.97/1.01  --demod_use_ground                      true
% 2.97/1.01  --sup_to_prop_solver                    passive
% 2.97/1.01  --sup_prop_simpl_new                    true
% 2.97/1.01  --sup_prop_simpl_given                  true
% 2.97/1.01  --sup_fun_splitting                     false
% 2.97/1.01  --sup_smt_interval                      50000
% 2.97/1.01  
% 2.97/1.01  ------ Superposition Simplification Setup
% 2.97/1.01  
% 2.97/1.01  --sup_indices_passive                   []
% 2.97/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_full_bw                           [BwDemod]
% 2.97/1.01  --sup_immed_triv                        [TrivRules]
% 2.97/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_immed_bw_main                     []
% 2.97/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.01  
% 2.97/1.01  ------ Combination Options
% 2.97/1.01  
% 2.97/1.01  --comb_res_mult                         3
% 2.97/1.01  --comb_sup_mult                         2
% 2.97/1.01  --comb_inst_mult                        10
% 2.97/1.01  
% 2.97/1.01  ------ Debug Options
% 2.97/1.01  
% 2.97/1.01  --dbg_backtrace                         false
% 2.97/1.01  --dbg_dump_prop_clauses                 false
% 2.97/1.01  --dbg_dump_prop_clauses_file            -
% 2.97/1.01  --dbg_out_stat                          false
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  ------ Proving...
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS status Theorem for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  fof(f15,conjecture,(
% 2.97/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f16,negated_conjecture,(
% 2.97/1.01    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.97/1.01    inference(negated_conjecture,[],[f15])).
% 2.97/1.01  
% 2.97/1.01  fof(f38,plain,(
% 2.97/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.97/1.01    inference(ennf_transformation,[],[f16])).
% 2.97/1.01  
% 2.97/1.01  fof(f39,plain,(
% 2.97/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.97/1.01    inference(flattening,[],[f38])).
% 2.97/1.01  
% 2.97/1.01  fof(f44,plain,(
% 2.97/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f43,plain,(
% 2.97/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f42,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f41,plain,(
% 2.97/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.97/1.01    introduced(choice_axiom,[])).
% 2.97/1.01  
% 2.97/1.01  fof(f45,plain,(
% 2.97/1.01    (((k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f44,f43,f42,f41])).
% 2.97/1.01  
% 2.97/1.01  fof(f75,plain,(
% 2.97/1.01    m1_subset_1(sK5,sK1)),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f3,axiom,(
% 2.97/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f19,plain,(
% 2.97/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.97/1.01    inference(ennf_transformation,[],[f3])).
% 2.97/1.01  
% 2.97/1.01  fof(f20,plain,(
% 2.97/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.97/1.01    inference(flattening,[],[f19])).
% 2.97/1.01  
% 2.97/1.01  fof(f48,plain,(
% 2.97/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f20])).
% 2.97/1.01  
% 2.97/1.01  fof(f77,plain,(
% 2.97/1.01    k1_xboole_0 != sK1),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f2,axiom,(
% 2.97/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f18,plain,(
% 2.97/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f2])).
% 2.97/1.01  
% 2.97/1.01  fof(f47,plain,(
% 2.97/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f18])).
% 2.97/1.01  
% 2.97/1.01  fof(f72,plain,(
% 2.97/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f8,axiom,(
% 2.97/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f25,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.01    inference(ennf_transformation,[],[f8])).
% 2.97/1.01  
% 2.97/1.01  fof(f53,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.01    inference(cnf_transformation,[],[f25])).
% 2.97/1.01  
% 2.97/1.01  fof(f13,axiom,(
% 2.97/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f34,plain,(
% 2.97/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.97/1.01    inference(ennf_transformation,[],[f13])).
% 2.97/1.01  
% 2.97/1.01  fof(f35,plain,(
% 2.97/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.97/1.01    inference(flattening,[],[f34])).
% 2.97/1.01  
% 2.97/1.01  fof(f67,plain,(
% 2.97/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f35])).
% 2.97/1.01  
% 2.97/1.01  fof(f76,plain,(
% 2.97/1.01    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f74,plain,(
% 2.97/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f7,axiom,(
% 2.97/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f24,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.01    inference(ennf_transformation,[],[f7])).
% 2.97/1.01  
% 2.97/1.01  fof(f52,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.01    inference(cnf_transformation,[],[f24])).
% 2.97/1.01  
% 2.97/1.01  fof(f70,plain,(
% 2.97/1.01    v1_funct_1(sK3)),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f4,axiom,(
% 2.97/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f21,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.01    inference(ennf_transformation,[],[f4])).
% 2.97/1.01  
% 2.97/1.01  fof(f49,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.01    inference(cnf_transformation,[],[f21])).
% 2.97/1.01  
% 2.97/1.01  fof(f10,axiom,(
% 2.97/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f28,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.01    inference(ennf_transformation,[],[f10])).
% 2.97/1.01  
% 2.97/1.01  fof(f29,plain,(
% 2.97/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.01    inference(flattening,[],[f28])).
% 2.97/1.01  
% 2.97/1.01  fof(f40,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.01    inference(nnf_transformation,[],[f29])).
% 2.97/1.01  
% 2.97/1.01  fof(f57,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.01    inference(cnf_transformation,[],[f40])).
% 2.97/1.01  
% 2.97/1.01  fof(f69,plain,(
% 2.97/1.01    ~v1_xboole_0(sK2)),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f71,plain,(
% 2.97/1.01    v1_funct_2(sK3,sK1,sK2)),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f1,axiom,(
% 2.97/1.01    v1_xboole_0(k1_xboole_0)),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f46,plain,(
% 2.97/1.01    v1_xboole_0(k1_xboole_0)),
% 2.97/1.01    inference(cnf_transformation,[],[f1])).
% 2.97/1.01  
% 2.97/1.01  fof(f14,axiom,(
% 2.97/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f36,plain,(
% 2.97/1.01    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.97/1.01    inference(ennf_transformation,[],[f14])).
% 2.97/1.01  
% 2.97/1.01  fof(f37,plain,(
% 2.97/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.97/1.01    inference(flattening,[],[f36])).
% 2.97/1.01  
% 2.97/1.01  fof(f68,plain,(
% 2.97/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f37])).
% 2.97/1.01  
% 2.97/1.01  fof(f66,plain,(
% 2.97/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f35])).
% 2.97/1.01  
% 2.97/1.01  fof(f5,axiom,(
% 2.97/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f17,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.97/1.01    inference(pure_predicate_removal,[],[f5])).
% 2.97/1.01  
% 2.97/1.01  fof(f22,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/1.01    inference(ennf_transformation,[],[f17])).
% 2.97/1.01  
% 2.97/1.01  fof(f50,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/1.01    inference(cnf_transformation,[],[f22])).
% 2.97/1.01  
% 2.97/1.01  fof(f11,axiom,(
% 2.97/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f30,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.97/1.01    inference(ennf_transformation,[],[f11])).
% 2.97/1.01  
% 2.97/1.01  fof(f31,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.97/1.01    inference(flattening,[],[f30])).
% 2.97/1.01  
% 2.97/1.01  fof(f63,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f31])).
% 2.97/1.01  
% 2.97/1.01  fof(f73,plain,(
% 2.97/1.01    v1_funct_1(sK4)),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f12,axiom,(
% 2.97/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f32,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.97/1.01    inference(ennf_transformation,[],[f12])).
% 2.97/1.01  
% 2.97/1.01  fof(f33,plain,(
% 2.97/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.97/1.01    inference(flattening,[],[f32])).
% 2.97/1.01  
% 2.97/1.01  fof(f64,plain,(
% 2.97/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f33])).
% 2.97/1.01  
% 2.97/1.01  fof(f78,plain,(
% 2.97/1.01    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 2.97/1.01    inference(cnf_transformation,[],[f45])).
% 2.97/1.01  
% 2.97/1.01  fof(f6,axiom,(
% 2.97/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f23,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.97/1.01    inference(ennf_transformation,[],[f6])).
% 2.97/1.01  
% 2.97/1.01  fof(f51,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f23])).
% 2.97/1.01  
% 2.97/1.01  fof(f9,axiom,(
% 2.97/1.01    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 2.97/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/1.01  
% 2.97/1.01  fof(f26,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.97/1.01    inference(ennf_transformation,[],[f9])).
% 2.97/1.01  
% 2.97/1.01  fof(f27,plain,(
% 2.97/1.01    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.97/1.01    inference(flattening,[],[f26])).
% 2.97/1.01  
% 2.97/1.01  fof(f55,plain,(
% 2.97/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.97/1.01    inference(cnf_transformation,[],[f27])).
% 2.97/1.01  
% 2.97/1.01  cnf(c_26,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK5,sK1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2110,plain,
% 2.97/1.01      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.97/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2123,plain,
% 2.97/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.97/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.97/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3306,plain,
% 2.97/1.01      ( r2_hidden(sK5,sK1) = iProver_top
% 2.97/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2110,c_2123]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_39,plain,
% 2.97/1.01      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_24,negated_conjecture,
% 2.97/1.01      ( k1_xboole_0 != sK1 ),
% 2.97/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1,plain,
% 2.97/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.97/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2360,plain,
% 2.97/1.01      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2361,plain,
% 2.97/1.01      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2360]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2516,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) | v1_xboole_0(sK1) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2709,plain,
% 2.97/1.01      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | v1_xboole_0(sK1) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_2516]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2710,plain,
% 2.97/1.01      ( m1_subset_1(sK5,sK1) != iProver_top
% 2.97/1.01      | r2_hidden(sK5,sK1) = iProver_top
% 2.97/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2709]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3862,plain,
% 2.97/1.01      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_3306,c_39,c_24,c_2361,c_2710]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_29,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.97/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2107,plain,
% 2.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_7,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2119,plain,
% 2.97/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3150,plain,
% 2.97/1.01      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2107,c_2119]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_19,plain,
% 2.97/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_25,negated_conjecture,
% 2.97/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.97/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_445,plain,
% 2.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0)
% 2.97/1.01      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.97/1.01      | k1_relset_1(sK2,sK0,sK4) != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_446,plain,
% 2.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0)
% 2.97/1.01      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_445]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2100,plain,
% 2.97/1.01      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3384,plain,
% 2.97/1.01      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_3150,c_2100]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_27,negated_conjecture,
% 2.97/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.97/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2109,plain,
% 2.97/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_6,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2120,plain,
% 2.97/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3158,plain,
% 2.97/1.01      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2109,c_2120]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4397,plain,
% 2.97/1.01      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.97/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_relat_1(sK4)))) = iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(light_normalisation,[status(thm)],[c_3384,c_3158]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4405,plain,
% 2.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top
% 2.97/1.01      | v1_funct_1(sK3) != iProver_top
% 2.97/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.97/1.01      inference(equality_resolution,[status(thm)],[c_4397]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_31,negated_conjecture,
% 2.97/1.01      ( v1_funct_1(sK3) ),
% 2.97/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_34,plain,
% 2.97/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_36,plain,
% 2.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | v1_relat_1(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2369,plain,
% 2.97/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.97/1.01      | v1_relat_1(sK3) ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2370,plain,
% 2.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.97/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_2369]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5379,plain,
% 2.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_relat_1(sK4)))) = iProver_top ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_4405,c_34,c_36,c_2370]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_16,plain,
% 2.97/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.97/1.01      | k1_xboole_0 = X2 ),
% 2.97/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2112,plain,
% 2.97/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 2.97/1.01      | k1_xboole_0 = X1
% 2.97/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4459,plain,
% 2.97/1.01      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 2.97/1.01      | sK2 = k1_xboole_0
% 2.97/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2107,c_2112]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3159,plain,
% 2.97/1.01      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2107,c_2120]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4463,plain,
% 2.97/1.01      ( k1_relat_1(sK3) = sK1
% 2.97/1.01      | sK2 = k1_xboole_0
% 2.97/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_4459,c_3159]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_32,negated_conjecture,
% 2.97/1.01      ( ~ v1_xboole_0(sK2) ),
% 2.97/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_30,negated_conjecture,
% 2.97/1.01      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.97/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_35,plain,
% 2.97/1.01      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_0,plain,
% 2.97/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1637,plain,
% 2.97/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.97/1.01      theory(equality) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2372,plain,
% 2.97/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_1637]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2374,plain,
% 2.97/1.01      ( v1_xboole_0(sK2)
% 2.97/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.97/1.01      | sK2 != k1_xboole_0 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_2372]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4813,plain,
% 2.97/1.01      ( k1_relat_1(sK3) = sK1 ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_4463,c_32,c_35,c_0,c_2374]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5383,plain,
% 2.97/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
% 2.97/1.01      inference(light_normalisation,[status(thm)],[c_5379,c_4813]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_22,plain,
% 2.97/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ r2_hidden(X3,X1)
% 2.97/1.01      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | k1_xboole_0 = X2 ),
% 2.97/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2111,plain,
% 2.97/1.01      ( k1_xboole_0 = X0
% 2.97/1.01      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.97/1.01      | r2_hidden(X3,X2) != iProver_top
% 2.97/1.01      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 2.97/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5393,plain,
% 2.97/1.01      ( k1_relat_1(sK4) = k1_xboole_0
% 2.97/1.01      | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
% 2.97/1.01      | r2_hidden(X0,sK1) != iProver_top
% 2.97/1.01      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.97/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_5383,c_2111]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_20,plain,
% 2.97/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.97/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_427,plain,
% 2.97/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0)
% 2.97/1.01      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.97/1.01      | k1_relset_1(sK2,sK0,sK4) != X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_428,plain,
% 2.97/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0)
% 2.97/1.01      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_427]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2101,plain,
% 2.97/1.01      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(X0)
% 2.97/1.01      | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3383,plain,
% 2.97/1.01      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.97/1.01      | v1_funct_2(X0,k1_relat_1(X0),k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_3150,c_2101]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4328,plain,
% 2.97/1.01      ( k2_relat_1(X0) != k2_relat_1(sK3)
% 2.97/1.01      | v1_funct_2(X0,k1_relat_1(X0),k1_relat_1(sK4)) = iProver_top
% 2.97/1.01      | v1_funct_1(X0) != iProver_top
% 2.97/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.97/1.01      inference(light_normalisation,[status(thm)],[c_3383,c_3158]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4336,plain,
% 2.97/1.01      ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top
% 2.97/1.01      | v1_funct_1(sK3) != iProver_top
% 2.97/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.97/1.01      inference(equality_resolution,[status(thm)],[c_4328]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5128,plain,
% 2.97/1.01      ( v1_funct_2(sK3,k1_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_4336,c_34,c_36,c_2370]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5132,plain,
% 2.97/1.01      ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.97/1.01      inference(light_normalisation,[status(thm)],[c_5128,c_4813]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5780,plain,
% 2.97/1.01      ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.97/1.01      | r2_hidden(X0,sK1) != iProver_top
% 2.97/1.01      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_5393,c_34,c_5132]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5781,plain,
% 2.97/1.01      ( k1_relat_1(sK4) = k1_xboole_0
% 2.97/1.01      | r2_hidden(X0,sK1) != iProver_top
% 2.97/1.01      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_5780]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_4,plain,
% 2.97/1.01      ( v5_relat_1(X0,X1)
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.97/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_17,plain,
% 2.97/1.01      ( ~ v5_relat_1(X0,X1)
% 2.97/1.01      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0)
% 2.97/1.01      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.97/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_321,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_relat_1(X0)
% 2.97/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.97/1.01      inference(resolution,[status(thm)],[c_4,c_17]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_325,plain,
% 2.97/1.01      ( ~ v1_funct_1(X0)
% 2.97/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_321,c_3]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_326,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_325]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2103,plain,
% 2.97/1.01      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.97/1.01      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.97/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2993,plain,
% 2.97/1.01      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.97/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.97/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2109,c_2103]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_28,negated_conjecture,
% 2.97/1.01      ( v1_funct_1(sK4) ),
% 2.97/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_37,plain,
% 2.97/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3674,plain,
% 2.97/1.01      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.97/1.01      | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_2993,c_37]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_3675,plain,
% 2.97/1.01      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.97/1.01      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_3674]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5789,plain,
% 2.97/1.01      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.97/1.01      | k1_relat_1(sK4) = k1_xboole_0
% 2.97/1.01      | r2_hidden(X0,sK1) != iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_5781,c_3675]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5797,plain,
% 2.97/1.01      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.97/1.01      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_3862,c_5789]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_18,plain,
% 2.97/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.97/1.01      | ~ m1_subset_1(X5,X1)
% 2.97/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ v1_funct_1(X4)
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | v1_xboole_0(X2)
% 2.97/1.01      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.97/1.01      | k1_xboole_0 = X1 ),
% 2.97/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_391,plain,
% 2.97/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.01      | ~ m1_subset_1(X3,X1)
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_funct_1(X4)
% 2.97/1.01      | v1_xboole_0(X2)
% 2.97/1.01      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.97/1.01      | k1_relset_1(X2,X5,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.97/1.01      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.97/1.01      | k1_xboole_0 = X1 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2102,plain,
% 2.97/1.01      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.97/1.01      | k1_relset_1(X1,X3,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.97/1.01      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.97/1.01      | k1_xboole_0 = X0
% 2.97/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.97/1.01      | m1_subset_1(X5,X0) != iProver_top
% 2.97/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.97/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 2.97/1.01      | v1_funct_1(X2) != iProver_top
% 2.97/1.01      | v1_funct_1(X4) != iProver_top
% 2.97/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2785,plain,
% 2.97/1.01      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.97/1.01      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.97/1.01      | sK1 = k1_xboole_0
% 2.97/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.97/1.01      | m1_subset_1(X2,sK1) != iProver_top
% 2.97/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.97/1.01      | v1_funct_1(X1) != iProver_top
% 2.97/1.01      | v1_funct_1(sK3) != iProver_top
% 2.97/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.97/1.01      inference(equality_resolution,[status(thm)],[c_2102]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_33,plain,
% 2.97/1.01      ( v1_xboole_0(sK2) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_95,plain,
% 2.97/1.01      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_1636,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2406,plain,
% 2.97/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_1636]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2407,plain,
% 2.97/1.01      ( sK1 != k1_xboole_0
% 2.97/1.01      | k1_xboole_0 = sK1
% 2.97/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.97/1.01      inference(instantiation,[status(thm)],[c_2406]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2790,plain,
% 2.97/1.01      ( m1_subset_1(X2,sK1) != iProver_top
% 2.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.97/1.01      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.97/1.01      | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.97/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_2785,c_33,c_34,c_35,c_36,c_24,c_95,c_0,c_2407]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2791,plain,
% 2.97/1.01      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.97/1.01      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.97/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.97/1.01      | m1_subset_1(X2,sK1) != iProver_top
% 2.97/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.97/1.01      inference(renaming,[status(thm)],[c_2790]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2801,plain,
% 2.97/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.97/1.01      | m1_subset_1(X0,sK1) != iProver_top
% 2.97/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.97/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.97/1.01      inference(equality_resolution,[status(thm)],[c_2791]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_38,plain,
% 2.97/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2855,plain,
% 2.97/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.97/1.01      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_2801,c_37,c_38]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2863,plain,
% 2.97/1.01      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_2110,c_2855]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_23,negated_conjecture,
% 2.97/1.01      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.97/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2865,plain,
% 2.97/1.01      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_2863,c_23]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5880,plain,
% 2.97/1.01      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_5797,c_2865]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ v1_xboole_0(X2)
% 2.97/1.01      | v1_xboole_0(X0) ),
% 2.97/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_2121,plain,
% 2.97/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.97/1.01      | v1_xboole_0(X2) != iProver_top
% 2.97/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5391,plain,
% 2.97/1.01      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
% 2.97/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.97/1.01      inference(superposition,[status(thm)],[c_5383,c_2121]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_9,plain,
% 2.97/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_xboole_0(X0)
% 2.97/1.01      | v1_xboole_0(X1)
% 2.97/1.01      | v1_xboole_0(X2) ),
% 2.97/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_689,plain,
% 2.97/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/1.01      | ~ v1_funct_1(X0)
% 2.97/1.01      | ~ v1_xboole_0(X0)
% 2.97/1.01      | v1_xboole_0(X1)
% 2.97/1.01      | v1_xboole_0(X2)
% 2.97/1.01      | sK2 != X2
% 2.97/1.01      | sK1 != X1
% 2.97/1.01      | sK3 != X0 ),
% 2.97/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_690,plain,
% 2.97/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.97/1.01      | ~ v1_funct_1(sK3)
% 2.97/1.01      | v1_xboole_0(sK2)
% 2.97/1.01      | v1_xboole_0(sK1)
% 2.97/1.01      | ~ v1_xboole_0(sK3) ),
% 2.97/1.01      inference(unflattening,[status(thm)],[c_689]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_692,plain,
% 2.97/1.01      ( v1_xboole_0(sK1) | ~ v1_xboole_0(sK3) ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_690,c_32,c_31,c_29]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_694,plain,
% 2.97/1.01      ( v1_xboole_0(sK1) = iProver_top
% 2.97/1.01      | v1_xboole_0(sK3) != iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5496,plain,
% 2.97/1.01      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 2.97/1.01      inference(global_propositional_subsumption,
% 2.97/1.01                [status(thm)],
% 2.97/1.01                [c_5391,c_24,c_694,c_2361]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_5889,plain,
% 2.97/1.01      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.97/1.01      inference(demodulation,[status(thm)],[c_5880,c_5496]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(c_97,plain,
% 2.97/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.97/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.97/1.01  
% 2.97/1.01  cnf(contradiction,plain,
% 2.97/1.01      ( $false ),
% 2.97/1.01      inference(minisat,[status(thm)],[c_5889,c_97]) ).
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.01  
% 2.97/1.01  ------                               Statistics
% 2.97/1.01  
% 2.97/1.01  ------ General
% 2.97/1.01  
% 2.97/1.01  abstr_ref_over_cycles:                  0
% 2.97/1.01  abstr_ref_under_cycles:                 0
% 2.97/1.01  gc_basic_clause_elim:                   0
% 2.97/1.01  forced_gc_time:                         0
% 2.97/1.01  parsing_time:                           0.015
% 2.97/1.01  unif_index_cands_time:                  0.
% 2.97/1.01  unif_index_add_time:                    0.
% 2.97/1.01  orderings_time:                         0.
% 2.97/1.01  out_proof_time:                         0.01
% 2.97/1.01  total_time:                             0.265
% 2.97/1.01  num_of_symbols:                         55
% 2.97/1.01  num_of_terms:                           8263
% 2.97/1.01  
% 2.97/1.01  ------ Preprocessing
% 2.97/1.01  
% 2.97/1.01  num_of_splits:                          0
% 2.97/1.01  num_of_split_atoms:                     0
% 2.97/1.01  num_of_reused_defs:                     0
% 2.97/1.01  num_eq_ax_congr_red:                    11
% 2.97/1.01  num_of_sem_filtered_clauses:            1
% 2.97/1.01  num_of_subtypes:                        0
% 2.97/1.01  monotx_restored_types:                  0
% 2.97/1.01  sat_num_of_epr_types:                   0
% 2.97/1.01  sat_num_of_non_cyclic_types:            0
% 2.97/1.01  sat_guarded_non_collapsed_types:        0
% 2.97/1.01  num_pure_diseq_elim:                    0
% 2.97/1.01  simp_replaced_by:                       0
% 2.97/1.01  res_preprocessed:                       143
% 2.97/1.01  prep_upred:                             0
% 2.97/1.01  prep_unflattend:                        142
% 2.97/1.01  smt_new_axioms:                         0
% 2.97/1.01  pred_elim_cands:                        6
% 2.97/1.01  pred_elim:                              2
% 2.97/1.01  pred_elim_cl:                           2
% 2.97/1.01  pred_elim_cycles:                       7
% 2.97/1.01  merged_defs:                            0
% 2.97/1.01  merged_defs_ncl:                        0
% 2.97/1.01  bin_hyper_res:                          0
% 2.97/1.01  prep_cycles:                            4
% 2.97/1.01  pred_elim_time:                         0.035
% 2.97/1.01  splitting_time:                         0.
% 2.97/1.01  sem_filter_time:                        0.
% 2.97/1.01  monotx_time:                            0.
% 2.97/1.01  subtype_inf_time:                       0.
% 2.97/1.01  
% 2.97/1.01  ------ Problem properties
% 2.97/1.01  
% 2.97/1.01  clauses:                                28
% 2.97/1.01  conjectures:                            9
% 2.97/1.01  epr:                                    9
% 2.97/1.01  horn:                                   20
% 2.97/1.01  ground:                                 10
% 2.97/1.01  unary:                                  10
% 2.97/1.01  binary:                                 4
% 2.97/1.01  lits:                                   80
% 2.97/1.01  lits_eq:                                22
% 2.97/1.01  fd_pure:                                0
% 2.97/1.01  fd_pseudo:                              0
% 2.97/1.01  fd_cond:                                6
% 2.97/1.01  fd_pseudo_cond:                         0
% 2.97/1.01  ac_symbols:                             0
% 2.97/1.01  
% 2.97/1.01  ------ Propositional Solver
% 2.97/1.01  
% 2.97/1.01  prop_solver_calls:                      27
% 2.97/1.01  prop_fast_solver_calls:                 1511
% 2.97/1.01  smt_solver_calls:                       0
% 2.97/1.01  smt_fast_solver_calls:                  0
% 2.97/1.01  prop_num_of_clauses:                    1973
% 2.97/1.01  prop_preprocess_simplified:             6060
% 2.97/1.01  prop_fo_subsumed:                       74
% 2.97/1.01  prop_solver_time:                       0.
% 2.97/1.01  smt_solver_time:                        0.
% 2.97/1.01  smt_fast_solver_time:                   0.
% 2.97/1.01  prop_fast_solver_time:                  0.
% 2.97/1.01  prop_unsat_core_time:                   0.
% 2.97/1.01  
% 2.97/1.01  ------ QBF
% 2.97/1.01  
% 2.97/1.01  qbf_q_res:                              0
% 2.97/1.01  qbf_num_tautologies:                    0
% 2.97/1.01  qbf_prep_cycles:                        0
% 2.97/1.01  
% 2.97/1.01  ------ BMC1
% 2.97/1.01  
% 2.97/1.01  bmc1_current_bound:                     -1
% 2.97/1.01  bmc1_last_solved_bound:                 -1
% 2.97/1.01  bmc1_unsat_core_size:                   -1
% 2.97/1.01  bmc1_unsat_core_parents_size:           -1
% 2.97/1.01  bmc1_merge_next_fun:                    0
% 2.97/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.01  
% 2.97/1.01  ------ Instantiation
% 2.97/1.01  
% 2.97/1.01  inst_num_of_clauses:                    599
% 2.97/1.01  inst_num_in_passive:                    9
% 2.97/1.01  inst_num_in_active:                     349
% 2.97/1.01  inst_num_in_unprocessed:                241
% 2.97/1.01  inst_num_of_loops:                      360
% 2.97/1.01  inst_num_of_learning_restarts:          0
% 2.97/1.01  inst_num_moves_active_passive:          8
% 2.97/1.01  inst_lit_activity:                      0
% 2.97/1.01  inst_lit_activity_moves:                0
% 2.97/1.01  inst_num_tautologies:                   0
% 2.97/1.01  inst_num_prop_implied:                  0
% 2.97/1.01  inst_num_existing_simplified:           0
% 2.97/1.01  inst_num_eq_res_simplified:             0
% 2.97/1.01  inst_num_child_elim:                    0
% 2.97/1.01  inst_num_of_dismatching_blockings:      41
% 2.97/1.01  inst_num_of_non_proper_insts:           431
% 2.97/1.01  inst_num_of_duplicates:                 0
% 2.97/1.01  inst_inst_num_from_inst_to_res:         0
% 2.97/1.01  inst_dismatching_checking_time:         0.
% 2.97/1.01  
% 2.97/1.01  ------ Resolution
% 2.97/1.01  
% 2.97/1.01  res_num_of_clauses:                     0
% 2.97/1.01  res_num_in_passive:                     0
% 2.97/1.01  res_num_in_active:                      0
% 2.97/1.01  res_num_of_loops:                       147
% 2.97/1.01  res_forward_subset_subsumed:            47
% 2.97/1.01  res_backward_subset_subsumed:           0
% 2.97/1.01  res_forward_subsumed:                   2
% 2.97/1.01  res_backward_subsumed:                  0
% 2.97/1.01  res_forward_subsumption_resolution:     5
% 2.97/1.01  res_backward_subsumption_resolution:    0
% 2.97/1.01  res_clause_to_clause_subsumption:       239
% 2.97/1.01  res_orphan_elimination:                 0
% 2.97/1.01  res_tautology_del:                      72
% 2.97/1.01  res_num_eq_res_simplified:              0
% 2.97/1.01  res_num_sel_changes:                    0
% 2.97/1.01  res_moves_from_active_to_pass:          0
% 2.97/1.01  
% 2.97/1.01  ------ Superposition
% 2.97/1.01  
% 2.97/1.01  sup_time_total:                         0.
% 2.97/1.01  sup_time_generating:                    0.
% 2.97/1.01  sup_time_sim_full:                      0.
% 2.97/1.01  sup_time_sim_immed:                     0.
% 2.97/1.01  
% 2.97/1.01  sup_num_of_clauses:                     51
% 2.97/1.01  sup_num_in_active:                      43
% 2.97/1.01  sup_num_in_passive:                     8
% 2.97/1.01  sup_num_of_loops:                       70
% 2.97/1.01  sup_fw_superposition:                   29
% 2.97/1.01  sup_bw_superposition:                   14
% 2.97/1.01  sup_immediate_simplified:               12
% 2.97/1.01  sup_given_eliminated:                   0
% 2.97/1.01  comparisons_done:                       0
% 2.97/1.01  comparisons_avoided:                    3
% 2.97/1.01  
% 2.97/1.01  ------ Simplifications
% 2.97/1.01  
% 2.97/1.01  
% 2.97/1.01  sim_fw_subset_subsumed:                 6
% 2.97/1.01  sim_bw_subset_subsumed:                 1
% 2.97/1.01  sim_fw_subsumed:                        2
% 2.97/1.01  sim_bw_subsumed:                        0
% 2.97/1.01  sim_fw_subsumption_res:                 0
% 2.97/1.01  sim_bw_subsumption_res:                 0
% 2.97/1.01  sim_tautology_del:                      0
% 2.97/1.01  sim_eq_tautology_del:                   2
% 2.97/1.01  sim_eq_res_simp:                        0
% 2.97/1.01  sim_fw_demodulated:                     2
% 2.97/1.01  sim_bw_demodulated:                     26
% 2.97/1.01  sim_light_normalised:                   8
% 2.97/1.01  sim_joinable_taut:                      0
% 2.97/1.01  sim_joinable_simp:                      0
% 2.97/1.01  sim_ac_normalised:                      0
% 2.97/1.01  sim_smt_subsumption:                    0
% 2.97/1.01  
%------------------------------------------------------------------------------
