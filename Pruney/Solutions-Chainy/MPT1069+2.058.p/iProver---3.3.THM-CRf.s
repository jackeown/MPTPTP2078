%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:54 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 496 expanded)
%              Number of clauses        :   91 ( 141 expanded)
%              Number of leaves         :   19 ( 163 expanded)
%              Depth                    :   19
%              Number of atoms          :  566 (3634 expanded)
%              Number of equality atoms :  233 ( 978 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f43,f42,f41,f40])).

fof(f71,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1779,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_787,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | X1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_1774,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_3665,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1774])).

cnf(c_36,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2015,plain,
    ( ~ m1_subset_1(X0,sK1)
    | r2_hidden(X0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_2112,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_2113,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2112])).

cnf(c_3715,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3665,c_36,c_21,c_2113])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1778,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1784,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2197,plain,
    ( v5_relat_1(sK4,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_1784])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1776,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1782,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2293,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1776,c_1782])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1780,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2409,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2293,c_1780])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1789,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v5_relat_1(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2845,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_1789])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1976,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2130,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_2131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2159,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2160,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2159])).

cnf(c_3476,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2845,c_33,c_2131,c_2160])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1783,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2758,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1778,c_1783])).

cnf(c_3480,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3476,c_2758])).

cnf(c_2759,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1776,c_1783])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_749,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_750,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_749])).

cnf(c_752,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_750,c_26])).

cnf(c_3110,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2759,c_752])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_313,plain,
    ( sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_29])).

cnf(c_3311,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3110,c_313])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1785,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1786,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3693,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1786])).

cnf(c_18,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1781,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4200,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3693,c_1781])).

cnf(c_4855,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(sK3,X2)) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(sK3,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3311,c_4200])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5086,plain,
    ( v1_relat_1(X1) != iProver_top
    | k7_partfun1(X0,X1,k1_funct_1(sK3,X2)) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(sK3,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4855,c_31,c_33,c_2131,c_2160])).

cnf(c_5087,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(sK3,X2)) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(sK3,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5086])).

cnf(c_5098,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3480,c_5087])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_35,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2127,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_2128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2127])).

cnf(c_2156,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2157,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

cnf(c_6111,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5098,c_34,c_35,c_2128,c_2157])).

cnf(c_6120,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2197,c_6111])).

cnf(c_6146,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3715,c_6120])).

cnf(c_19,plain,
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

cnf(c_722,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_723,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_727,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_723,c_29,c_28,c_26,c_21])).

cnf(c_728,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(X2,sK1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
    inference(renaming,[status(thm)],[c_727])).

cnf(c_1770,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2634,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1770,c_2293])).

cnf(c_2643,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2409,c_2634])).

cnf(c_3919,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2643,c_34,c_35])).

cnf(c_3927,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1779,c_3919])).

cnf(c_20,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3929,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3927,c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6146,c_3929])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.32  % Computer   : n022.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 13:09:55 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running in FOF mode
% 2.72/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/0.98  
% 2.72/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/0.98  
% 2.72/0.98  ------  iProver source info
% 2.72/0.98  
% 2.72/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.72/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/0.98  git: non_committed_changes: false
% 2.72/0.98  git: last_make_outside_of_git: false
% 2.72/0.98  
% 2.72/0.98  ------ 
% 2.72/0.98  
% 2.72/0.98  ------ Input Options
% 2.72/0.98  
% 2.72/0.98  --out_options                           all
% 2.72/0.98  --tptp_safe_out                         true
% 2.72/0.98  --problem_path                          ""
% 2.72/0.98  --include_path                          ""
% 2.72/0.98  --clausifier                            res/vclausify_rel
% 2.72/0.98  --clausifier_options                    --mode clausify
% 2.72/0.98  --stdin                                 false
% 2.72/0.98  --stats_out                             all
% 2.72/0.98  
% 2.72/0.98  ------ General Options
% 2.72/0.98  
% 2.72/0.98  --fof                                   false
% 2.72/0.98  --time_out_real                         305.
% 2.72/0.98  --time_out_virtual                      -1.
% 2.72/0.98  --symbol_type_check                     false
% 2.72/0.98  --clausify_out                          false
% 2.72/0.98  --sig_cnt_out                           false
% 2.72/0.98  --trig_cnt_out                          false
% 2.72/0.98  --trig_cnt_out_tolerance                1.
% 2.72/0.98  --trig_cnt_out_sk_spl                   false
% 2.72/0.98  --abstr_cl_out                          false
% 2.72/0.98  
% 2.72/0.98  ------ Global Options
% 2.72/0.98  
% 2.72/0.98  --schedule                              default
% 2.72/0.98  --add_important_lit                     false
% 2.72/0.98  --prop_solver_per_cl                    1000
% 2.72/0.98  --min_unsat_core                        false
% 2.72/0.98  --soft_assumptions                      false
% 2.72/0.98  --soft_lemma_size                       3
% 2.72/0.98  --prop_impl_unit_size                   0
% 2.72/0.98  --prop_impl_unit                        []
% 2.72/0.98  --share_sel_clauses                     true
% 2.72/0.98  --reset_solvers                         false
% 2.72/0.98  --bc_imp_inh                            [conj_cone]
% 2.72/0.98  --conj_cone_tolerance                   3.
% 2.72/0.98  --extra_neg_conj                        none
% 2.72/0.98  --large_theory_mode                     true
% 2.72/0.98  --prolific_symb_bound                   200
% 2.72/0.98  --lt_threshold                          2000
% 2.72/0.98  --clause_weak_htbl                      true
% 2.72/0.98  --gc_record_bc_elim                     false
% 2.72/0.98  
% 2.72/0.98  ------ Preprocessing Options
% 2.72/0.98  
% 2.72/0.98  --preprocessing_flag                    true
% 2.72/0.98  --time_out_prep_mult                    0.1
% 2.72/0.98  --splitting_mode                        input
% 2.72/0.98  --splitting_grd                         true
% 2.72/0.98  --splitting_cvd                         false
% 2.72/0.98  --splitting_cvd_svl                     false
% 2.72/0.98  --splitting_nvd                         32
% 2.72/0.98  --sub_typing                            true
% 2.72/0.98  --prep_gs_sim                           true
% 2.72/0.98  --prep_unflatten                        true
% 2.72/0.98  --prep_res_sim                          true
% 2.72/0.98  --prep_upred                            true
% 2.72/0.98  --prep_sem_filter                       exhaustive
% 2.72/0.98  --prep_sem_filter_out                   false
% 2.72/0.98  --pred_elim                             true
% 2.72/0.98  --res_sim_input                         true
% 2.72/0.98  --eq_ax_congr_red                       true
% 2.72/0.98  --pure_diseq_elim                       true
% 2.72/0.98  --brand_transform                       false
% 2.72/0.98  --non_eq_to_eq                          false
% 2.72/0.98  --prep_def_merge                        true
% 2.72/0.98  --prep_def_merge_prop_impl              false
% 2.72/0.98  --prep_def_merge_mbd                    true
% 2.72/0.98  --prep_def_merge_tr_red                 false
% 2.72/0.98  --prep_def_merge_tr_cl                  false
% 2.72/0.98  --smt_preprocessing                     true
% 2.72/0.98  --smt_ac_axioms                         fast
% 2.72/0.98  --preprocessed_out                      false
% 2.72/0.98  --preprocessed_stats                    false
% 2.72/0.98  
% 2.72/0.98  ------ Abstraction refinement Options
% 2.72/0.98  
% 2.72/0.98  --abstr_ref                             []
% 2.72/0.98  --abstr_ref_prep                        false
% 2.72/0.98  --abstr_ref_until_sat                   false
% 2.72/0.98  --abstr_ref_sig_restrict                funpre
% 2.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.98  --abstr_ref_under                       []
% 2.72/0.98  
% 2.72/0.98  ------ SAT Options
% 2.72/0.98  
% 2.72/0.98  --sat_mode                              false
% 2.72/0.98  --sat_fm_restart_options                ""
% 2.72/0.98  --sat_gr_def                            false
% 2.72/0.98  --sat_epr_types                         true
% 2.72/0.98  --sat_non_cyclic_types                  false
% 2.72/0.98  --sat_finite_models                     false
% 2.72/0.98  --sat_fm_lemmas                         false
% 2.72/0.98  --sat_fm_prep                           false
% 2.72/0.98  --sat_fm_uc_incr                        true
% 2.72/0.98  --sat_out_model                         small
% 2.72/0.98  --sat_out_clauses                       false
% 2.72/0.98  
% 2.72/0.98  ------ QBF Options
% 2.72/0.98  
% 2.72/0.98  --qbf_mode                              false
% 2.72/0.98  --qbf_elim_univ                         false
% 2.72/0.98  --qbf_dom_inst                          none
% 2.72/0.98  --qbf_dom_pre_inst                      false
% 2.72/0.98  --qbf_sk_in                             false
% 2.72/0.98  --qbf_pred_elim                         true
% 2.72/0.98  --qbf_split                             512
% 2.72/0.98  
% 2.72/0.98  ------ BMC1 Options
% 2.72/0.98  
% 2.72/0.98  --bmc1_incremental                      false
% 2.72/0.98  --bmc1_axioms                           reachable_all
% 2.72/0.98  --bmc1_min_bound                        0
% 2.72/0.98  --bmc1_max_bound                        -1
% 2.72/0.98  --bmc1_max_bound_default                -1
% 2.72/0.98  --bmc1_symbol_reachability              true
% 2.72/0.98  --bmc1_property_lemmas                  false
% 2.72/0.98  --bmc1_k_induction                      false
% 2.72/0.98  --bmc1_non_equiv_states                 false
% 2.72/0.98  --bmc1_deadlock                         false
% 2.72/0.98  --bmc1_ucm                              false
% 2.72/0.98  --bmc1_add_unsat_core                   none
% 2.72/0.98  --bmc1_unsat_core_children              false
% 2.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.98  --bmc1_out_stat                         full
% 2.72/0.98  --bmc1_ground_init                      false
% 2.72/0.98  --bmc1_pre_inst_next_state              false
% 2.72/0.98  --bmc1_pre_inst_state                   false
% 2.72/0.98  --bmc1_pre_inst_reach_state             false
% 2.72/0.98  --bmc1_out_unsat_core                   false
% 2.72/0.98  --bmc1_aig_witness_out                  false
% 2.72/0.98  --bmc1_verbose                          false
% 2.72/0.98  --bmc1_dump_clauses_tptp                false
% 2.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.98  --bmc1_dump_file                        -
% 2.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.98  --bmc1_ucm_extend_mode                  1
% 2.72/0.98  --bmc1_ucm_init_mode                    2
% 2.72/0.98  --bmc1_ucm_cone_mode                    none
% 2.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.98  --bmc1_ucm_relax_model                  4
% 2.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.98  --bmc1_ucm_layered_model                none
% 2.72/0.98  --bmc1_ucm_max_lemma_size               10
% 2.72/0.98  
% 2.72/0.98  ------ AIG Options
% 2.72/0.98  
% 2.72/0.98  --aig_mode                              false
% 2.72/0.98  
% 2.72/0.98  ------ Instantiation Options
% 2.72/0.98  
% 2.72/0.98  --instantiation_flag                    true
% 2.72/0.98  --inst_sos_flag                         false
% 2.72/0.98  --inst_sos_phase                        true
% 2.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.98  --inst_lit_sel_side                     num_symb
% 2.72/0.98  --inst_solver_per_active                1400
% 2.72/0.98  --inst_solver_calls_frac                1.
% 2.72/0.98  --inst_passive_queue_type               priority_queues
% 2.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.98  --inst_passive_queues_freq              [25;2]
% 2.72/0.98  --inst_dismatching                      true
% 2.72/0.98  --inst_eager_unprocessed_to_passive     true
% 2.72/0.98  --inst_prop_sim_given                   true
% 2.72/0.98  --inst_prop_sim_new                     false
% 2.72/0.98  --inst_subs_new                         false
% 2.72/0.98  --inst_eq_res_simp                      false
% 2.72/0.98  --inst_subs_given                       false
% 2.72/0.98  --inst_orphan_elimination               true
% 2.72/0.98  --inst_learning_loop_flag               true
% 2.72/0.98  --inst_learning_start                   3000
% 2.72/0.98  --inst_learning_factor                  2
% 2.72/0.98  --inst_start_prop_sim_after_learn       3
% 2.72/0.98  --inst_sel_renew                        solver
% 2.72/0.98  --inst_lit_activity_flag                true
% 2.72/0.98  --inst_restr_to_given                   false
% 2.72/0.98  --inst_activity_threshold               500
% 2.72/0.98  --inst_out_proof                        true
% 2.72/0.98  
% 2.72/0.98  ------ Resolution Options
% 2.72/0.98  
% 2.72/0.98  --resolution_flag                       true
% 2.72/0.98  --res_lit_sel                           adaptive
% 2.72/0.98  --res_lit_sel_side                      none
% 2.72/0.98  --res_ordering                          kbo
% 2.72/0.98  --res_to_prop_solver                    active
% 2.72/0.98  --res_prop_simpl_new                    false
% 2.72/0.98  --res_prop_simpl_given                  true
% 2.72/0.98  --res_passive_queue_type                priority_queues
% 2.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.98  --res_passive_queues_freq               [15;5]
% 2.72/0.98  --res_forward_subs                      full
% 2.72/0.98  --res_backward_subs                     full
% 2.72/0.98  --res_forward_subs_resolution           true
% 2.72/0.98  --res_backward_subs_resolution          true
% 2.72/0.98  --res_orphan_elimination                true
% 2.72/0.98  --res_time_limit                        2.
% 2.72/0.98  --res_out_proof                         true
% 2.72/0.98  
% 2.72/0.98  ------ Superposition Options
% 2.72/0.98  
% 2.72/0.98  --superposition_flag                    true
% 2.72/0.98  --sup_passive_queue_type                priority_queues
% 2.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.98  --demod_completeness_check              fast
% 2.72/0.98  --demod_use_ground                      true
% 2.72/0.98  --sup_to_prop_solver                    passive
% 2.72/0.98  --sup_prop_simpl_new                    true
% 2.72/0.98  --sup_prop_simpl_given                  true
% 2.72/0.98  --sup_fun_splitting                     false
% 2.72/0.98  --sup_smt_interval                      50000
% 2.72/0.98  
% 2.72/0.98  ------ Superposition Simplification Setup
% 2.72/0.98  
% 2.72/0.98  --sup_indices_passive                   []
% 2.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.98  --sup_full_bw                           [BwDemod]
% 2.72/0.98  --sup_immed_triv                        [TrivRules]
% 2.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.98  --sup_immed_bw_main                     []
% 2.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.98  
% 2.72/0.98  ------ Combination Options
% 2.72/0.98  
% 2.72/0.98  --comb_res_mult                         3
% 2.72/0.98  --comb_sup_mult                         2
% 2.72/0.98  --comb_inst_mult                        10
% 2.72/0.98  
% 2.72/0.98  ------ Debug Options
% 2.72/0.98  
% 2.72/0.98  --dbg_backtrace                         false
% 2.72/0.98  --dbg_dump_prop_clauses                 false
% 2.72/0.98  --dbg_dump_prop_clauses_file            -
% 2.72/0.98  --dbg_out_stat                          false
% 2.72/0.98  ------ Parsing...
% 2.72/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/0.98  
% 2.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.72/0.98  
% 2.72/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/0.98  
% 2.72/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/0.98  ------ Proving...
% 2.72/0.98  ------ Problem Properties 
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  clauses                                 25
% 2.72/0.98  conjectures                             8
% 2.72/0.98  EPR                                     7
% 2.72/0.98  Horn                                    22
% 2.72/0.98  unary                                   10
% 2.72/0.98  binary                                  5
% 2.72/0.98  lits                                    63
% 2.72/0.98  lits eq                                 16
% 2.72/0.98  fd_pure                                 0
% 2.72/0.98  fd_pseudo                               0
% 2.72/0.98  fd_cond                                 2
% 2.72/0.98  fd_pseudo_cond                          0
% 2.72/0.98  AC symbols                              0
% 2.72/0.98  
% 2.72/0.98  ------ Schedule dynamic 5 is on 
% 2.72/0.98  
% 2.72/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  ------ 
% 2.72/0.98  Current options:
% 2.72/0.98  ------ 
% 2.72/0.98  
% 2.72/0.98  ------ Input Options
% 2.72/0.98  
% 2.72/0.98  --out_options                           all
% 2.72/0.98  --tptp_safe_out                         true
% 2.72/0.98  --problem_path                          ""
% 2.72/0.98  --include_path                          ""
% 2.72/0.98  --clausifier                            res/vclausify_rel
% 2.72/0.98  --clausifier_options                    --mode clausify
% 2.72/0.98  --stdin                                 false
% 2.72/0.98  --stats_out                             all
% 2.72/0.98  
% 2.72/0.98  ------ General Options
% 2.72/0.98  
% 2.72/0.98  --fof                                   false
% 2.72/0.98  --time_out_real                         305.
% 2.72/0.98  --time_out_virtual                      -1.
% 2.72/0.98  --symbol_type_check                     false
% 2.72/0.98  --clausify_out                          false
% 2.72/0.98  --sig_cnt_out                           false
% 2.72/0.98  --trig_cnt_out                          false
% 2.72/0.98  --trig_cnt_out_tolerance                1.
% 2.72/0.98  --trig_cnt_out_sk_spl                   false
% 2.72/0.98  --abstr_cl_out                          false
% 2.72/0.98  
% 2.72/0.98  ------ Global Options
% 2.72/0.98  
% 2.72/0.98  --schedule                              default
% 2.72/0.98  --add_important_lit                     false
% 2.72/0.98  --prop_solver_per_cl                    1000
% 2.72/0.98  --min_unsat_core                        false
% 2.72/0.98  --soft_assumptions                      false
% 2.72/0.98  --soft_lemma_size                       3
% 2.72/0.98  --prop_impl_unit_size                   0
% 2.72/0.98  --prop_impl_unit                        []
% 2.72/0.98  --share_sel_clauses                     true
% 2.72/0.98  --reset_solvers                         false
% 2.72/0.98  --bc_imp_inh                            [conj_cone]
% 2.72/0.98  --conj_cone_tolerance                   3.
% 2.72/0.98  --extra_neg_conj                        none
% 2.72/0.98  --large_theory_mode                     true
% 2.72/0.98  --prolific_symb_bound                   200
% 2.72/0.98  --lt_threshold                          2000
% 2.72/0.98  --clause_weak_htbl                      true
% 2.72/0.98  --gc_record_bc_elim                     false
% 2.72/0.98  
% 2.72/0.98  ------ Preprocessing Options
% 2.72/0.98  
% 2.72/0.98  --preprocessing_flag                    true
% 2.72/0.98  --time_out_prep_mult                    0.1
% 2.72/0.98  --splitting_mode                        input
% 2.72/0.98  --splitting_grd                         true
% 2.72/0.98  --splitting_cvd                         false
% 2.72/0.98  --splitting_cvd_svl                     false
% 2.72/0.98  --splitting_nvd                         32
% 2.72/0.98  --sub_typing                            true
% 2.72/0.98  --prep_gs_sim                           true
% 2.72/0.98  --prep_unflatten                        true
% 2.72/0.98  --prep_res_sim                          true
% 2.72/0.98  --prep_upred                            true
% 2.72/0.98  --prep_sem_filter                       exhaustive
% 2.72/0.98  --prep_sem_filter_out                   false
% 2.72/0.98  --pred_elim                             true
% 2.72/0.98  --res_sim_input                         true
% 2.72/0.98  --eq_ax_congr_red                       true
% 2.72/0.98  --pure_diseq_elim                       true
% 2.72/0.98  --brand_transform                       false
% 2.72/0.98  --non_eq_to_eq                          false
% 2.72/0.98  --prep_def_merge                        true
% 2.72/0.98  --prep_def_merge_prop_impl              false
% 2.72/0.98  --prep_def_merge_mbd                    true
% 2.72/0.98  --prep_def_merge_tr_red                 false
% 2.72/0.98  --prep_def_merge_tr_cl                  false
% 2.72/0.98  --smt_preprocessing                     true
% 2.72/0.98  --smt_ac_axioms                         fast
% 2.72/0.98  --preprocessed_out                      false
% 2.72/0.98  --preprocessed_stats                    false
% 2.72/0.98  
% 2.72/0.98  ------ Abstraction refinement Options
% 2.72/0.98  
% 2.72/0.98  --abstr_ref                             []
% 2.72/0.98  --abstr_ref_prep                        false
% 2.72/0.98  --abstr_ref_until_sat                   false
% 2.72/0.98  --abstr_ref_sig_restrict                funpre
% 2.72/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.98  --abstr_ref_under                       []
% 2.72/0.98  
% 2.72/0.98  ------ SAT Options
% 2.72/0.98  
% 2.72/0.98  --sat_mode                              false
% 2.72/0.98  --sat_fm_restart_options                ""
% 2.72/0.98  --sat_gr_def                            false
% 2.72/0.98  --sat_epr_types                         true
% 2.72/0.98  --sat_non_cyclic_types                  false
% 2.72/0.98  --sat_finite_models                     false
% 2.72/0.98  --sat_fm_lemmas                         false
% 2.72/0.98  --sat_fm_prep                           false
% 2.72/0.98  --sat_fm_uc_incr                        true
% 2.72/0.98  --sat_out_model                         small
% 2.72/0.98  --sat_out_clauses                       false
% 2.72/0.98  
% 2.72/0.98  ------ QBF Options
% 2.72/0.98  
% 2.72/0.98  --qbf_mode                              false
% 2.72/0.98  --qbf_elim_univ                         false
% 2.72/0.98  --qbf_dom_inst                          none
% 2.72/0.98  --qbf_dom_pre_inst                      false
% 2.72/0.98  --qbf_sk_in                             false
% 2.72/0.98  --qbf_pred_elim                         true
% 2.72/0.98  --qbf_split                             512
% 2.72/0.98  
% 2.72/0.98  ------ BMC1 Options
% 2.72/0.98  
% 2.72/0.98  --bmc1_incremental                      false
% 2.72/0.98  --bmc1_axioms                           reachable_all
% 2.72/0.98  --bmc1_min_bound                        0
% 2.72/0.98  --bmc1_max_bound                        -1
% 2.72/0.98  --bmc1_max_bound_default                -1
% 2.72/0.98  --bmc1_symbol_reachability              true
% 2.72/0.98  --bmc1_property_lemmas                  false
% 2.72/0.98  --bmc1_k_induction                      false
% 2.72/0.98  --bmc1_non_equiv_states                 false
% 2.72/0.98  --bmc1_deadlock                         false
% 2.72/0.98  --bmc1_ucm                              false
% 2.72/0.98  --bmc1_add_unsat_core                   none
% 2.72/0.98  --bmc1_unsat_core_children              false
% 2.72/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.98  --bmc1_out_stat                         full
% 2.72/0.98  --bmc1_ground_init                      false
% 2.72/0.98  --bmc1_pre_inst_next_state              false
% 2.72/0.98  --bmc1_pre_inst_state                   false
% 2.72/0.98  --bmc1_pre_inst_reach_state             false
% 2.72/0.98  --bmc1_out_unsat_core                   false
% 2.72/0.98  --bmc1_aig_witness_out                  false
% 2.72/0.98  --bmc1_verbose                          false
% 2.72/0.98  --bmc1_dump_clauses_tptp                false
% 2.72/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.98  --bmc1_dump_file                        -
% 2.72/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.98  --bmc1_ucm_extend_mode                  1
% 2.72/0.98  --bmc1_ucm_init_mode                    2
% 2.72/0.98  --bmc1_ucm_cone_mode                    none
% 2.72/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.98  --bmc1_ucm_relax_model                  4
% 2.72/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.98  --bmc1_ucm_layered_model                none
% 2.72/0.98  --bmc1_ucm_max_lemma_size               10
% 2.72/0.98  
% 2.72/0.98  ------ AIG Options
% 2.72/0.98  
% 2.72/0.98  --aig_mode                              false
% 2.72/0.98  
% 2.72/0.98  ------ Instantiation Options
% 2.72/0.98  
% 2.72/0.98  --instantiation_flag                    true
% 2.72/0.98  --inst_sos_flag                         false
% 2.72/0.98  --inst_sos_phase                        true
% 2.72/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.98  --inst_lit_sel_side                     none
% 2.72/0.98  --inst_solver_per_active                1400
% 2.72/0.98  --inst_solver_calls_frac                1.
% 2.72/0.98  --inst_passive_queue_type               priority_queues
% 2.72/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.98  --inst_passive_queues_freq              [25;2]
% 2.72/0.98  --inst_dismatching                      true
% 2.72/0.98  --inst_eager_unprocessed_to_passive     true
% 2.72/0.98  --inst_prop_sim_given                   true
% 2.72/0.98  --inst_prop_sim_new                     false
% 2.72/0.98  --inst_subs_new                         false
% 2.72/0.98  --inst_eq_res_simp                      false
% 2.72/0.98  --inst_subs_given                       false
% 2.72/0.98  --inst_orphan_elimination               true
% 2.72/0.98  --inst_learning_loop_flag               true
% 2.72/0.98  --inst_learning_start                   3000
% 2.72/0.98  --inst_learning_factor                  2
% 2.72/0.98  --inst_start_prop_sim_after_learn       3
% 2.72/0.98  --inst_sel_renew                        solver
% 2.72/0.98  --inst_lit_activity_flag                true
% 2.72/0.98  --inst_restr_to_given                   false
% 2.72/0.98  --inst_activity_threshold               500
% 2.72/0.98  --inst_out_proof                        true
% 2.72/0.98  
% 2.72/0.98  ------ Resolution Options
% 2.72/0.98  
% 2.72/0.98  --resolution_flag                       false
% 2.72/0.98  --res_lit_sel                           adaptive
% 2.72/0.98  --res_lit_sel_side                      none
% 2.72/0.98  --res_ordering                          kbo
% 2.72/0.98  --res_to_prop_solver                    active
% 2.72/0.98  --res_prop_simpl_new                    false
% 2.72/0.98  --res_prop_simpl_given                  true
% 2.72/0.98  --res_passive_queue_type                priority_queues
% 2.72/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.98  --res_passive_queues_freq               [15;5]
% 2.72/0.98  --res_forward_subs                      full
% 2.72/0.98  --res_backward_subs                     full
% 2.72/0.98  --res_forward_subs_resolution           true
% 2.72/0.98  --res_backward_subs_resolution          true
% 2.72/0.98  --res_orphan_elimination                true
% 2.72/0.98  --res_time_limit                        2.
% 2.72/0.98  --res_out_proof                         true
% 2.72/0.98  
% 2.72/0.98  ------ Superposition Options
% 2.72/0.98  
% 2.72/0.98  --superposition_flag                    true
% 2.72/0.98  --sup_passive_queue_type                priority_queues
% 2.72/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.98  --demod_completeness_check              fast
% 2.72/0.98  --demod_use_ground                      true
% 2.72/0.98  --sup_to_prop_solver                    passive
% 2.72/0.98  --sup_prop_simpl_new                    true
% 2.72/0.98  --sup_prop_simpl_given                  true
% 2.72/0.98  --sup_fun_splitting                     false
% 2.72/0.98  --sup_smt_interval                      50000
% 2.72/0.98  
% 2.72/0.98  ------ Superposition Simplification Setup
% 2.72/0.98  
% 2.72/0.98  --sup_indices_passive                   []
% 2.72/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.98  --sup_full_bw                           [BwDemod]
% 2.72/0.98  --sup_immed_triv                        [TrivRules]
% 2.72/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.98  --sup_immed_bw_main                     []
% 2.72/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.98  
% 2.72/0.98  ------ Combination Options
% 2.72/0.98  
% 2.72/0.98  --comb_res_mult                         3
% 2.72/0.98  --comb_sup_mult                         2
% 2.72/0.98  --comb_inst_mult                        10
% 2.72/0.98  
% 2.72/0.98  ------ Debug Options
% 2.72/0.98  
% 2.72/0.98  --dbg_backtrace                         false
% 2.72/0.98  --dbg_dump_prop_clauses                 false
% 2.72/0.98  --dbg_dump_prop_clauses_file            -
% 2.72/0.98  --dbg_out_stat                          false
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  ------ Proving...
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  % SZS status Theorem for theBenchmark.p
% 2.72/0.98  
% 2.72/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/0.98  
% 2.72/0.98  fof(f15,conjecture,(
% 2.72/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f16,negated_conjecture,(
% 2.72/0.98    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.72/0.98    inference(negated_conjecture,[],[f15])).
% 2.72/0.98  
% 2.72/0.98  fof(f36,plain,(
% 2.72/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.72/0.98    inference(ennf_transformation,[],[f16])).
% 2.72/0.98  
% 2.72/0.98  fof(f37,plain,(
% 2.72/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.72/0.98    inference(flattening,[],[f36])).
% 2.72/0.98  
% 2.72/0.98  fof(f43,plain,(
% 2.72/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) != k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.72/0.98    introduced(choice_axiom,[])).
% 2.72/0.98  
% 2.72/0.98  fof(f42,plain,(
% 2.72/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) != k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.72/0.98    introduced(choice_axiom,[])).
% 2.72/0.98  
% 2.72/0.98  fof(f41,plain,(
% 2.72/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.72/0.98    introduced(choice_axiom,[])).
% 2.72/0.98  
% 2.72/0.98  fof(f40,plain,(
% 2.72/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.72/0.98    introduced(choice_axiom,[])).
% 2.72/0.98  
% 2.72/0.98  fof(f44,plain,(
% 2.72/0.98    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.72/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f43,f42,f41,f40])).
% 2.72/0.98  
% 2.72/0.98  fof(f71,plain,(
% 2.72/0.98    m1_subset_1(sK5,sK1)),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f2,axiom,(
% 2.72/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f18,plain,(
% 2.72/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.72/0.98    inference(ennf_transformation,[],[f2])).
% 2.72/0.98  
% 2.72/0.98  fof(f46,plain,(
% 2.72/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f18])).
% 2.72/0.98  
% 2.72/0.98  fof(f3,axiom,(
% 2.72/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f19,plain,(
% 2.72/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.72/0.98    inference(ennf_transformation,[],[f3])).
% 2.72/0.98  
% 2.72/0.98  fof(f20,plain,(
% 2.72/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.72/0.98    inference(flattening,[],[f19])).
% 2.72/0.98  
% 2.72/0.98  fof(f47,plain,(
% 2.72/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f20])).
% 2.72/0.98  
% 2.72/0.98  fof(f73,plain,(
% 2.72/0.98    k1_xboole_0 != sK1),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f70,plain,(
% 2.72/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f9,axiom,(
% 2.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f17,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.72/0.98    inference(pure_predicate_removal,[],[f9])).
% 2.72/0.98  
% 2.72/0.98  fof(f27,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.98    inference(ennf_transformation,[],[f17])).
% 2.72/0.98  
% 2.72/0.98  fof(f54,plain,(
% 2.72/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.98    inference(cnf_transformation,[],[f27])).
% 2.72/0.98  
% 2.72/0.98  fof(f68,plain,(
% 2.72/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f11,axiom,(
% 2.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f29,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.98    inference(ennf_transformation,[],[f11])).
% 2.72/0.98  
% 2.72/0.98  fof(f56,plain,(
% 2.72/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.98    inference(cnf_transformation,[],[f29])).
% 2.72/0.98  
% 2.72/0.98  fof(f72,plain,(
% 2.72/0.98    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f5,axiom,(
% 2.72/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f22,plain,(
% 2.72/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.72/0.98    inference(ennf_transformation,[],[f5])).
% 2.72/0.98  
% 2.72/0.98  fof(f38,plain,(
% 2.72/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.72/0.98    inference(nnf_transformation,[],[f22])).
% 2.72/0.98  
% 2.72/0.98  fof(f50,plain,(
% 2.72/0.98    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f38])).
% 2.72/0.98  
% 2.72/0.98  fof(f4,axiom,(
% 2.72/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f21,plain,(
% 2.72/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.72/0.98    inference(ennf_transformation,[],[f4])).
% 2.72/0.98  
% 2.72/0.98  fof(f48,plain,(
% 2.72/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f21])).
% 2.72/0.98  
% 2.72/0.98  fof(f6,axiom,(
% 2.72/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f51,plain,(
% 2.72/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.72/0.98    inference(cnf_transformation,[],[f6])).
% 2.72/0.98  
% 2.72/0.98  fof(f10,axiom,(
% 2.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f28,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.98    inference(ennf_transformation,[],[f10])).
% 2.72/0.98  
% 2.72/0.98  fof(f55,plain,(
% 2.72/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.98    inference(cnf_transformation,[],[f28])).
% 2.72/0.98  
% 2.72/0.98  fof(f12,axiom,(
% 2.72/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f30,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.98    inference(ennf_transformation,[],[f12])).
% 2.72/0.98  
% 2.72/0.98  fof(f31,plain,(
% 2.72/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.98    inference(flattening,[],[f30])).
% 2.72/0.98  
% 2.72/0.98  fof(f39,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.72/0.98    inference(nnf_transformation,[],[f31])).
% 2.72/0.98  
% 2.72/0.98  fof(f57,plain,(
% 2.72/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.72/0.98    inference(cnf_transformation,[],[f39])).
% 2.72/0.98  
% 2.72/0.98  fof(f67,plain,(
% 2.72/0.98    v1_funct_2(sK3,sK1,sK2)),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f1,axiom,(
% 2.72/0.98    v1_xboole_0(k1_xboole_0)),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f45,plain,(
% 2.72/0.98    v1_xboole_0(k1_xboole_0)),
% 2.72/0.98    inference(cnf_transformation,[],[f1])).
% 2.72/0.98  
% 2.72/0.98  fof(f65,plain,(
% 2.72/0.98    ~v1_xboole_0(sK2)),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f8,axiom,(
% 2.72/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f25,plain,(
% 2.72/0.98    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.72/0.98    inference(ennf_transformation,[],[f8])).
% 2.72/0.98  
% 2.72/0.98  fof(f26,plain,(
% 2.72/0.98    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.72/0.98    inference(flattening,[],[f25])).
% 2.72/0.98  
% 2.72/0.98  fof(f53,plain,(
% 2.72/0.98    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f26])).
% 2.72/0.98  
% 2.72/0.98  fof(f7,axiom,(
% 2.72/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f23,plain,(
% 2.72/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.72/0.98    inference(ennf_transformation,[],[f7])).
% 2.72/0.98  
% 2.72/0.98  fof(f24,plain,(
% 2.72/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.72/0.98    inference(flattening,[],[f23])).
% 2.72/0.98  
% 2.72/0.98  fof(f52,plain,(
% 2.72/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f24])).
% 2.72/0.98  
% 2.72/0.98  fof(f13,axiom,(
% 2.72/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f32,plain,(
% 2.72/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.72/0.98    inference(ennf_transformation,[],[f13])).
% 2.72/0.98  
% 2.72/0.98  fof(f33,plain,(
% 2.72/0.98    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.72/0.98    inference(flattening,[],[f32])).
% 2.72/0.98  
% 2.72/0.98  fof(f63,plain,(
% 2.72/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f33])).
% 2.72/0.98  
% 2.72/0.98  fof(f66,plain,(
% 2.72/0.98    v1_funct_1(sK3)),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f69,plain,(
% 2.72/0.98    v1_funct_1(sK4)),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  fof(f14,axiom,(
% 2.72/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.72/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/0.98  
% 2.72/0.98  fof(f34,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.72/0.98    inference(ennf_transformation,[],[f14])).
% 2.72/0.98  
% 2.72/0.98  fof(f35,plain,(
% 2.72/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.72/0.98    inference(flattening,[],[f34])).
% 2.72/0.98  
% 2.72/0.98  fof(f64,plain,(
% 2.72/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.72/0.98    inference(cnf_transformation,[],[f35])).
% 2.72/0.98  
% 2.72/0.98  fof(f74,plain,(
% 2.72/0.98    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 2.72/0.98    inference(cnf_transformation,[],[f44])).
% 2.72/0.98  
% 2.72/0.98  cnf(c_23,negated_conjecture,
% 2.72/0.98      ( m1_subset_1(sK5,sK1) ),
% 2.72/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1779,plain,
% 2.72/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1,plain,
% 2.72/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.72/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.72/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_787,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,X1)
% 2.72/0.98      | r2_hidden(X0,X1)
% 2.72/0.98      | X1 != X2
% 2.72/0.98      | k1_xboole_0 = X2 ),
% 2.72/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_788,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1 ),
% 2.72/0.98      inference(unflattening,[status(thm)],[c_787]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1774,plain,
% 2.72/0.98      ( k1_xboole_0 = X0
% 2.72/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.72/0.98      | r2_hidden(X1,X0) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3665,plain,
% 2.72/0.98      ( sK1 = k1_xboole_0 | r2_hidden(sK5,sK1) = iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1779,c_1774]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_36,plain,
% 2.72/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_21,negated_conjecture,
% 2.72/0.98      ( k1_xboole_0 != sK1 ),
% 2.72/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2015,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,sK1) | r2_hidden(X0,sK1) | k1_xboole_0 = sK1 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_788]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2112,plain,
% 2.72/0.98      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | k1_xboole_0 = sK1 ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_2015]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2113,plain,
% 2.72/0.98      ( k1_xboole_0 = sK1
% 2.72/0.98      | m1_subset_1(sK5,sK1) != iProver_top
% 2.72/0.98      | r2_hidden(sK5,sK1) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2112]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3715,plain,
% 2.72/0.98      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_3665,c_36,c_21,c_2113]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_24,negated_conjecture,
% 2.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.72/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1778,plain,
% 2.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_9,plain,
% 2.72/0.98      ( v5_relat_1(X0,X1)
% 2.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.72/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1784,plain,
% 2.72/0.98      ( v5_relat_1(X0,X1) = iProver_top
% 2.72/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2197,plain,
% 2.72/0.98      ( v5_relat_1(sK4,sK0) = iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1778,c_1784]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_26,negated_conjecture,
% 2.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.72/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1776,plain,
% 2.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_11,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.72/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1782,plain,
% 2.72/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2293,plain,
% 2.72/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1776,c_1782]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_22,negated_conjecture,
% 2.72/0.98      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.72/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1780,plain,
% 2.72/0.98      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2409,plain,
% 2.72/0.98      ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.72/0.98      inference(demodulation,[status(thm)],[c_2293,c_1780]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_4,plain,
% 2.72/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.72/0.98      | v5_relat_1(X0,X1)
% 2.72/0.98      | ~ v1_relat_1(X0) ),
% 2.72/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1789,plain,
% 2.72/0.98      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.72/0.98      | v5_relat_1(X0,X1) = iProver_top
% 2.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2845,plain,
% 2.72/0.98      ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.72/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_2409,c_1789]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_33,plain,
% 2.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/0.98      | ~ v1_relat_1(X1)
% 2.72/0.98      | v1_relat_1(X0) ),
% 2.72/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1976,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.98      | v1_relat_1(X0)
% 2.72/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2130,plain,
% 2.72/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.72/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.72/0.98      | v1_relat_1(sK3) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1976]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2131,plain,
% 2.72/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.72/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.72/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_6,plain,
% 2.72/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.72/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2159,plain,
% 2.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2160,plain,
% 2.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2159]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3476,plain,
% 2.72/0.98      ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_2845,c_33,c_2131,c_2160]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_10,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.72/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1783,plain,
% 2.72/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.72/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2758,plain,
% 2.72/0.98      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1778,c_1783]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3480,plain,
% 2.72/0.98      ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
% 2.72/0.98      inference(light_normalisation,[status(thm)],[c_3476,c_2758]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2759,plain,
% 2.72/0.98      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1776,c_1783]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_17,plain,
% 2.72/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.72/0.98      | k1_xboole_0 = X2 ),
% 2.72/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_27,negated_conjecture,
% 2.72/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.72/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_749,plain,
% 2.72/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.72/0.98      | sK3 != X0
% 2.72/0.98      | sK2 != X2
% 2.72/0.98      | sK1 != X1
% 2.72/0.98      | k1_xboole_0 = X2 ),
% 2.72/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_750,plain,
% 2.72/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.72/0.98      | k1_relset_1(sK1,sK2,sK3) = sK1
% 2.72/0.98      | k1_xboole_0 = sK2 ),
% 2.72/0.98      inference(unflattening,[status(thm)],[c_749]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_752,plain,
% 2.72/0.98      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_750,c_26]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3110,plain,
% 2.72/0.98      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_2759,c_752]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_0,plain,
% 2.72/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.72/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_29,negated_conjecture,
% 2.72/0.98      ( ~ v1_xboole_0(sK2) ),
% 2.72/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_313,plain,
% 2.72/0.98      ( sK2 != k1_xboole_0 ),
% 2.72/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_29]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3311,plain,
% 2.72/0.98      ( k1_relat_1(sK3) = sK1 ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_3110,c_313]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_8,plain,
% 2.72/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.72/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.72/0.98      | ~ v1_funct_1(X1)
% 2.72/0.98      | ~ v1_relat_1(X1) ),
% 2.72/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1785,plain,
% 2.72/0.98      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 2.72/0.98      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top
% 2.72/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_7,plain,
% 2.72/0.98      ( ~ v5_relat_1(X0,X1)
% 2.72/0.98      | r2_hidden(X2,X1)
% 2.72/0.98      | ~ r2_hidden(X2,k2_relat_1(X0))
% 2.72/0.98      | ~ v1_relat_1(X0) ),
% 2.72/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1786,plain,
% 2.72/0.98      ( v5_relat_1(X0,X1) != iProver_top
% 2.72/0.98      | r2_hidden(X2,X1) = iProver_top
% 2.72/0.98      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 2.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3693,plain,
% 2.72/0.98      ( v5_relat_1(X0,X1) != iProver_top
% 2.72/0.98      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 2.72/0.98      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 2.72/0.98      | v1_funct_1(X0) != iProver_top
% 2.72/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1785,c_1786]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_18,plain,
% 2.72/0.98      ( ~ v5_relat_1(X0,X1)
% 2.72/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.72/0.98      | ~ v1_funct_1(X0)
% 2.72/0.98      | ~ v1_relat_1(X0)
% 2.72/0.98      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.72/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1781,plain,
% 2.72/0.98      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.72/0.98      | v5_relat_1(X1,X0) != iProver_top
% 2.72/0.98      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top
% 2.72/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_4200,plain,
% 2.72/0.98      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 2.72/0.98      | v5_relat_1(X1,X0) != iProver_top
% 2.72/0.98      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 2.72/0.98      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 2.72/0.98      | v1_funct_1(X2) != iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top
% 2.72/0.98      | v1_relat_1(X2) != iProver_top
% 2.72/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_3693,c_1781]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_4855,plain,
% 2.72/0.98      ( k7_partfun1(X0,X1,k1_funct_1(sK3,X2)) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.72/0.98      | v5_relat_1(X1,X0) != iProver_top
% 2.72/0.98      | v5_relat_1(sK3,k1_relat_1(X1)) != iProver_top
% 2.72/0.98      | r2_hidden(X2,sK1) != iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top
% 2.72/0.98      | v1_funct_1(sK3) != iProver_top
% 2.72/0.98      | v1_relat_1(X1) != iProver_top
% 2.72/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_3311,c_4200]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_28,negated_conjecture,
% 2.72/0.98      ( v1_funct_1(sK3) ),
% 2.72/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_31,plain,
% 2.72/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_5086,plain,
% 2.72/0.98      ( v1_relat_1(X1) != iProver_top
% 2.72/0.98      | k7_partfun1(X0,X1,k1_funct_1(sK3,X2)) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.72/0.98      | v5_relat_1(X1,X0) != iProver_top
% 2.72/0.98      | v5_relat_1(sK3,k1_relat_1(X1)) != iProver_top
% 2.72/0.98      | r2_hidden(X2,sK1) != iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_4855,c_31,c_33,c_2131,c_2160]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_5087,plain,
% 2.72/0.98      ( k7_partfun1(X0,X1,k1_funct_1(sK3,X2)) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.72/0.98      | v5_relat_1(X1,X0) != iProver_top
% 2.72/0.98      | v5_relat_1(sK3,k1_relat_1(X1)) != iProver_top
% 2.72/0.98      | r2_hidden(X2,sK1) != iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top
% 2.72/0.98      | v1_relat_1(X1) != iProver_top ),
% 2.72/0.98      inference(renaming,[status(thm)],[c_5086]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_5098,plain,
% 2.72/0.98      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.72/0.98      | v5_relat_1(sK4,X0) != iProver_top
% 2.72/0.98      | r2_hidden(X1,sK1) != iProver_top
% 2.72/0.98      | v1_funct_1(sK4) != iProver_top
% 2.72/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_3480,c_5087]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_25,negated_conjecture,
% 2.72/0.98      ( v1_funct_1(sK4) ),
% 2.72/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_34,plain,
% 2.72/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_35,plain,
% 2.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2127,plain,
% 2.72/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 2.72/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
% 2.72/0.98      | v1_relat_1(sK4) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_1976]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2128,plain,
% 2.72/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.72/0.98      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 2.72/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2127]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2156,plain,
% 2.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 2.72/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2157,plain,
% 2.72/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_2156]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_6111,plain,
% 2.72/0.98      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 2.72/0.98      | v5_relat_1(sK4,X0) != iProver_top
% 2.72/0.98      | r2_hidden(X1,sK1) != iProver_top ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_5098,c_34,c_35,c_2128,c_2157]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_6120,plain,
% 2.72/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.72/0.98      | r2_hidden(X0,sK1) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_2197,c_6111]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_6146,plain,
% 2.72/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_3715,c_6120]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_19,plain,
% 2.72/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.72/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.72/0.98      | ~ m1_subset_1(X5,X1)
% 2.72/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.72/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.72/0.98      | ~ v1_funct_1(X4)
% 2.72/0.98      | ~ v1_funct_1(X0)
% 2.72/0.98      | v1_xboole_0(X2)
% 2.72/0.98      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.72/0.98      | k1_xboole_0 = X1 ),
% 2.72/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_722,plain,
% 2.72/0.98      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 2.72/0.98      | ~ m1_subset_1(X5,X0)
% 2.72/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.72/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.72/0.98      | ~ v1_funct_1(X2)
% 2.72/0.98      | ~ v1_funct_1(X4)
% 2.72/0.98      | v1_xboole_0(X1)
% 2.72/0.98      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.72/0.98      | sK3 != X2
% 2.72/0.98      | sK2 != X1
% 2.72/0.98      | sK1 != X0
% 2.72/0.98      | k1_xboole_0 = X0 ),
% 2.72/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_723,plain,
% 2.72/0.98      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.72/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.72/0.98      | ~ m1_subset_1(X2,sK1)
% 2.72/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.72/0.98      | ~ v1_funct_1(X1)
% 2.72/0.98      | ~ v1_funct_1(sK3)
% 2.72/0.98      | v1_xboole_0(sK2)
% 2.72/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.72/0.98      | k1_xboole_0 = sK1 ),
% 2.72/0.98      inference(unflattening,[status(thm)],[c_722]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_727,plain,
% 2.72/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.72/0.98      | ~ v1_funct_1(X1)
% 2.72/0.98      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.72/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.72/0.98      | ~ m1_subset_1(X2,sK1) ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_723,c_29,c_28,c_26,c_21]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_728,plain,
% 2.72/0.98      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 2.72/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 2.72/0.98      | ~ m1_subset_1(X2,sK1)
% 2.72/0.98      | ~ v1_funct_1(X1)
% 2.72/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) ),
% 2.72/0.98      inference(renaming,[status(thm)],[c_727]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_1770,plain,
% 2.72/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.72/0.98      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
% 2.72/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.72/0.98      | m1_subset_1(X2,sK1) != iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.98      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2634,plain,
% 2.72/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.72/0.98      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
% 2.72/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.72/0.98      | m1_subset_1(X2,sK1) != iProver_top
% 2.72/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.72/0.98      inference(light_normalisation,[status(thm)],[c_1770,c_2293]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_2643,plain,
% 2.72/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.72/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 2.72/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.72/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_2409,c_2634]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3919,plain,
% 2.72/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.72/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.72/0.98      inference(global_propositional_subsumption,
% 2.72/0.98                [status(thm)],
% 2.72/0.98                [c_2643,c_34,c_35]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3927,plain,
% 2.72/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.72/0.98      inference(superposition,[status(thm)],[c_1779,c_3919]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_20,negated_conjecture,
% 2.72/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
% 2.72/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(c_3929,plain,
% 2.72/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.72/0.98      inference(demodulation,[status(thm)],[c_3927,c_20]) ).
% 2.72/0.98  
% 2.72/0.98  cnf(contradiction,plain,
% 2.72/0.98      ( $false ),
% 2.72/0.98      inference(minisat,[status(thm)],[c_6146,c_3929]) ).
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/0.98  
% 2.72/0.98  ------                               Statistics
% 2.72/0.98  
% 2.72/0.98  ------ General
% 2.72/0.98  
% 2.72/0.98  abstr_ref_over_cycles:                  0
% 2.72/0.98  abstr_ref_under_cycles:                 0
% 2.72/0.98  gc_basic_clause_elim:                   0
% 2.72/0.98  forced_gc_time:                         0
% 2.72/0.98  parsing_time:                           0.013
% 2.72/0.98  unif_index_cands_time:                  0.
% 2.72/0.98  unif_index_add_time:                    0.
% 2.72/0.98  orderings_time:                         0.
% 2.72/0.98  out_proof_time:                         0.011
% 2.72/0.98  total_time:                             0.268
% 2.72/0.98  num_of_symbols:                         55
% 2.72/0.98  num_of_terms:                           11000
% 2.72/0.98  
% 2.72/0.98  ------ Preprocessing
% 2.72/0.98  
% 2.72/0.98  num_of_splits:                          0
% 2.72/0.98  num_of_split_atoms:                     0
% 2.72/0.98  num_of_reused_defs:                     0
% 2.72/0.98  num_eq_ax_congr_red:                    12
% 2.72/0.98  num_of_sem_filtered_clauses:            1
% 2.72/0.98  num_of_subtypes:                        0
% 2.72/0.98  monotx_restored_types:                  0
% 2.72/0.98  sat_num_of_epr_types:                   0
% 2.72/0.98  sat_num_of_non_cyclic_types:            0
% 2.72/0.98  sat_guarded_non_collapsed_types:        0
% 2.72/0.98  num_pure_diseq_elim:                    0
% 2.72/0.98  simp_replaced_by:                       0
% 2.72/0.98  res_preprocessed:                       134
% 2.72/0.98  prep_upred:                             0
% 2.72/0.98  prep_unflattend:                        52
% 2.72/0.98  smt_new_axioms:                         0
% 2.72/0.98  pred_elim_cands:                        6
% 2.72/0.98  pred_elim:                              2
% 2.72/0.98  pred_elim_cl:                           5
% 2.72/0.98  pred_elim_cycles:                       8
% 2.72/0.98  merged_defs:                            0
% 2.72/0.98  merged_defs_ncl:                        0
% 2.72/0.98  bin_hyper_res:                          0
% 2.72/0.98  prep_cycles:                            4
% 2.72/0.98  pred_elim_time:                         0.025
% 2.72/0.98  splitting_time:                         0.
% 2.72/0.98  sem_filter_time:                        0.
% 2.72/0.98  monotx_time:                            0.001
% 2.72/0.98  subtype_inf_time:                       0.
% 2.72/0.98  
% 2.72/0.98  ------ Problem properties
% 2.72/0.98  
% 2.72/0.98  clauses:                                25
% 2.72/0.98  conjectures:                            8
% 2.72/0.98  epr:                                    7
% 2.72/0.98  horn:                                   22
% 2.72/0.98  ground:                                 11
% 2.72/0.98  unary:                                  10
% 2.72/0.98  binary:                                 5
% 2.72/0.98  lits:                                   63
% 2.72/0.98  lits_eq:                                16
% 2.72/0.98  fd_pure:                                0
% 2.72/0.98  fd_pseudo:                              0
% 2.72/0.98  fd_cond:                                2
% 2.72/0.98  fd_pseudo_cond:                         0
% 2.72/0.98  ac_symbols:                             0
% 2.72/0.98  
% 2.72/0.98  ------ Propositional Solver
% 2.72/0.98  
% 2.72/0.98  prop_solver_calls:                      28
% 2.72/0.98  prop_fast_solver_calls:                 1224
% 2.72/0.98  smt_solver_calls:                       0
% 2.72/0.98  smt_fast_solver_calls:                  0
% 2.72/0.98  prop_num_of_clauses:                    2180
% 2.72/0.98  prop_preprocess_simplified:             6613
% 2.72/0.98  prop_fo_subsumed:                       40
% 2.72/0.98  prop_solver_time:                       0.
% 2.72/0.98  smt_solver_time:                        0.
% 2.72/0.98  smt_fast_solver_time:                   0.
% 2.72/0.98  prop_fast_solver_time:                  0.
% 2.72/0.98  prop_unsat_core_time:                   0.
% 2.72/0.98  
% 2.72/0.98  ------ QBF
% 2.72/0.98  
% 2.72/0.98  qbf_q_res:                              0
% 2.72/0.98  qbf_num_tautologies:                    0
% 2.72/0.98  qbf_prep_cycles:                        0
% 2.72/0.98  
% 2.72/0.98  ------ BMC1
% 2.72/0.98  
% 2.72/0.98  bmc1_current_bound:                     -1
% 2.72/0.98  bmc1_last_solved_bound:                 -1
% 2.72/0.98  bmc1_unsat_core_size:                   -1
% 2.72/0.98  bmc1_unsat_core_parents_size:           -1
% 2.72/0.98  bmc1_merge_next_fun:                    0
% 2.72/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.72/0.98  
% 2.72/0.98  ------ Instantiation
% 2.72/0.98  
% 2.72/0.98  inst_num_of_clauses:                    687
% 2.72/0.98  inst_num_in_passive:                    340
% 2.72/0.98  inst_num_in_active:                     345
% 2.72/0.98  inst_num_in_unprocessed:                2
% 2.72/0.98  inst_num_of_loops:                      360
% 2.72/0.98  inst_num_of_learning_restarts:          0
% 2.72/0.98  inst_num_moves_active_passive:          12
% 2.72/0.98  inst_lit_activity:                      0
% 2.72/0.98  inst_lit_activity_moves:                0
% 2.72/0.98  inst_num_tautologies:                   0
% 2.72/0.98  inst_num_prop_implied:                  0
% 2.72/0.98  inst_num_existing_simplified:           0
% 2.72/0.98  inst_num_eq_res_simplified:             0
% 2.72/0.98  inst_num_child_elim:                    0
% 2.72/0.98  inst_num_of_dismatching_blockings:      97
% 2.72/0.98  inst_num_of_non_proper_insts:           439
% 2.72/0.98  inst_num_of_duplicates:                 0
% 2.72/0.98  inst_inst_num_from_inst_to_res:         0
% 2.72/0.98  inst_dismatching_checking_time:         0.
% 2.72/0.98  
% 2.72/0.98  ------ Resolution
% 2.72/0.98  
% 2.72/0.98  res_num_of_clauses:                     0
% 2.72/0.98  res_num_in_passive:                     0
% 2.72/0.98  res_num_in_active:                      0
% 2.72/0.98  res_num_of_loops:                       138
% 2.72/0.98  res_forward_subset_subsumed:            59
% 2.72/0.98  res_backward_subset_subsumed:           0
% 2.72/0.98  res_forward_subsumed:                   0
% 2.72/0.98  res_backward_subsumed:                  0
% 2.72/0.98  res_forward_subsumption_resolution:     1
% 2.72/0.98  res_backward_subsumption_resolution:    0
% 2.72/0.98  res_clause_to_clause_subsumption:       376
% 2.72/0.98  res_orphan_elimination:                 0
% 2.72/0.98  res_tautology_del:                      47
% 2.72/0.98  res_num_eq_res_simplified:              0
% 2.72/0.98  res_num_sel_changes:                    0
% 2.72/0.98  res_moves_from_active_to_pass:          0
% 2.72/0.98  
% 2.72/0.98  ------ Superposition
% 2.72/0.98  
% 2.72/0.98  sup_time_total:                         0.
% 2.72/0.98  sup_time_generating:                    0.
% 2.72/0.98  sup_time_sim_full:                      0.
% 2.72/0.98  sup_time_sim_immed:                     0.
% 2.72/0.98  
% 2.72/0.98  sup_num_of_clauses:                     74
% 2.72/0.98  sup_num_in_active:                      66
% 2.72/0.98  sup_num_in_passive:                     8
% 2.72/0.98  sup_num_of_loops:                       70
% 2.72/0.98  sup_fw_superposition:                   50
% 2.72/0.98  sup_bw_superposition:                   13
% 2.72/0.98  sup_immediate_simplified:               5
% 2.72/0.98  sup_given_eliminated:                   0
% 2.72/0.98  comparisons_done:                       0
% 2.72/0.98  comparisons_avoided:                    0
% 2.72/0.98  
% 2.72/0.98  ------ Simplifications
% 2.72/0.98  
% 2.72/0.98  
% 2.72/0.98  sim_fw_subset_subsumed:                 0
% 2.72/0.98  sim_bw_subset_subsumed:                 2
% 2.72/0.98  sim_fw_subsumed:                        3
% 2.72/0.98  sim_bw_subsumed:                        0
% 2.72/0.98  sim_fw_subsumption_res:                 1
% 2.72/0.98  sim_bw_subsumption_res:                 0
% 2.72/0.98  sim_tautology_del:                      1
% 2.72/0.98  sim_eq_tautology_del:                   0
% 2.72/0.98  sim_eq_res_simp:                        0
% 2.72/0.98  sim_fw_demodulated:                     0
% 2.72/0.98  sim_bw_demodulated:                     4
% 2.72/0.98  sim_light_normalised:                   5
% 2.72/0.98  sim_joinable_taut:                      0
% 2.72/0.98  sim_joinable_simp:                      0
% 2.72/0.98  sim_ac_normalised:                      0
% 2.72/0.98  sim_smt_subsumption:                    0
% 2.72/0.98  
%------------------------------------------------------------------------------
