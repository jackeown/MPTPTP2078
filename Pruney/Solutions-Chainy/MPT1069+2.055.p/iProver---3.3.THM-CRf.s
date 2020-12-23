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
% DateTime   : Thu Dec  3 12:09:53 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 434 expanded)
%              Number of clauses        :   84 ( 118 expanded)
%              Number of leaves         :   21 ( 146 expanded)
%              Depth                    :   18
%              Number of atoms          :  542 (3225 expanded)
%              Number of equality atoms :  206 ( 849 expanded)
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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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
                  ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK3
                  & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4))
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f35,f47,f46,f45,f44])).

fof(f76,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f40])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
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

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f43,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f69,plain,(
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

fof(f79,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2149,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2160,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3452,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_2160])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2368,plain,
    ( r2_hidden(sK1(sK3),sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2369,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK1(sK3),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2490,plain,
    ( ~ r2_hidden(sK1(sK3),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2491,plain,
    ( r2_hidden(sK1(sK3),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2490])).

cnf(c_3841,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3452,c_22,c_2369,c_2491])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2148,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2154,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2975,plain,
    ( v5_relat_1(sK6,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2148,c_2154])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2146,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2152,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3033,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2146,c_2152])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2150,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3153,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3033,c_2150])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2153,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3041,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2148,c_2153])).

cnf(c_3330,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3153,c_3041])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2158,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v5_relat_1(X0,X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3609,plain,
    ( v5_relat_1(sK5,k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3330,c_2158])).

cnf(c_34,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2783,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_2784,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2783])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2813,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2814,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2813])).

cnf(c_4082,plain,
    ( v5_relat_1(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3609,c_34,c_2784,c_2814])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2155,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2151,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4035,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_2151])).

cnf(c_6250,plain,
    ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
    | v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4082,c_4035])).

cnf(c_3042,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2146,c_2153])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_792,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_791])).

cnf(c_794,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_792,c_27])).

cnf(c_3223,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3042,c_794])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_503,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_30])).

cnf(c_3333,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3223,c_503])).

cnf(c_6275,plain,
    ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
    | v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6250,c_3333])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2780,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_2781,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2780])).

cnf(c_2810,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2811,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2810])).

cnf(c_6890,plain,
    ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
    | v5_relat_1(sK6,X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6275,c_32,c_34,c_35,c_36,c_2781,c_2784,c_2811,c_2814])).

cnf(c_6899,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2975,c_6890])).

cnf(c_6958,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3841,c_6899])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_764,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X5,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
    | sK5 != X2
    | sK4 != X1
    | sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_765,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
    | ~ m1_subset_1(X2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4)
    | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_764])).

cnf(c_769,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
    | ~ m1_subset_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_765,c_30,c_29,c_27,c_22])).

cnf(c_770,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
    | ~ m1_subset_1(X2,sK3)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2)) ),
    inference(renaming,[status(thm)],[c_769])).

cnf(c_2141,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_2690,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2150,c_2141])).

cnf(c_2769,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_35,c_36])).

cnf(c_2777,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2149,c_2769])).

cnf(c_21,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2779,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_2777,c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6958,c_2779])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.92/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.92/1.00  
% 2.92/1.00  ------  iProver source info
% 2.92/1.00  
% 2.92/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.92/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.92/1.00  git: non_committed_changes: false
% 2.92/1.00  git: last_make_outside_of_git: false
% 2.92/1.00  
% 2.92/1.00  ------ 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options
% 2.92/1.00  
% 2.92/1.00  --out_options                           all
% 2.92/1.00  --tptp_safe_out                         true
% 2.92/1.00  --problem_path                          ""
% 2.92/1.00  --include_path                          ""
% 2.92/1.00  --clausifier                            res/vclausify_rel
% 2.92/1.00  --clausifier_options                    --mode clausify
% 2.92/1.00  --stdin                                 false
% 2.92/1.00  --stats_out                             all
% 2.92/1.00  
% 2.92/1.00  ------ General Options
% 2.92/1.00  
% 2.92/1.00  --fof                                   false
% 2.92/1.00  --time_out_real                         305.
% 2.92/1.00  --time_out_virtual                      -1.
% 2.92/1.00  --symbol_type_check                     false
% 2.92/1.00  --clausify_out                          false
% 2.92/1.00  --sig_cnt_out                           false
% 2.92/1.00  --trig_cnt_out                          false
% 2.92/1.00  --trig_cnt_out_tolerance                1.
% 2.92/1.00  --trig_cnt_out_sk_spl                   false
% 2.92/1.00  --abstr_cl_out                          false
% 2.92/1.00  
% 2.92/1.00  ------ Global Options
% 2.92/1.00  
% 2.92/1.00  --schedule                              default
% 2.92/1.00  --add_important_lit                     false
% 2.92/1.00  --prop_solver_per_cl                    1000
% 2.92/1.00  --min_unsat_core                        false
% 2.92/1.00  --soft_assumptions                      false
% 2.92/1.00  --soft_lemma_size                       3
% 2.92/1.00  --prop_impl_unit_size                   0
% 2.92/1.00  --prop_impl_unit                        []
% 2.92/1.00  --share_sel_clauses                     true
% 2.92/1.00  --reset_solvers                         false
% 2.92/1.00  --bc_imp_inh                            [conj_cone]
% 2.92/1.00  --conj_cone_tolerance                   3.
% 2.92/1.00  --extra_neg_conj                        none
% 2.92/1.00  --large_theory_mode                     true
% 2.92/1.00  --prolific_symb_bound                   200
% 2.92/1.00  --lt_threshold                          2000
% 2.92/1.00  --clause_weak_htbl                      true
% 2.92/1.00  --gc_record_bc_elim                     false
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing Options
% 2.92/1.00  
% 2.92/1.00  --preprocessing_flag                    true
% 2.92/1.00  --time_out_prep_mult                    0.1
% 2.92/1.00  --splitting_mode                        input
% 2.92/1.00  --splitting_grd                         true
% 2.92/1.00  --splitting_cvd                         false
% 2.92/1.00  --splitting_cvd_svl                     false
% 2.92/1.00  --splitting_nvd                         32
% 2.92/1.00  --sub_typing                            true
% 2.92/1.00  --prep_gs_sim                           true
% 2.92/1.00  --prep_unflatten                        true
% 2.92/1.00  --prep_res_sim                          true
% 2.92/1.00  --prep_upred                            true
% 2.92/1.00  --prep_sem_filter                       exhaustive
% 2.92/1.00  --prep_sem_filter_out                   false
% 2.92/1.00  --pred_elim                             true
% 2.92/1.00  --res_sim_input                         true
% 2.92/1.00  --eq_ax_congr_red                       true
% 2.92/1.00  --pure_diseq_elim                       true
% 2.92/1.00  --brand_transform                       false
% 2.92/1.00  --non_eq_to_eq                          false
% 2.92/1.00  --prep_def_merge                        true
% 2.92/1.00  --prep_def_merge_prop_impl              false
% 2.92/1.00  --prep_def_merge_mbd                    true
% 2.92/1.00  --prep_def_merge_tr_red                 false
% 2.92/1.00  --prep_def_merge_tr_cl                  false
% 2.92/1.00  --smt_preprocessing                     true
% 2.92/1.00  --smt_ac_axioms                         fast
% 2.92/1.00  --preprocessed_out                      false
% 2.92/1.00  --preprocessed_stats                    false
% 2.92/1.00  
% 2.92/1.00  ------ Abstraction refinement Options
% 2.92/1.00  
% 2.92/1.00  --abstr_ref                             []
% 2.92/1.00  --abstr_ref_prep                        false
% 2.92/1.00  --abstr_ref_until_sat                   false
% 2.92/1.00  --abstr_ref_sig_restrict                funpre
% 2.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/1.00  --abstr_ref_under                       []
% 2.92/1.00  
% 2.92/1.00  ------ SAT Options
% 2.92/1.00  
% 2.92/1.00  --sat_mode                              false
% 2.92/1.00  --sat_fm_restart_options                ""
% 2.92/1.00  --sat_gr_def                            false
% 2.92/1.00  --sat_epr_types                         true
% 2.92/1.00  --sat_non_cyclic_types                  false
% 2.92/1.00  --sat_finite_models                     false
% 2.92/1.00  --sat_fm_lemmas                         false
% 2.92/1.00  --sat_fm_prep                           false
% 2.92/1.00  --sat_fm_uc_incr                        true
% 2.92/1.00  --sat_out_model                         small
% 2.92/1.00  --sat_out_clauses                       false
% 2.92/1.00  
% 2.92/1.00  ------ QBF Options
% 2.92/1.00  
% 2.92/1.00  --qbf_mode                              false
% 2.92/1.00  --qbf_elim_univ                         false
% 2.92/1.00  --qbf_dom_inst                          none
% 2.92/1.00  --qbf_dom_pre_inst                      false
% 2.92/1.00  --qbf_sk_in                             false
% 2.92/1.00  --qbf_pred_elim                         true
% 2.92/1.00  --qbf_split                             512
% 2.92/1.00  
% 2.92/1.00  ------ BMC1 Options
% 2.92/1.00  
% 2.92/1.00  --bmc1_incremental                      false
% 2.92/1.00  --bmc1_axioms                           reachable_all
% 2.92/1.00  --bmc1_min_bound                        0
% 2.92/1.00  --bmc1_max_bound                        -1
% 2.92/1.00  --bmc1_max_bound_default                -1
% 2.92/1.00  --bmc1_symbol_reachability              true
% 2.92/1.00  --bmc1_property_lemmas                  false
% 2.92/1.00  --bmc1_k_induction                      false
% 2.92/1.00  --bmc1_non_equiv_states                 false
% 2.92/1.00  --bmc1_deadlock                         false
% 2.92/1.00  --bmc1_ucm                              false
% 2.92/1.00  --bmc1_add_unsat_core                   none
% 2.92/1.00  --bmc1_unsat_core_children              false
% 2.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/1.00  --bmc1_out_stat                         full
% 2.92/1.00  --bmc1_ground_init                      false
% 2.92/1.00  --bmc1_pre_inst_next_state              false
% 2.92/1.00  --bmc1_pre_inst_state                   false
% 2.92/1.00  --bmc1_pre_inst_reach_state             false
% 2.92/1.00  --bmc1_out_unsat_core                   false
% 2.92/1.00  --bmc1_aig_witness_out                  false
% 2.92/1.00  --bmc1_verbose                          false
% 2.92/1.00  --bmc1_dump_clauses_tptp                false
% 2.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.92/1.00  --bmc1_dump_file                        -
% 2.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.92/1.00  --bmc1_ucm_extend_mode                  1
% 2.92/1.00  --bmc1_ucm_init_mode                    2
% 2.92/1.00  --bmc1_ucm_cone_mode                    none
% 2.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.92/1.00  --bmc1_ucm_relax_model                  4
% 2.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/1.00  --bmc1_ucm_layered_model                none
% 2.92/1.00  --bmc1_ucm_max_lemma_size               10
% 2.92/1.00  
% 2.92/1.00  ------ AIG Options
% 2.92/1.00  
% 2.92/1.00  --aig_mode                              false
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation Options
% 2.92/1.00  
% 2.92/1.00  --instantiation_flag                    true
% 2.92/1.00  --inst_sos_flag                         false
% 2.92/1.00  --inst_sos_phase                        true
% 2.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel_side                     num_symb
% 2.92/1.00  --inst_solver_per_active                1400
% 2.92/1.00  --inst_solver_calls_frac                1.
% 2.92/1.00  --inst_passive_queue_type               priority_queues
% 2.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/1.00  --inst_passive_queues_freq              [25;2]
% 2.92/1.00  --inst_dismatching                      true
% 2.92/1.00  --inst_eager_unprocessed_to_passive     true
% 2.92/1.00  --inst_prop_sim_given                   true
% 2.92/1.00  --inst_prop_sim_new                     false
% 2.92/1.00  --inst_subs_new                         false
% 2.92/1.00  --inst_eq_res_simp                      false
% 2.92/1.00  --inst_subs_given                       false
% 2.92/1.00  --inst_orphan_elimination               true
% 2.92/1.00  --inst_learning_loop_flag               true
% 2.92/1.00  --inst_learning_start                   3000
% 2.92/1.00  --inst_learning_factor                  2
% 2.92/1.00  --inst_start_prop_sim_after_learn       3
% 2.92/1.00  --inst_sel_renew                        solver
% 2.92/1.00  --inst_lit_activity_flag                true
% 2.92/1.00  --inst_restr_to_given                   false
% 2.92/1.00  --inst_activity_threshold               500
% 2.92/1.00  --inst_out_proof                        true
% 2.92/1.00  
% 2.92/1.00  ------ Resolution Options
% 2.92/1.00  
% 2.92/1.00  --resolution_flag                       true
% 2.92/1.00  --res_lit_sel                           adaptive
% 2.92/1.00  --res_lit_sel_side                      none
% 2.92/1.00  --res_ordering                          kbo
% 2.92/1.00  --res_to_prop_solver                    active
% 2.92/1.00  --res_prop_simpl_new                    false
% 2.92/1.00  --res_prop_simpl_given                  true
% 2.92/1.00  --res_passive_queue_type                priority_queues
% 2.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/1.00  --res_passive_queues_freq               [15;5]
% 2.92/1.00  --res_forward_subs                      full
% 2.92/1.00  --res_backward_subs                     full
% 2.92/1.00  --res_forward_subs_resolution           true
% 2.92/1.00  --res_backward_subs_resolution          true
% 2.92/1.00  --res_orphan_elimination                true
% 2.92/1.00  --res_time_limit                        2.
% 2.92/1.00  --res_out_proof                         true
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Options
% 2.92/1.00  
% 2.92/1.00  --superposition_flag                    true
% 2.92/1.00  --sup_passive_queue_type                priority_queues
% 2.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.92/1.00  --demod_completeness_check              fast
% 2.92/1.00  --demod_use_ground                      true
% 2.92/1.00  --sup_to_prop_solver                    passive
% 2.92/1.00  --sup_prop_simpl_new                    true
% 2.92/1.00  --sup_prop_simpl_given                  true
% 2.92/1.00  --sup_fun_splitting                     false
% 2.92/1.00  --sup_smt_interval                      50000
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Simplification Setup
% 2.92/1.00  
% 2.92/1.00  --sup_indices_passive                   []
% 2.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_full_bw                           [BwDemod]
% 2.92/1.00  --sup_immed_triv                        [TrivRules]
% 2.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_immed_bw_main                     []
% 2.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  
% 2.92/1.00  ------ Combination Options
% 2.92/1.00  
% 2.92/1.00  --comb_res_mult                         3
% 2.92/1.00  --comb_sup_mult                         2
% 2.92/1.00  --comb_inst_mult                        10
% 2.92/1.00  
% 2.92/1.00  ------ Debug Options
% 2.92/1.00  
% 2.92/1.00  --dbg_backtrace                         false
% 2.92/1.00  --dbg_dump_prop_clauses                 false
% 2.92/1.00  --dbg_dump_prop_clauses_file            -
% 2.92/1.00  --dbg_out_stat                          false
% 2.92/1.00  ------ Parsing...
% 2.92/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.92/1.00  ------ Proving...
% 2.92/1.00  ------ Problem Properties 
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  clauses                                 28
% 2.92/1.00  conjectures                             9
% 2.92/1.00  EPR                                     9
% 2.92/1.00  Horn                                    23
% 2.92/1.00  unary                                   12
% 2.92/1.00  binary                                  7
% 2.92/1.00  lits                                    67
% 2.92/1.00  lits eq                                 16
% 2.92/1.00  fd_pure                                 0
% 2.92/1.00  fd_pseudo                               0
% 2.92/1.00  fd_cond                                 2
% 2.92/1.00  fd_pseudo_cond                          0
% 2.92/1.00  AC symbols                              0
% 2.92/1.00  
% 2.92/1.00  ------ Schedule dynamic 5 is on 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ 
% 2.92/1.00  Current options:
% 2.92/1.00  ------ 
% 2.92/1.00  
% 2.92/1.00  ------ Input Options
% 2.92/1.00  
% 2.92/1.00  --out_options                           all
% 2.92/1.00  --tptp_safe_out                         true
% 2.92/1.00  --problem_path                          ""
% 2.92/1.00  --include_path                          ""
% 2.92/1.00  --clausifier                            res/vclausify_rel
% 2.92/1.00  --clausifier_options                    --mode clausify
% 2.92/1.00  --stdin                                 false
% 2.92/1.00  --stats_out                             all
% 2.92/1.00  
% 2.92/1.00  ------ General Options
% 2.92/1.00  
% 2.92/1.00  --fof                                   false
% 2.92/1.00  --time_out_real                         305.
% 2.92/1.00  --time_out_virtual                      -1.
% 2.92/1.00  --symbol_type_check                     false
% 2.92/1.00  --clausify_out                          false
% 2.92/1.00  --sig_cnt_out                           false
% 2.92/1.00  --trig_cnt_out                          false
% 2.92/1.00  --trig_cnt_out_tolerance                1.
% 2.92/1.00  --trig_cnt_out_sk_spl                   false
% 2.92/1.00  --abstr_cl_out                          false
% 2.92/1.00  
% 2.92/1.00  ------ Global Options
% 2.92/1.00  
% 2.92/1.00  --schedule                              default
% 2.92/1.00  --add_important_lit                     false
% 2.92/1.00  --prop_solver_per_cl                    1000
% 2.92/1.00  --min_unsat_core                        false
% 2.92/1.00  --soft_assumptions                      false
% 2.92/1.00  --soft_lemma_size                       3
% 2.92/1.00  --prop_impl_unit_size                   0
% 2.92/1.00  --prop_impl_unit                        []
% 2.92/1.00  --share_sel_clauses                     true
% 2.92/1.00  --reset_solvers                         false
% 2.92/1.00  --bc_imp_inh                            [conj_cone]
% 2.92/1.00  --conj_cone_tolerance                   3.
% 2.92/1.00  --extra_neg_conj                        none
% 2.92/1.00  --large_theory_mode                     true
% 2.92/1.00  --prolific_symb_bound                   200
% 2.92/1.00  --lt_threshold                          2000
% 2.92/1.00  --clause_weak_htbl                      true
% 2.92/1.00  --gc_record_bc_elim                     false
% 2.92/1.00  
% 2.92/1.00  ------ Preprocessing Options
% 2.92/1.00  
% 2.92/1.00  --preprocessing_flag                    true
% 2.92/1.00  --time_out_prep_mult                    0.1
% 2.92/1.00  --splitting_mode                        input
% 2.92/1.00  --splitting_grd                         true
% 2.92/1.00  --splitting_cvd                         false
% 2.92/1.00  --splitting_cvd_svl                     false
% 2.92/1.00  --splitting_nvd                         32
% 2.92/1.00  --sub_typing                            true
% 2.92/1.00  --prep_gs_sim                           true
% 2.92/1.00  --prep_unflatten                        true
% 2.92/1.00  --prep_res_sim                          true
% 2.92/1.00  --prep_upred                            true
% 2.92/1.00  --prep_sem_filter                       exhaustive
% 2.92/1.00  --prep_sem_filter_out                   false
% 2.92/1.00  --pred_elim                             true
% 2.92/1.00  --res_sim_input                         true
% 2.92/1.00  --eq_ax_congr_red                       true
% 2.92/1.00  --pure_diseq_elim                       true
% 2.92/1.00  --brand_transform                       false
% 2.92/1.00  --non_eq_to_eq                          false
% 2.92/1.00  --prep_def_merge                        true
% 2.92/1.00  --prep_def_merge_prop_impl              false
% 2.92/1.00  --prep_def_merge_mbd                    true
% 2.92/1.00  --prep_def_merge_tr_red                 false
% 2.92/1.00  --prep_def_merge_tr_cl                  false
% 2.92/1.00  --smt_preprocessing                     true
% 2.92/1.00  --smt_ac_axioms                         fast
% 2.92/1.00  --preprocessed_out                      false
% 2.92/1.00  --preprocessed_stats                    false
% 2.92/1.00  
% 2.92/1.00  ------ Abstraction refinement Options
% 2.92/1.00  
% 2.92/1.00  --abstr_ref                             []
% 2.92/1.00  --abstr_ref_prep                        false
% 2.92/1.00  --abstr_ref_until_sat                   false
% 2.92/1.00  --abstr_ref_sig_restrict                funpre
% 2.92/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.92/1.00  --abstr_ref_under                       []
% 2.92/1.00  
% 2.92/1.00  ------ SAT Options
% 2.92/1.00  
% 2.92/1.00  --sat_mode                              false
% 2.92/1.00  --sat_fm_restart_options                ""
% 2.92/1.00  --sat_gr_def                            false
% 2.92/1.00  --sat_epr_types                         true
% 2.92/1.00  --sat_non_cyclic_types                  false
% 2.92/1.00  --sat_finite_models                     false
% 2.92/1.00  --sat_fm_lemmas                         false
% 2.92/1.00  --sat_fm_prep                           false
% 2.92/1.00  --sat_fm_uc_incr                        true
% 2.92/1.00  --sat_out_model                         small
% 2.92/1.00  --sat_out_clauses                       false
% 2.92/1.00  
% 2.92/1.00  ------ QBF Options
% 2.92/1.00  
% 2.92/1.00  --qbf_mode                              false
% 2.92/1.00  --qbf_elim_univ                         false
% 2.92/1.00  --qbf_dom_inst                          none
% 2.92/1.00  --qbf_dom_pre_inst                      false
% 2.92/1.00  --qbf_sk_in                             false
% 2.92/1.00  --qbf_pred_elim                         true
% 2.92/1.00  --qbf_split                             512
% 2.92/1.00  
% 2.92/1.00  ------ BMC1 Options
% 2.92/1.00  
% 2.92/1.00  --bmc1_incremental                      false
% 2.92/1.00  --bmc1_axioms                           reachable_all
% 2.92/1.00  --bmc1_min_bound                        0
% 2.92/1.00  --bmc1_max_bound                        -1
% 2.92/1.00  --bmc1_max_bound_default                -1
% 2.92/1.00  --bmc1_symbol_reachability              true
% 2.92/1.00  --bmc1_property_lemmas                  false
% 2.92/1.00  --bmc1_k_induction                      false
% 2.92/1.00  --bmc1_non_equiv_states                 false
% 2.92/1.00  --bmc1_deadlock                         false
% 2.92/1.00  --bmc1_ucm                              false
% 2.92/1.00  --bmc1_add_unsat_core                   none
% 2.92/1.00  --bmc1_unsat_core_children              false
% 2.92/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.92/1.00  --bmc1_out_stat                         full
% 2.92/1.00  --bmc1_ground_init                      false
% 2.92/1.00  --bmc1_pre_inst_next_state              false
% 2.92/1.00  --bmc1_pre_inst_state                   false
% 2.92/1.00  --bmc1_pre_inst_reach_state             false
% 2.92/1.00  --bmc1_out_unsat_core                   false
% 2.92/1.00  --bmc1_aig_witness_out                  false
% 2.92/1.00  --bmc1_verbose                          false
% 2.92/1.00  --bmc1_dump_clauses_tptp                false
% 2.92/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.92/1.00  --bmc1_dump_file                        -
% 2.92/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.92/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.92/1.00  --bmc1_ucm_extend_mode                  1
% 2.92/1.00  --bmc1_ucm_init_mode                    2
% 2.92/1.00  --bmc1_ucm_cone_mode                    none
% 2.92/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.92/1.00  --bmc1_ucm_relax_model                  4
% 2.92/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.92/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.92/1.00  --bmc1_ucm_layered_model                none
% 2.92/1.00  --bmc1_ucm_max_lemma_size               10
% 2.92/1.00  
% 2.92/1.00  ------ AIG Options
% 2.92/1.00  
% 2.92/1.00  --aig_mode                              false
% 2.92/1.00  
% 2.92/1.00  ------ Instantiation Options
% 2.92/1.00  
% 2.92/1.00  --instantiation_flag                    true
% 2.92/1.00  --inst_sos_flag                         false
% 2.92/1.00  --inst_sos_phase                        true
% 2.92/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.92/1.00  --inst_lit_sel_side                     none
% 2.92/1.00  --inst_solver_per_active                1400
% 2.92/1.00  --inst_solver_calls_frac                1.
% 2.92/1.00  --inst_passive_queue_type               priority_queues
% 2.92/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.92/1.00  --inst_passive_queues_freq              [25;2]
% 2.92/1.00  --inst_dismatching                      true
% 2.92/1.00  --inst_eager_unprocessed_to_passive     true
% 2.92/1.00  --inst_prop_sim_given                   true
% 2.92/1.00  --inst_prop_sim_new                     false
% 2.92/1.00  --inst_subs_new                         false
% 2.92/1.00  --inst_eq_res_simp                      false
% 2.92/1.00  --inst_subs_given                       false
% 2.92/1.00  --inst_orphan_elimination               true
% 2.92/1.00  --inst_learning_loop_flag               true
% 2.92/1.00  --inst_learning_start                   3000
% 2.92/1.00  --inst_learning_factor                  2
% 2.92/1.00  --inst_start_prop_sim_after_learn       3
% 2.92/1.00  --inst_sel_renew                        solver
% 2.92/1.00  --inst_lit_activity_flag                true
% 2.92/1.00  --inst_restr_to_given                   false
% 2.92/1.00  --inst_activity_threshold               500
% 2.92/1.00  --inst_out_proof                        true
% 2.92/1.00  
% 2.92/1.00  ------ Resolution Options
% 2.92/1.00  
% 2.92/1.00  --resolution_flag                       false
% 2.92/1.00  --res_lit_sel                           adaptive
% 2.92/1.00  --res_lit_sel_side                      none
% 2.92/1.00  --res_ordering                          kbo
% 2.92/1.00  --res_to_prop_solver                    active
% 2.92/1.00  --res_prop_simpl_new                    false
% 2.92/1.00  --res_prop_simpl_given                  true
% 2.92/1.00  --res_passive_queue_type                priority_queues
% 2.92/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.92/1.00  --res_passive_queues_freq               [15;5]
% 2.92/1.00  --res_forward_subs                      full
% 2.92/1.00  --res_backward_subs                     full
% 2.92/1.00  --res_forward_subs_resolution           true
% 2.92/1.00  --res_backward_subs_resolution          true
% 2.92/1.00  --res_orphan_elimination                true
% 2.92/1.00  --res_time_limit                        2.
% 2.92/1.00  --res_out_proof                         true
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Options
% 2.92/1.00  
% 2.92/1.00  --superposition_flag                    true
% 2.92/1.00  --sup_passive_queue_type                priority_queues
% 2.92/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.92/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.92/1.00  --demod_completeness_check              fast
% 2.92/1.00  --demod_use_ground                      true
% 2.92/1.00  --sup_to_prop_solver                    passive
% 2.92/1.00  --sup_prop_simpl_new                    true
% 2.92/1.00  --sup_prop_simpl_given                  true
% 2.92/1.00  --sup_fun_splitting                     false
% 2.92/1.00  --sup_smt_interval                      50000
% 2.92/1.00  
% 2.92/1.00  ------ Superposition Simplification Setup
% 2.92/1.00  
% 2.92/1.00  --sup_indices_passive                   []
% 2.92/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.92/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.92/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_full_bw                           [BwDemod]
% 2.92/1.00  --sup_immed_triv                        [TrivRules]
% 2.92/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.92/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_immed_bw_main                     []
% 2.92/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.92/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.92/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.92/1.00  
% 2.92/1.00  ------ Combination Options
% 2.92/1.00  
% 2.92/1.00  --comb_res_mult                         3
% 2.92/1.00  --comb_sup_mult                         2
% 2.92/1.00  --comb_inst_mult                        10
% 2.92/1.00  
% 2.92/1.00  ------ Debug Options
% 2.92/1.00  
% 2.92/1.00  --dbg_backtrace                         false
% 2.92/1.00  --dbg_dump_prop_clauses                 false
% 2.92/1.00  --dbg_dump_prop_clauses_file            -
% 2.92/1.00  --dbg_out_stat                          false
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  ------ Proving...
% 2.92/1.00  
% 2.92/1.00  
% 2.92/1.00  % SZS status Theorem for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.92/1.00  
% 2.92/1.00  fof(f15,conjecture,(
% 2.92/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f16,negated_conjecture,(
% 2.92/1.00    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 2.92/1.00    inference(negated_conjecture,[],[f15])).
% 2.92/1.00  
% 2.92/1.00  fof(f34,plain,(
% 2.92/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.92/1.00    inference(ennf_transformation,[],[f16])).
% 2.92/1.00  
% 2.92/1.00  fof(f35,plain,(
% 2.92/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.92/1.00    inference(flattening,[],[f34])).
% 2.92/1.00  
% 2.92/1.00  fof(f47,plain,(
% 2.92/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f46,plain,(
% 2.92/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f45,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f44,plain,(
% 2.92/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f48,plain,(
% 2.92/1.00    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f35,f47,f46,f45,f44])).
% 2.92/1.00  
% 2.92/1.00  fof(f76,plain,(
% 2.92/1.00    m1_subset_1(sK7,sK3)),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f4,axiom,(
% 2.92/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f19,plain,(
% 2.92/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.92/1.00    inference(ennf_transformation,[],[f4])).
% 2.92/1.00  
% 2.92/1.00  fof(f20,plain,(
% 2.92/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.92/1.00    inference(flattening,[],[f19])).
% 2.92/1.00  
% 2.92/1.00  fof(f53,plain,(
% 2.92/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f20])).
% 2.92/1.00  
% 2.92/1.00  fof(f78,plain,(
% 2.92/1.00    k1_xboole_0 != sK3),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f3,axiom,(
% 2.92/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f18,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.92/1.00    inference(ennf_transformation,[],[f3])).
% 2.92/1.00  
% 2.92/1.00  fof(f40,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f41,plain,(
% 2.92/1.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f40])).
% 2.92/1.00  
% 2.92/1.00  fof(f52,plain,(
% 2.92/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.92/1.00    inference(cnf_transformation,[],[f41])).
% 2.92/1.00  
% 2.92/1.00  fof(f1,axiom,(
% 2.92/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f36,plain,(
% 2.92/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.92/1.00    inference(nnf_transformation,[],[f1])).
% 2.92/1.00  
% 2.92/1.00  fof(f37,plain,(
% 2.92/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.92/1.00    inference(rectify,[],[f36])).
% 2.92/1.00  
% 2.92/1.00  fof(f38,plain,(
% 2.92/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.92/1.00    introduced(choice_axiom,[])).
% 2.92/1.00  
% 2.92/1.00  fof(f39,plain,(
% 2.92/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.92/1.00  
% 2.92/1.00  fof(f49,plain,(
% 2.92/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f39])).
% 2.92/1.00  
% 2.92/1.00  fof(f75,plain,(
% 2.92/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f9,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f17,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.92/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.92/1.00  
% 2.92/1.00  fof(f25,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f17])).
% 2.92/1.00  
% 2.92/1.00  fof(f59,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f25])).
% 2.92/1.00  
% 2.92/1.00  fof(f73,plain,(
% 2.92/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f11,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f27,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f11])).
% 2.92/1.00  
% 2.92/1.00  fof(f61,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f27])).
% 2.92/1.00  
% 2.92/1.00  fof(f77,plain,(
% 2.92/1.00    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f10,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f26,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f10])).
% 2.92/1.00  
% 2.92/1.00  fof(f60,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f26])).
% 2.92/1.00  
% 2.92/1.00  fof(f6,axiom,(
% 2.92/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f22,plain,(
% 2.92/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.92/1.00    inference(ennf_transformation,[],[f6])).
% 2.92/1.00  
% 2.92/1.00  fof(f42,plain,(
% 2.92/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.92/1.00    inference(nnf_transformation,[],[f22])).
% 2.92/1.00  
% 2.92/1.00  fof(f56,plain,(
% 2.92/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f42])).
% 2.92/1.00  
% 2.92/1.00  fof(f5,axiom,(
% 2.92/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f21,plain,(
% 2.92/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.92/1.00    inference(ennf_transformation,[],[f5])).
% 2.92/1.00  
% 2.92/1.00  fof(f54,plain,(
% 2.92/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f21])).
% 2.92/1.00  
% 2.92/1.00  fof(f7,axiom,(
% 2.92/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f57,plain,(
% 2.92/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f7])).
% 2.92/1.00  
% 2.92/1.00  fof(f8,axiom,(
% 2.92/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f23,plain,(
% 2.92/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.92/1.00    inference(ennf_transformation,[],[f8])).
% 2.92/1.00  
% 2.92/1.00  fof(f24,plain,(
% 2.92/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.92/1.00    inference(flattening,[],[f23])).
% 2.92/1.00  
% 2.92/1.00  fof(f58,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f24])).
% 2.92/1.00  
% 2.92/1.00  fof(f13,axiom,(
% 2.92/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f30,plain,(
% 2.92/1.00    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.92/1.00    inference(ennf_transformation,[],[f13])).
% 2.92/1.00  
% 2.92/1.00  fof(f31,plain,(
% 2.92/1.00    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.92/1.00    inference(flattening,[],[f30])).
% 2.92/1.00  
% 2.92/1.00  fof(f68,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f31])).
% 2.92/1.00  
% 2.92/1.00  fof(f12,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f28,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(ennf_transformation,[],[f12])).
% 2.92/1.00  
% 2.92/1.00  fof(f29,plain,(
% 2.92/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(flattening,[],[f28])).
% 2.92/1.00  
% 2.92/1.00  fof(f43,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.92/1.00    inference(nnf_transformation,[],[f29])).
% 2.92/1.00  
% 2.92/1.00  fof(f62,plain,(
% 2.92/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.92/1.00    inference(cnf_transformation,[],[f43])).
% 2.92/1.00  
% 2.92/1.00  fof(f72,plain,(
% 2.92/1.00    v1_funct_2(sK5,sK3,sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f2,axiom,(
% 2.92/1.00    v1_xboole_0(k1_xboole_0)),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f51,plain,(
% 2.92/1.00    v1_xboole_0(k1_xboole_0)),
% 2.92/1.00    inference(cnf_transformation,[],[f2])).
% 2.92/1.00  
% 2.92/1.00  fof(f70,plain,(
% 2.92/1.00    ~v1_xboole_0(sK4)),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f71,plain,(
% 2.92/1.00    v1_funct_1(sK5)),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f74,plain,(
% 2.92/1.00    v1_funct_1(sK6)),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  fof(f14,axiom,(
% 2.92/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.92/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.92/1.00  
% 2.92/1.00  fof(f32,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.92/1.00    inference(ennf_transformation,[],[f14])).
% 2.92/1.00  
% 2.92/1.00  fof(f33,plain,(
% 2.92/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.92/1.00    inference(flattening,[],[f32])).
% 2.92/1.00  
% 2.92/1.00  fof(f69,plain,(
% 2.92/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.92/1.00    inference(cnf_transformation,[],[f33])).
% 2.92/1.00  
% 2.92/1.00  fof(f79,plain,(
% 2.92/1.00    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 2.92/1.00    inference(cnf_transformation,[],[f48])).
% 2.92/1.00  
% 2.92/1.00  cnf(c_24,negated_conjecture,
% 2.92/1.00      ( m1_subset_1(sK7,sK3) ),
% 2.92/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2149,plain,
% 2.92/1.00      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2160,plain,
% 2.92/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.92/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.92/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3452,plain,
% 2.92/1.00      ( r2_hidden(sK7,sK3) = iProver_top
% 2.92/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2149,c_2160]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_22,negated_conjecture,
% 2.92/1.00      ( k1_xboole_0 != sK3 ),
% 2.92/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3,plain,
% 2.92/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.92/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2368,plain,
% 2.92/1.00      ( r2_hidden(sK1(sK3),sK3) | k1_xboole_0 = sK3 ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2369,plain,
% 2.92/1.00      ( k1_xboole_0 = sK3 | r2_hidden(sK1(sK3),sK3) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_1,plain,
% 2.92/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.92/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2490,plain,
% 2.92/1.00      ( ~ r2_hidden(sK1(sK3),sK3) | ~ v1_xboole_0(sK3) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2491,plain,
% 2.92/1.00      ( r2_hidden(sK1(sK3),sK3) != iProver_top
% 2.92/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2490]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3841,plain,
% 2.92/1.00      ( r2_hidden(sK7,sK3) = iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3452,c_22,c_2369,c_2491]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_25,negated_conjecture,
% 2.92/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 2.92/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2148,plain,
% 2.92/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_10,plain,
% 2.92/1.00      ( v5_relat_1(X0,X1)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.92/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2154,plain,
% 2.92/1.00      ( v5_relat_1(X0,X1) = iProver_top
% 2.92/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2975,plain,
% 2.92/1.00      ( v5_relat_1(sK6,sK2) = iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2148,c_2154]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_27,negated_conjecture,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.92/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2146,plain,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_12,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2152,plain,
% 2.92/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.92/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3033,plain,
% 2.92/1.00      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2146,c_2152]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_23,negated_conjecture,
% 2.92/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2150,plain,
% 2.92/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3153,plain,
% 2.92/1.00      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 2.92/1.00      inference(demodulation,[status(thm)],[c_3033,c_2150]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_11,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2153,plain,
% 2.92/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.92/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3041,plain,
% 2.92/1.00      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2148,c_2153]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3330,plain,
% 2.92/1.00      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 2.92/1.00      inference(light_normalisation,[status(thm)],[c_3153,c_3041]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6,plain,
% 2.92/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.92/1.00      | v5_relat_1(X0,X1)
% 2.92/1.00      | ~ v1_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2158,plain,
% 2.92/1.00      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.92/1.00      | v5_relat_1(X0,X1) = iProver_top
% 2.92/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3609,plain,
% 2.92/1.00      ( v5_relat_1(sK5,k1_relat_1(sK6)) = iProver_top
% 2.92/1.00      | v1_relat_1(sK5) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_3330,c_2158]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_34,plain,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_5,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.92/1.00      | ~ v1_relat_1(X1)
% 2.92/1.00      | v1_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2371,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | v1_relat_1(X0)
% 2.92/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2783,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.92/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 2.92/1.00      | v1_relat_1(sK5) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2371]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2784,plain,
% 2.92/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.92/1.00      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.92/1.00      | v1_relat_1(sK5) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2783]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_8,plain,
% 2.92/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.92/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2813,plain,
% 2.92/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2814,plain,
% 2.92/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2813]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4082,plain,
% 2.92/1.00      ( v5_relat_1(sK5,k1_relat_1(sK6)) = iProver_top ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3609,c_34,c_2784,c_2814]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_9,plain,
% 2.92/1.00      ( ~ v5_relat_1(X0,X1)
% 2.92/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.92/1.00      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.92/1.00      | ~ v1_funct_1(X0)
% 2.92/1.00      | ~ v1_relat_1(X0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2155,plain,
% 2.92/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 2.92/1.00      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 2.92/1.00      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 2.92/1.00      | v1_funct_1(X0) != iProver_top
% 2.92/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_19,plain,
% 2.92/1.00      ( ~ v5_relat_1(X0,X1)
% 2.92/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.92/1.00      | ~ v1_funct_1(X0)
% 2.92/1.00      | ~ v1_relat_1(X0)
% 2.92/1.00      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.92/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2151,plain,
% 2.92/1.00      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.92/1.00      | v5_relat_1(X1,X0) != iProver_top
% 2.92/1.00      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.92/1.00      | v1_funct_1(X1) != iProver_top
% 2.92/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_4035,plain,
% 2.92/1.00      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 2.92/1.00      | v5_relat_1(X1,X0) != iProver_top
% 2.92/1.00      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 2.92/1.00      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 2.92/1.00      | v1_funct_1(X2) != iProver_top
% 2.92/1.00      | v1_funct_1(X1) != iProver_top
% 2.92/1.00      | v1_relat_1(X2) != iProver_top
% 2.92/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2155,c_2151]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6250,plain,
% 2.92/1.00      ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
% 2.92/1.00      | v5_relat_1(sK6,X0) != iProver_top
% 2.92/1.00      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 2.92/1.00      | v1_funct_1(sK6) != iProver_top
% 2.92/1.00      | v1_funct_1(sK5) != iProver_top
% 2.92/1.00      | v1_relat_1(sK6) != iProver_top
% 2.92/1.00      | v1_relat_1(sK5) != iProver_top ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_4082,c_4035]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3042,plain,
% 2.92/1.00      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_2146,c_2153]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_18,plain,
% 2.92/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.92/1.00      | k1_xboole_0 = X2 ),
% 2.92/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_28,negated_conjecture,
% 2.92/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_791,plain,
% 2.92/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.92/1.00      | sK5 != X0
% 2.92/1.00      | sK4 != X2
% 2.92/1.00      | sK3 != X1
% 2.92/1.00      | k1_xboole_0 = X2 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_792,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.92/1.00      | k1_relset_1(sK3,sK4,sK5) = sK3
% 2.92/1.00      | k1_xboole_0 = sK4 ),
% 2.92/1.00      inference(unflattening,[status(thm)],[c_791]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_794,plain,
% 2.92/1.00      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_792,c_27]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3223,plain,
% 2.92/1.00      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 2.92/1.00      inference(superposition,[status(thm)],[c_3042,c_794]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2,plain,
% 2.92/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.92/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_30,negated_conjecture,
% 2.92/1.00      ( ~ v1_xboole_0(sK4) ),
% 2.92/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_503,plain,
% 2.92/1.00      ( sK4 != k1_xboole_0 ),
% 2.92/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_30]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_3333,plain,
% 2.92/1.00      ( k1_relat_1(sK5) = sK3 ),
% 2.92/1.00      inference(global_propositional_subsumption,
% 2.92/1.00                [status(thm)],
% 2.92/1.00                [c_3223,c_503]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6275,plain,
% 2.92/1.00      ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
% 2.92/1.00      | v5_relat_1(sK6,X0) != iProver_top
% 2.92/1.00      | r2_hidden(X1,sK3) != iProver_top
% 2.92/1.00      | v1_funct_1(sK6) != iProver_top
% 2.92/1.00      | v1_funct_1(sK5) != iProver_top
% 2.92/1.00      | v1_relat_1(sK6) != iProver_top
% 2.92/1.00      | v1_relat_1(sK5) != iProver_top ),
% 2.92/1.00      inference(light_normalisation,[status(thm)],[c_6250,c_3333]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_29,negated_conjecture,
% 2.92/1.00      ( v1_funct_1(sK5) ),
% 2.92/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_32,plain,
% 2.92/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_26,negated_conjecture,
% 2.92/1.00      ( v1_funct_1(sK6) ),
% 2.92/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_35,plain,
% 2.92/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_36,plain,
% 2.92/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2780,plain,
% 2.92/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 2.92/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
% 2.92/1.00      | v1_relat_1(sK6) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_2371]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2781,plain,
% 2.92/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 2.92/1.00      | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
% 2.92/1.00      | v1_relat_1(sK6) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2780]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2810,plain,
% 2.92/1.00      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
% 2.92/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_2811,plain,
% 2.92/1.00      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 2.92/1.00      inference(predicate_to_equality,[status(thm)],[c_2810]) ).
% 2.92/1.00  
% 2.92/1.00  cnf(c_6890,plain,
% 2.92/1.00      ( k7_partfun1(X0,sK6,k1_funct_1(sK5,X1)) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
% 2.92/1.01      | v5_relat_1(sK6,X0) != iProver_top
% 2.92/1.01      | r2_hidden(X1,sK3) != iProver_top ),
% 2.92/1.01      inference(global_propositional_subsumption,
% 2.92/1.01                [status(thm)],
% 2.92/1.01                [c_6275,c_32,c_34,c_35,c_36,c_2781,c_2784,c_2811,c_2814]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_6899,plain,
% 2.92/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 2.92/1.01      | r2_hidden(X0,sK3) != iProver_top ),
% 2.92/1.01      inference(superposition,[status(thm)],[c_2975,c_6890]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_6958,plain,
% 2.92/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 2.92/1.01      inference(superposition,[status(thm)],[c_3841,c_6899]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_20,plain,
% 2.92/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.92/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.92/1.01      | ~ m1_subset_1(X5,X1)
% 2.92/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.92/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.92/1.01      | ~ v1_funct_1(X4)
% 2.92/1.01      | ~ v1_funct_1(X0)
% 2.92/1.01      | v1_xboole_0(X2)
% 2.92/1.01      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.92/1.01      | k1_xboole_0 = X1 ),
% 2.92/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_764,plain,
% 2.92/1.01      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 2.92/1.01      | ~ m1_subset_1(X5,X0)
% 2.92/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.92/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.92/1.01      | ~ v1_funct_1(X2)
% 2.92/1.01      | ~ v1_funct_1(X4)
% 2.92/1.01      | v1_xboole_0(X1)
% 2.92/1.01      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.92/1.01      | sK5 != X2
% 2.92/1.01      | sK4 != X1
% 2.92/1.01      | sK3 != X0
% 2.92/1.01      | k1_xboole_0 = X0 ),
% 2.92/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_765,plain,
% 2.92/1.01      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1))
% 2.92/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
% 2.92/1.01      | ~ m1_subset_1(X2,sK3)
% 2.92/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.92/1.01      | ~ v1_funct_1(X1)
% 2.92/1.01      | ~ v1_funct_1(sK5)
% 2.92/1.01      | v1_xboole_0(sK4)
% 2.92/1.01      | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 2.92/1.01      | k1_xboole_0 = sK3 ),
% 2.92/1.01      inference(unflattening,[status(thm)],[c_764]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_769,plain,
% 2.92/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 2.92/1.01      | ~ v1_funct_1(X1)
% 2.92/1.01      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1))
% 2.92/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
% 2.92/1.01      | ~ m1_subset_1(X2,sK3) ),
% 2.92/1.01      inference(global_propositional_subsumption,
% 2.92/1.01                [status(thm)],
% 2.92/1.01                [c_765,c_30,c_29,c_27,c_22]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_770,plain,
% 2.92/1.01      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1))
% 2.92/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
% 2.92/1.01      | ~ m1_subset_1(X2,sK3)
% 2.92/1.01      | ~ v1_funct_1(X1)
% 2.92/1.01      | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2)) ),
% 2.92/1.01      inference(renaming,[status(thm)],[c_769]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_2141,plain,
% 2.92/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 2.92/1.01      | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 2.92/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 2.92/1.01      | m1_subset_1(X2,sK3) != iProver_top
% 2.92/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.92/1.01      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_2690,plain,
% 2.92/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 2.92/1.01      | m1_subset_1(X0,sK3) != iProver_top
% 2.92/1.01      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 2.92/1.01      | v1_funct_1(sK6) != iProver_top ),
% 2.92/1.01      inference(superposition,[status(thm)],[c_2150,c_2141]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_2769,plain,
% 2.92/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 2.92/1.01      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.92/1.01      inference(global_propositional_subsumption,
% 2.92/1.01                [status(thm)],
% 2.92/1.01                [c_2690,c_35,c_36]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_2777,plain,
% 2.92/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 2.92/1.01      inference(superposition,[status(thm)],[c_2149,c_2769]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_21,negated_conjecture,
% 2.92/1.01      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
% 2.92/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(c_2779,plain,
% 2.92/1.01      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 2.92/1.01      inference(demodulation,[status(thm)],[c_2777,c_21]) ).
% 2.92/1.01  
% 2.92/1.01  cnf(contradiction,plain,
% 2.92/1.01      ( $false ),
% 2.92/1.01      inference(minisat,[status(thm)],[c_6958,c_2779]) ).
% 2.92/1.01  
% 2.92/1.01  
% 2.92/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.92/1.01  
% 2.92/1.01  ------                               Statistics
% 2.92/1.01  
% 2.92/1.01  ------ General
% 2.92/1.01  
% 2.92/1.01  abstr_ref_over_cycles:                  0
% 2.92/1.01  abstr_ref_under_cycles:                 0
% 2.92/1.01  gc_basic_clause_elim:                   0
% 2.92/1.01  forced_gc_time:                         0
% 2.92/1.01  parsing_time:                           0.012
% 2.92/1.01  unif_index_cands_time:                  0.
% 2.92/1.01  unif_index_add_time:                    0.
% 2.92/1.01  orderings_time:                         0.
% 2.92/1.01  out_proof_time:                         0.015
% 2.92/1.01  total_time:                             0.25
% 2.92/1.01  num_of_symbols:                         57
% 2.92/1.01  num_of_terms:                           5829
% 2.92/1.01  
% 2.92/1.01  ------ Preprocessing
% 2.92/1.01  
% 2.92/1.01  num_of_splits:                          0
% 2.92/1.01  num_of_split_atoms:                     0
% 2.92/1.01  num_of_reused_defs:                     0
% 2.92/1.01  num_eq_ax_congr_red:                    18
% 2.92/1.01  num_of_sem_filtered_clauses:            1
% 2.92/1.01  num_of_subtypes:                        0
% 2.92/1.01  monotx_restored_types:                  0
% 2.92/1.01  sat_num_of_epr_types:                   0
% 2.92/1.01  sat_num_of_non_cyclic_types:            0
% 2.92/1.01  sat_guarded_non_collapsed_types:        0
% 2.92/1.01  num_pure_diseq_elim:                    0
% 2.92/1.01  simp_replaced_by:                       0
% 2.92/1.01  res_preprocessed:                       146
% 2.92/1.01  prep_upred:                             0
% 2.92/1.01  prep_unflattend:                        60
% 2.92/1.01  smt_new_axioms:                         0
% 2.92/1.01  pred_elim_cands:                        7
% 2.92/1.01  pred_elim:                              1
% 2.92/1.01  pred_elim_cl:                           3
% 2.92/1.01  pred_elim_cycles:                       9
% 2.92/1.01  merged_defs:                            0
% 2.92/1.01  merged_defs_ncl:                        0
% 2.92/1.01  bin_hyper_res:                          0
% 2.92/1.01  prep_cycles:                            4
% 2.92/1.01  pred_elim_time:                         0.031
% 2.92/1.01  splitting_time:                         0.
% 2.92/1.01  sem_filter_time:                        0.
% 2.92/1.01  monotx_time:                            0.
% 2.92/1.01  subtype_inf_time:                       0.
% 2.92/1.01  
% 2.92/1.01  ------ Problem properties
% 2.92/1.01  
% 2.92/1.01  clauses:                                28
% 2.92/1.01  conjectures:                            9
% 2.92/1.01  epr:                                    9
% 2.92/1.01  horn:                                   23
% 2.92/1.01  ground:                                 13
% 2.92/1.01  unary:                                  12
% 2.92/1.01  binary:                                 7
% 2.92/1.01  lits:                                   67
% 2.92/1.01  lits_eq:                                16
% 2.92/1.01  fd_pure:                                0
% 2.92/1.01  fd_pseudo:                              0
% 2.92/1.01  fd_cond:                                2
% 2.92/1.01  fd_pseudo_cond:                         0
% 2.92/1.01  ac_symbols:                             0
% 2.92/1.01  
% 2.92/1.01  ------ Propositional Solver
% 2.92/1.01  
% 2.92/1.01  prop_solver_calls:                      29
% 2.92/1.01  prop_fast_solver_calls:                 1386
% 2.92/1.01  smt_solver_calls:                       0
% 2.92/1.01  smt_fast_solver_calls:                  0
% 2.92/1.01  prop_num_of_clauses:                    2030
% 2.92/1.01  prop_preprocess_simplified:             6833
% 2.92/1.01  prop_fo_subsumed:                       59
% 2.92/1.01  prop_solver_time:                       0.
% 2.92/1.01  smt_solver_time:                        0.
% 2.92/1.01  smt_fast_solver_time:                   0.
% 2.92/1.01  prop_fast_solver_time:                  0.
% 2.92/1.01  prop_unsat_core_time:                   0.
% 2.92/1.01  
% 2.92/1.01  ------ QBF
% 2.92/1.01  
% 2.92/1.01  qbf_q_res:                              0
% 2.92/1.01  qbf_num_tautologies:                    0
% 2.92/1.01  qbf_prep_cycles:                        0
% 2.92/1.01  
% 2.92/1.01  ------ BMC1
% 2.92/1.01  
% 2.92/1.01  bmc1_current_bound:                     -1
% 2.92/1.01  bmc1_last_solved_bound:                 -1
% 2.92/1.01  bmc1_unsat_core_size:                   -1
% 2.92/1.01  bmc1_unsat_core_parents_size:           -1
% 2.92/1.01  bmc1_merge_next_fun:                    0
% 2.92/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.92/1.01  
% 2.92/1.01  ------ Instantiation
% 2.92/1.01  
% 2.92/1.01  inst_num_of_clauses:                    766
% 2.92/1.01  inst_num_in_passive:                    394
% 2.92/1.01  inst_num_in_active:                     343
% 2.92/1.01  inst_num_in_unprocessed:                29
% 2.92/1.01  inst_num_of_loops:                      450
% 2.92/1.01  inst_num_of_learning_restarts:          0
% 2.92/1.01  inst_num_moves_active_passive:          104
% 2.92/1.01  inst_lit_activity:                      0
% 2.92/1.01  inst_lit_activity_moves:                0
% 2.92/1.01  inst_num_tautologies:                   0
% 2.92/1.01  inst_num_prop_implied:                  0
% 2.92/1.01  inst_num_existing_simplified:           0
% 2.92/1.01  inst_num_eq_res_simplified:             0
% 2.92/1.01  inst_num_child_elim:                    0
% 2.92/1.01  inst_num_of_dismatching_blockings:      121
% 2.92/1.01  inst_num_of_non_proper_insts:           495
% 2.92/1.01  inst_num_of_duplicates:                 0
% 2.92/1.01  inst_inst_num_from_inst_to_res:         0
% 2.92/1.01  inst_dismatching_checking_time:         0.
% 2.92/1.01  
% 2.92/1.01  ------ Resolution
% 2.92/1.01  
% 2.92/1.01  res_num_of_clauses:                     0
% 2.92/1.01  res_num_in_passive:                     0
% 2.92/1.01  res_num_in_active:                      0
% 2.92/1.01  res_num_of_loops:                       150
% 2.92/1.01  res_forward_subset_subsumed:            63
% 2.92/1.01  res_backward_subset_subsumed:           0
% 2.92/1.01  res_forward_subsumed:                   0
% 2.92/1.01  res_backward_subsumed:                  0
% 2.92/1.01  res_forward_subsumption_resolution:     0
% 2.92/1.01  res_backward_subsumption_resolution:    0
% 2.92/1.01  res_clause_to_clause_subsumption:       400
% 2.92/1.01  res_orphan_elimination:                 0
% 2.92/1.01  res_tautology_del:                      68
% 2.92/1.01  res_num_eq_res_simplified:              0
% 2.92/1.01  res_num_sel_changes:                    0
% 2.92/1.01  res_moves_from_active_to_pass:          0
% 2.92/1.01  
% 2.92/1.01  ------ Superposition
% 2.92/1.01  
% 2.92/1.01  sup_time_total:                         0.
% 2.92/1.01  sup_time_generating:                    0.
% 2.92/1.01  sup_time_sim_full:                      0.
% 2.92/1.01  sup_time_sim_immed:                     0.
% 2.92/1.01  
% 2.92/1.01  sup_num_of_clauses:                     106
% 2.92/1.01  sup_num_in_active:                      83
% 2.92/1.01  sup_num_in_passive:                     23
% 2.92/1.01  sup_num_of_loops:                       88
% 2.92/1.01  sup_fw_superposition:                   86
% 2.92/1.01  sup_bw_superposition:                   11
% 2.92/1.01  sup_immediate_simplified:               17
% 2.92/1.01  sup_given_eliminated:                   0
% 2.92/1.01  comparisons_done:                       0
% 2.92/1.01  comparisons_avoided:                    6
% 2.92/1.01  
% 2.92/1.01  ------ Simplifications
% 2.92/1.01  
% 2.92/1.01  
% 2.92/1.01  sim_fw_subset_subsumed:                 5
% 2.92/1.01  sim_bw_subset_subsumed:                 5
% 2.92/1.01  sim_fw_subsumed:                        3
% 2.92/1.01  sim_bw_subsumed:                        0
% 2.92/1.01  sim_fw_subsumption_res:                 2
% 2.92/1.01  sim_bw_subsumption_res:                 0
% 2.92/1.01  sim_tautology_del:                      4
% 2.92/1.01  sim_eq_tautology_del:                   3
% 2.92/1.01  sim_eq_res_simp:                        0
% 2.92/1.01  sim_fw_demodulated:                     1
% 2.92/1.01  sim_bw_demodulated:                     4
% 2.92/1.01  sim_light_normalised:                   8
% 2.92/1.01  sim_joinable_taut:                      0
% 2.92/1.01  sim_joinable_simp:                      0
% 2.92/1.01  sim_ac_normalised:                      0
% 2.92/1.01  sim_smt_subsumption:                    0
% 2.92/1.01  
%------------------------------------------------------------------------------
