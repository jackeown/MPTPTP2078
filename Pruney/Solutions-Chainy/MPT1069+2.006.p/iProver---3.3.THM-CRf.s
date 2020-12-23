%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:42 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 639 expanded)
%              Number of clauses        :  101 ( 173 expanded)
%              Number of leaves         :   21 ( 219 expanded)
%              Depth                    :   21
%              Number of atoms          :  662 (4930 expanded)
%              Number of equality atoms :  265 (1338 expanded)
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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f43,f42,f41,f40])).

fof(f74,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    k1_xboole_0 != sK1 ),
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

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f60,plain,(
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

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f77,plain,(
    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1036,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1040,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2986,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1040])).

cnf(c_39,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1250,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1251,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_1321,plain,
    ( r2_hidden(X0,sK1)
    | ~ m1_subset_1(X0,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1520,plain,
    ( r2_hidden(sK5,sK1)
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_1521,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | m1_subset_1(sK5,sK1) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1520])).

cnf(c_3331,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2986,c_39,c_24,c_1251,c_1521])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1035,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1038,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2108,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1035,c_1038])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_435,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK2,sK0,sK4) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_436,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(sK2,sK0,sK4))))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1023,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_1355,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1023])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_632,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1263,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1265,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_1833,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_32,c_34,c_35,c_36,c_0,c_1265])).

cnf(c_2136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2108,c_1833])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1037,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3589,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_1037])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_412,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK2,sK0,sK4) != X3
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_413,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_1024,plain,
    ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X2,X0,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_1666,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1024])).

cnf(c_1768,plain,
    ( v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1666,c_32,c_34,c_35,c_36,c_0,c_1265])).

cnf(c_2137,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2108,c_1768])).

cnf(c_4308,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3589,c_34,c_2137])).

cnf(c_4309,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4308])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_307,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(resolution,[status(thm)],[c_9,c_14])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_307,c_8])).

cnf(c_1028,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_1978,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1035,c_1028])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2444,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1978,c_37])).

cnf(c_2445,plain,
    ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2444])).

cnf(c_4318,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | k1_relat_1(sK4) = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4309,c_2445])).

cnf(c_4401,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3331,c_4318])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_334,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_1027,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_1680,plain,
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
    inference(equality_resolution,[status(thm)],[c_1027])).

cnf(c_33,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_75,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_76,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_631,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1275,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_1276,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1275])).

cnf(c_1839,plain,
    ( m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1680,c_33,c_34,c_35,c_36,c_24,c_75,c_76,c_1276])).

cnf(c_1840,plain,
    ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1839])).

cnf(c_1850,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1840])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1964,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1850,c_37,c_38])).

cnf(c_1972,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1036,c_1964])).

cnf(c_23,negated_conjecture,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2387,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1972,c_23])).

cnf(c_4514,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4401,c_2387])).

cnf(c_4527,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4514,c_2136])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4543,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4527,c_2])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_153,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_7])).

cnf(c_154,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_1320,plain,
    ( ~ v1_funct_2(X0,sK1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_1704,plain,
    ( ~ v1_funct_2(X0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1320])).

cnf(c_1783,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_1784,plain,
    ( v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1489,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1490,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1489])).

cnf(c_1492,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_80,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4543,c_1784,c_1492,c_1251,c_80,c_24,c_36,c_35,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.96/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/0.98  
% 2.96/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.96/0.98  
% 2.96/0.98  ------  iProver source info
% 2.96/0.98  
% 2.96/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.96/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.96/0.98  git: non_committed_changes: false
% 2.96/0.98  git: last_make_outside_of_git: false
% 2.96/0.98  
% 2.96/0.98  ------ 
% 2.96/0.98  
% 2.96/0.98  ------ Input Options
% 2.96/0.98  
% 2.96/0.98  --out_options                           all
% 2.96/0.98  --tptp_safe_out                         true
% 2.96/0.98  --problem_path                          ""
% 2.96/0.98  --include_path                          ""
% 2.96/0.98  --clausifier                            res/vclausify_rel
% 2.96/0.98  --clausifier_options                    --mode clausify
% 2.96/0.98  --stdin                                 false
% 2.96/0.98  --stats_out                             all
% 2.96/0.98  
% 2.96/0.98  ------ General Options
% 2.96/0.98  
% 2.96/0.98  --fof                                   false
% 2.96/0.98  --time_out_real                         305.
% 2.96/0.98  --time_out_virtual                      -1.
% 2.96/0.98  --symbol_type_check                     false
% 2.96/0.98  --clausify_out                          false
% 2.96/0.98  --sig_cnt_out                           false
% 2.96/0.98  --trig_cnt_out                          false
% 2.96/0.98  --trig_cnt_out_tolerance                1.
% 2.96/0.98  --trig_cnt_out_sk_spl                   false
% 2.96/0.98  --abstr_cl_out                          false
% 2.96/0.98  
% 2.96/0.98  ------ Global Options
% 2.96/0.98  
% 2.96/0.98  --schedule                              default
% 2.96/0.98  --add_important_lit                     false
% 2.96/0.98  --prop_solver_per_cl                    1000
% 2.96/0.98  --min_unsat_core                        false
% 2.96/0.98  --soft_assumptions                      false
% 2.96/0.98  --soft_lemma_size                       3
% 2.96/0.98  --prop_impl_unit_size                   0
% 2.96/0.98  --prop_impl_unit                        []
% 2.96/0.98  --share_sel_clauses                     true
% 2.96/0.98  --reset_solvers                         false
% 2.96/0.98  --bc_imp_inh                            [conj_cone]
% 2.96/0.98  --conj_cone_tolerance                   3.
% 2.96/0.98  --extra_neg_conj                        none
% 2.96/0.98  --large_theory_mode                     true
% 2.96/0.98  --prolific_symb_bound                   200
% 2.96/0.98  --lt_threshold                          2000
% 2.96/0.98  --clause_weak_htbl                      true
% 2.96/0.98  --gc_record_bc_elim                     false
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing Options
% 2.96/0.98  
% 2.96/0.98  --preprocessing_flag                    true
% 2.96/0.98  --time_out_prep_mult                    0.1
% 2.96/0.98  --splitting_mode                        input
% 2.96/0.98  --splitting_grd                         true
% 2.96/0.98  --splitting_cvd                         false
% 2.96/0.98  --splitting_cvd_svl                     false
% 2.96/0.98  --splitting_nvd                         32
% 2.96/0.98  --sub_typing                            true
% 2.96/0.98  --prep_gs_sim                           true
% 2.96/0.98  --prep_unflatten                        true
% 2.96/0.98  --prep_res_sim                          true
% 2.96/0.98  --prep_upred                            true
% 2.96/0.98  --prep_sem_filter                       exhaustive
% 2.96/0.98  --prep_sem_filter_out                   false
% 2.96/0.98  --pred_elim                             true
% 2.96/0.98  --res_sim_input                         true
% 2.96/0.98  --eq_ax_congr_red                       true
% 2.96/0.98  --pure_diseq_elim                       true
% 2.96/0.98  --brand_transform                       false
% 2.96/0.98  --non_eq_to_eq                          false
% 2.96/0.98  --prep_def_merge                        true
% 2.96/0.98  --prep_def_merge_prop_impl              false
% 2.96/0.98  --prep_def_merge_mbd                    true
% 2.96/0.98  --prep_def_merge_tr_red                 false
% 2.96/0.98  --prep_def_merge_tr_cl                  false
% 2.96/0.98  --smt_preprocessing                     true
% 2.96/0.98  --smt_ac_axioms                         fast
% 2.96/0.98  --preprocessed_out                      false
% 2.96/0.98  --preprocessed_stats                    false
% 2.96/0.98  
% 2.96/0.98  ------ Abstraction refinement Options
% 2.96/0.98  
% 2.96/0.98  --abstr_ref                             []
% 2.96/0.98  --abstr_ref_prep                        false
% 2.96/0.98  --abstr_ref_until_sat                   false
% 2.96/0.98  --abstr_ref_sig_restrict                funpre
% 2.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.98  --abstr_ref_under                       []
% 2.96/0.98  
% 2.96/0.98  ------ SAT Options
% 2.96/0.98  
% 2.96/0.98  --sat_mode                              false
% 2.96/0.98  --sat_fm_restart_options                ""
% 2.96/0.98  --sat_gr_def                            false
% 2.96/0.98  --sat_epr_types                         true
% 2.96/0.98  --sat_non_cyclic_types                  false
% 2.96/0.98  --sat_finite_models                     false
% 2.96/0.98  --sat_fm_lemmas                         false
% 2.96/0.98  --sat_fm_prep                           false
% 2.96/0.98  --sat_fm_uc_incr                        true
% 2.96/0.98  --sat_out_model                         small
% 2.96/0.98  --sat_out_clauses                       false
% 2.96/0.98  
% 2.96/0.98  ------ QBF Options
% 2.96/0.98  
% 2.96/0.98  --qbf_mode                              false
% 2.96/0.98  --qbf_elim_univ                         false
% 2.96/0.98  --qbf_dom_inst                          none
% 2.96/0.98  --qbf_dom_pre_inst                      false
% 2.96/0.98  --qbf_sk_in                             false
% 2.96/0.98  --qbf_pred_elim                         true
% 2.96/0.98  --qbf_split                             512
% 2.96/0.98  
% 2.96/0.98  ------ BMC1 Options
% 2.96/0.98  
% 2.96/0.98  --bmc1_incremental                      false
% 2.96/0.98  --bmc1_axioms                           reachable_all
% 2.96/0.98  --bmc1_min_bound                        0
% 2.96/0.98  --bmc1_max_bound                        -1
% 2.96/0.98  --bmc1_max_bound_default                -1
% 2.96/0.98  --bmc1_symbol_reachability              true
% 2.96/0.98  --bmc1_property_lemmas                  false
% 2.96/0.98  --bmc1_k_induction                      false
% 2.96/0.98  --bmc1_non_equiv_states                 false
% 2.96/0.98  --bmc1_deadlock                         false
% 2.96/0.98  --bmc1_ucm                              false
% 2.96/0.98  --bmc1_add_unsat_core                   none
% 2.96/0.98  --bmc1_unsat_core_children              false
% 2.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.98  --bmc1_out_stat                         full
% 2.96/0.98  --bmc1_ground_init                      false
% 2.96/0.98  --bmc1_pre_inst_next_state              false
% 2.96/0.98  --bmc1_pre_inst_state                   false
% 2.96/0.98  --bmc1_pre_inst_reach_state             false
% 2.96/0.98  --bmc1_out_unsat_core                   false
% 2.96/0.98  --bmc1_aig_witness_out                  false
% 2.96/0.98  --bmc1_verbose                          false
% 2.96/0.98  --bmc1_dump_clauses_tptp                false
% 2.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.98  --bmc1_dump_file                        -
% 2.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.98  --bmc1_ucm_extend_mode                  1
% 2.96/0.98  --bmc1_ucm_init_mode                    2
% 2.96/0.98  --bmc1_ucm_cone_mode                    none
% 2.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.98  --bmc1_ucm_relax_model                  4
% 2.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.98  --bmc1_ucm_layered_model                none
% 2.96/0.98  --bmc1_ucm_max_lemma_size               10
% 2.96/0.98  
% 2.96/0.98  ------ AIG Options
% 2.96/0.98  
% 2.96/0.98  --aig_mode                              false
% 2.96/0.98  
% 2.96/0.98  ------ Instantiation Options
% 2.96/0.98  
% 2.96/0.98  --instantiation_flag                    true
% 2.96/0.98  --inst_sos_flag                         false
% 2.96/0.98  --inst_sos_phase                        true
% 2.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel_side                     num_symb
% 2.96/0.98  --inst_solver_per_active                1400
% 2.96/0.98  --inst_solver_calls_frac                1.
% 2.96/0.98  --inst_passive_queue_type               priority_queues
% 2.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.98  --inst_passive_queues_freq              [25;2]
% 2.96/0.98  --inst_dismatching                      true
% 2.96/0.98  --inst_eager_unprocessed_to_passive     true
% 2.96/0.98  --inst_prop_sim_given                   true
% 2.96/0.98  --inst_prop_sim_new                     false
% 2.96/0.98  --inst_subs_new                         false
% 2.96/0.98  --inst_eq_res_simp                      false
% 2.96/0.98  --inst_subs_given                       false
% 2.96/0.98  --inst_orphan_elimination               true
% 2.96/0.98  --inst_learning_loop_flag               true
% 2.96/0.98  --inst_learning_start                   3000
% 2.96/0.98  --inst_learning_factor                  2
% 2.96/0.98  --inst_start_prop_sim_after_learn       3
% 2.96/0.98  --inst_sel_renew                        solver
% 2.96/0.98  --inst_lit_activity_flag                true
% 2.96/0.98  --inst_restr_to_given                   false
% 2.96/0.98  --inst_activity_threshold               500
% 2.96/0.98  --inst_out_proof                        true
% 2.96/0.98  
% 2.96/0.98  ------ Resolution Options
% 2.96/0.98  
% 2.96/0.98  --resolution_flag                       true
% 2.96/0.98  --res_lit_sel                           adaptive
% 2.96/0.98  --res_lit_sel_side                      none
% 2.96/0.98  --res_ordering                          kbo
% 2.96/0.98  --res_to_prop_solver                    active
% 2.96/0.98  --res_prop_simpl_new                    false
% 2.96/0.98  --res_prop_simpl_given                  true
% 2.96/0.98  --res_passive_queue_type                priority_queues
% 2.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.98  --res_passive_queues_freq               [15;5]
% 2.96/0.98  --res_forward_subs                      full
% 2.96/0.98  --res_backward_subs                     full
% 2.96/0.98  --res_forward_subs_resolution           true
% 2.96/0.98  --res_backward_subs_resolution          true
% 2.96/0.98  --res_orphan_elimination                true
% 2.96/0.98  --res_time_limit                        2.
% 2.96/0.98  --res_out_proof                         true
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Options
% 2.96/0.98  
% 2.96/0.98  --superposition_flag                    true
% 2.96/0.98  --sup_passive_queue_type                priority_queues
% 2.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.98  --demod_completeness_check              fast
% 2.96/0.98  --demod_use_ground                      true
% 2.96/0.98  --sup_to_prop_solver                    passive
% 2.96/0.98  --sup_prop_simpl_new                    true
% 2.96/0.98  --sup_prop_simpl_given                  true
% 2.96/0.98  --sup_fun_splitting                     false
% 2.96/0.98  --sup_smt_interval                      50000
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Simplification Setup
% 2.96/0.98  
% 2.96/0.98  --sup_indices_passive                   []
% 2.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_full_bw                           [BwDemod]
% 2.96/0.98  --sup_immed_triv                        [TrivRules]
% 2.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_immed_bw_main                     []
% 2.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  
% 2.96/0.98  ------ Combination Options
% 2.96/0.98  
% 2.96/0.98  --comb_res_mult                         3
% 2.96/0.98  --comb_sup_mult                         2
% 2.96/0.98  --comb_inst_mult                        10
% 2.96/0.98  
% 2.96/0.98  ------ Debug Options
% 2.96/0.98  
% 2.96/0.98  --dbg_backtrace                         false
% 2.96/0.98  --dbg_dump_prop_clauses                 false
% 2.96/0.98  --dbg_dump_prop_clauses_file            -
% 2.96/0.98  --dbg_out_stat                          false
% 2.96/0.98  ------ Parsing...
% 2.96/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.96/0.98  ------ Proving...
% 2.96/0.98  ------ Problem Properties 
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  clauses                                 26
% 2.96/0.98  conjectures                             9
% 2.96/0.98  EPR                                     10
% 2.96/0.98  Horn                                    19
% 2.96/0.98  unary                                   12
% 2.96/0.98  binary                                  3
% 2.96/0.98  lits                                    75
% 2.96/0.98  lits eq                                 21
% 2.96/0.98  fd_pure                                 0
% 2.96/0.98  fd_pseudo                               0
% 2.96/0.98  fd_cond                                 6
% 2.96/0.98  fd_pseudo_cond                          0
% 2.96/0.98  AC symbols                              0
% 2.96/0.98  
% 2.96/0.98  ------ Schedule dynamic 5 is on 
% 2.96/0.98  
% 2.96/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  ------ 
% 2.96/0.98  Current options:
% 2.96/0.98  ------ 
% 2.96/0.98  
% 2.96/0.98  ------ Input Options
% 2.96/0.98  
% 2.96/0.98  --out_options                           all
% 2.96/0.98  --tptp_safe_out                         true
% 2.96/0.98  --problem_path                          ""
% 2.96/0.98  --include_path                          ""
% 2.96/0.98  --clausifier                            res/vclausify_rel
% 2.96/0.98  --clausifier_options                    --mode clausify
% 2.96/0.98  --stdin                                 false
% 2.96/0.98  --stats_out                             all
% 2.96/0.98  
% 2.96/0.98  ------ General Options
% 2.96/0.98  
% 2.96/0.98  --fof                                   false
% 2.96/0.98  --time_out_real                         305.
% 2.96/0.98  --time_out_virtual                      -1.
% 2.96/0.98  --symbol_type_check                     false
% 2.96/0.98  --clausify_out                          false
% 2.96/0.98  --sig_cnt_out                           false
% 2.96/0.98  --trig_cnt_out                          false
% 2.96/0.98  --trig_cnt_out_tolerance                1.
% 2.96/0.98  --trig_cnt_out_sk_spl                   false
% 2.96/0.98  --abstr_cl_out                          false
% 2.96/0.98  
% 2.96/0.98  ------ Global Options
% 2.96/0.98  
% 2.96/0.98  --schedule                              default
% 2.96/0.98  --add_important_lit                     false
% 2.96/0.98  --prop_solver_per_cl                    1000
% 2.96/0.98  --min_unsat_core                        false
% 2.96/0.98  --soft_assumptions                      false
% 2.96/0.98  --soft_lemma_size                       3
% 2.96/0.98  --prop_impl_unit_size                   0
% 2.96/0.98  --prop_impl_unit                        []
% 2.96/0.98  --share_sel_clauses                     true
% 2.96/0.98  --reset_solvers                         false
% 2.96/0.98  --bc_imp_inh                            [conj_cone]
% 2.96/0.98  --conj_cone_tolerance                   3.
% 2.96/0.98  --extra_neg_conj                        none
% 2.96/0.98  --large_theory_mode                     true
% 2.96/0.98  --prolific_symb_bound                   200
% 2.96/0.98  --lt_threshold                          2000
% 2.96/0.98  --clause_weak_htbl                      true
% 2.96/0.98  --gc_record_bc_elim                     false
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing Options
% 2.96/0.98  
% 2.96/0.98  --preprocessing_flag                    true
% 2.96/0.98  --time_out_prep_mult                    0.1
% 2.96/0.98  --splitting_mode                        input
% 2.96/0.98  --splitting_grd                         true
% 2.96/0.98  --splitting_cvd                         false
% 2.96/0.98  --splitting_cvd_svl                     false
% 2.96/0.98  --splitting_nvd                         32
% 2.96/0.98  --sub_typing                            true
% 2.96/0.98  --prep_gs_sim                           true
% 2.96/0.98  --prep_unflatten                        true
% 2.96/0.98  --prep_res_sim                          true
% 2.96/0.98  --prep_upred                            true
% 2.96/0.98  --prep_sem_filter                       exhaustive
% 2.96/0.98  --prep_sem_filter_out                   false
% 2.96/0.98  --pred_elim                             true
% 2.96/0.98  --res_sim_input                         true
% 2.96/0.98  --eq_ax_congr_red                       true
% 2.96/0.98  --pure_diseq_elim                       true
% 2.96/0.98  --brand_transform                       false
% 2.96/0.98  --non_eq_to_eq                          false
% 2.96/0.98  --prep_def_merge                        true
% 2.96/0.98  --prep_def_merge_prop_impl              false
% 2.96/0.98  --prep_def_merge_mbd                    true
% 2.96/0.98  --prep_def_merge_tr_red                 false
% 2.96/0.98  --prep_def_merge_tr_cl                  false
% 2.96/0.98  --smt_preprocessing                     true
% 2.96/0.98  --smt_ac_axioms                         fast
% 2.96/0.98  --preprocessed_out                      false
% 2.96/0.98  --preprocessed_stats                    false
% 2.96/0.98  
% 2.96/0.98  ------ Abstraction refinement Options
% 2.96/0.98  
% 2.96/0.98  --abstr_ref                             []
% 2.96/0.98  --abstr_ref_prep                        false
% 2.96/0.98  --abstr_ref_until_sat                   false
% 2.96/0.98  --abstr_ref_sig_restrict                funpre
% 2.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.96/0.98  --abstr_ref_under                       []
% 2.96/0.98  
% 2.96/0.98  ------ SAT Options
% 2.96/0.98  
% 2.96/0.98  --sat_mode                              false
% 2.96/0.98  --sat_fm_restart_options                ""
% 2.96/0.98  --sat_gr_def                            false
% 2.96/0.98  --sat_epr_types                         true
% 2.96/0.98  --sat_non_cyclic_types                  false
% 2.96/0.98  --sat_finite_models                     false
% 2.96/0.98  --sat_fm_lemmas                         false
% 2.96/0.98  --sat_fm_prep                           false
% 2.96/0.98  --sat_fm_uc_incr                        true
% 2.96/0.98  --sat_out_model                         small
% 2.96/0.98  --sat_out_clauses                       false
% 2.96/0.98  
% 2.96/0.98  ------ QBF Options
% 2.96/0.98  
% 2.96/0.98  --qbf_mode                              false
% 2.96/0.98  --qbf_elim_univ                         false
% 2.96/0.98  --qbf_dom_inst                          none
% 2.96/0.98  --qbf_dom_pre_inst                      false
% 2.96/0.98  --qbf_sk_in                             false
% 2.96/0.98  --qbf_pred_elim                         true
% 2.96/0.98  --qbf_split                             512
% 2.96/0.98  
% 2.96/0.98  ------ BMC1 Options
% 2.96/0.98  
% 2.96/0.98  --bmc1_incremental                      false
% 2.96/0.98  --bmc1_axioms                           reachable_all
% 2.96/0.98  --bmc1_min_bound                        0
% 2.96/0.98  --bmc1_max_bound                        -1
% 2.96/0.98  --bmc1_max_bound_default                -1
% 2.96/0.98  --bmc1_symbol_reachability              true
% 2.96/0.98  --bmc1_property_lemmas                  false
% 2.96/0.98  --bmc1_k_induction                      false
% 2.96/0.98  --bmc1_non_equiv_states                 false
% 2.96/0.98  --bmc1_deadlock                         false
% 2.96/0.98  --bmc1_ucm                              false
% 2.96/0.98  --bmc1_add_unsat_core                   none
% 2.96/0.98  --bmc1_unsat_core_children              false
% 2.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.96/0.98  --bmc1_out_stat                         full
% 2.96/0.98  --bmc1_ground_init                      false
% 2.96/0.98  --bmc1_pre_inst_next_state              false
% 2.96/0.98  --bmc1_pre_inst_state                   false
% 2.96/0.98  --bmc1_pre_inst_reach_state             false
% 2.96/0.98  --bmc1_out_unsat_core                   false
% 2.96/0.98  --bmc1_aig_witness_out                  false
% 2.96/0.98  --bmc1_verbose                          false
% 2.96/0.98  --bmc1_dump_clauses_tptp                false
% 2.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.96/0.98  --bmc1_dump_file                        -
% 2.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.96/0.98  --bmc1_ucm_extend_mode                  1
% 2.96/0.98  --bmc1_ucm_init_mode                    2
% 2.96/0.98  --bmc1_ucm_cone_mode                    none
% 2.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.96/0.98  --bmc1_ucm_relax_model                  4
% 2.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.96/0.98  --bmc1_ucm_layered_model                none
% 2.96/0.98  --bmc1_ucm_max_lemma_size               10
% 2.96/0.98  
% 2.96/0.98  ------ AIG Options
% 2.96/0.98  
% 2.96/0.98  --aig_mode                              false
% 2.96/0.98  
% 2.96/0.98  ------ Instantiation Options
% 2.96/0.98  
% 2.96/0.98  --instantiation_flag                    true
% 2.96/0.98  --inst_sos_flag                         false
% 2.96/0.98  --inst_sos_phase                        true
% 2.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.96/0.98  --inst_lit_sel_side                     none
% 2.96/0.98  --inst_solver_per_active                1400
% 2.96/0.98  --inst_solver_calls_frac                1.
% 2.96/0.98  --inst_passive_queue_type               priority_queues
% 2.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.96/0.98  --inst_passive_queues_freq              [25;2]
% 2.96/0.98  --inst_dismatching                      true
% 2.96/0.98  --inst_eager_unprocessed_to_passive     true
% 2.96/0.98  --inst_prop_sim_given                   true
% 2.96/0.98  --inst_prop_sim_new                     false
% 2.96/0.98  --inst_subs_new                         false
% 2.96/0.98  --inst_eq_res_simp                      false
% 2.96/0.98  --inst_subs_given                       false
% 2.96/0.98  --inst_orphan_elimination               true
% 2.96/0.98  --inst_learning_loop_flag               true
% 2.96/0.98  --inst_learning_start                   3000
% 2.96/0.98  --inst_learning_factor                  2
% 2.96/0.98  --inst_start_prop_sim_after_learn       3
% 2.96/0.98  --inst_sel_renew                        solver
% 2.96/0.98  --inst_lit_activity_flag                true
% 2.96/0.98  --inst_restr_to_given                   false
% 2.96/0.98  --inst_activity_threshold               500
% 2.96/0.98  --inst_out_proof                        true
% 2.96/0.98  
% 2.96/0.98  ------ Resolution Options
% 2.96/0.98  
% 2.96/0.98  --resolution_flag                       false
% 2.96/0.98  --res_lit_sel                           adaptive
% 2.96/0.98  --res_lit_sel_side                      none
% 2.96/0.98  --res_ordering                          kbo
% 2.96/0.98  --res_to_prop_solver                    active
% 2.96/0.98  --res_prop_simpl_new                    false
% 2.96/0.98  --res_prop_simpl_given                  true
% 2.96/0.98  --res_passive_queue_type                priority_queues
% 2.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.96/0.98  --res_passive_queues_freq               [15;5]
% 2.96/0.98  --res_forward_subs                      full
% 2.96/0.98  --res_backward_subs                     full
% 2.96/0.98  --res_forward_subs_resolution           true
% 2.96/0.98  --res_backward_subs_resolution          true
% 2.96/0.98  --res_orphan_elimination                true
% 2.96/0.98  --res_time_limit                        2.
% 2.96/0.98  --res_out_proof                         true
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Options
% 2.96/0.98  
% 2.96/0.98  --superposition_flag                    true
% 2.96/0.98  --sup_passive_queue_type                priority_queues
% 2.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.96/0.98  --demod_completeness_check              fast
% 2.96/0.98  --demod_use_ground                      true
% 2.96/0.98  --sup_to_prop_solver                    passive
% 2.96/0.98  --sup_prop_simpl_new                    true
% 2.96/0.98  --sup_prop_simpl_given                  true
% 2.96/0.98  --sup_fun_splitting                     false
% 2.96/0.98  --sup_smt_interval                      50000
% 2.96/0.98  
% 2.96/0.98  ------ Superposition Simplification Setup
% 2.96/0.98  
% 2.96/0.98  --sup_indices_passive                   []
% 2.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_full_bw                           [BwDemod]
% 2.96/0.98  --sup_immed_triv                        [TrivRules]
% 2.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_immed_bw_main                     []
% 2.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.96/0.98  
% 2.96/0.98  ------ Combination Options
% 2.96/0.98  
% 2.96/0.98  --comb_res_mult                         3
% 2.96/0.98  --comb_sup_mult                         2
% 2.96/0.98  --comb_inst_mult                        10
% 2.96/0.98  
% 2.96/0.98  ------ Debug Options
% 2.96/0.98  
% 2.96/0.98  --dbg_backtrace                         false
% 2.96/0.98  --dbg_dump_prop_clauses                 false
% 2.96/0.98  --dbg_dump_prop_clauses_file            -
% 2.96/0.98  --dbg_out_stat                          false
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  ------ Proving...
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  % SZS status Theorem for theBenchmark.p
% 2.96/0.98  
% 2.96/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.96/0.98  
% 2.96/0.98  fof(f15,conjecture,(
% 2.96/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f16,negated_conjecture,(
% 2.96/0.98    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.96/0.98    inference(negated_conjecture,[],[f15])).
% 2.96/0.98  
% 2.96/0.98  fof(f36,plain,(
% 2.96/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.96/0.98    inference(ennf_transformation,[],[f16])).
% 2.96/0.98  
% 2.96/0.98  fof(f37,plain,(
% 2.96/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.96/0.98    inference(flattening,[],[f36])).
% 2.96/0.98  
% 2.96/0.98  fof(f43,plain,(
% 2.96/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f42,plain,(
% 2.96/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f41,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f40,plain,(
% 2.96/0.98    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.96/0.98    introduced(choice_axiom,[])).
% 2.96/0.98  
% 2.96/0.98  fof(f44,plain,(
% 2.96/0.98    (((k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f43,f42,f41,f40])).
% 2.96/0.98  
% 2.96/0.98  fof(f74,plain,(
% 2.96/0.98    m1_subset_1(sK5,sK1)),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f5,axiom,(
% 2.96/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f20,plain,(
% 2.96/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.96/0.98    inference(ennf_transformation,[],[f5])).
% 2.96/0.98  
% 2.96/0.98  fof(f21,plain,(
% 2.96/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.96/0.98    inference(flattening,[],[f20])).
% 2.96/0.98  
% 2.96/0.98  fof(f51,plain,(
% 2.96/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f21])).
% 2.96/0.98  
% 2.96/0.98  fof(f76,plain,(
% 2.96/0.98    k1_xboole_0 != sK1),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f2,axiom,(
% 2.96/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f18,plain,(
% 2.96/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.96/0.98    inference(ennf_transformation,[],[f2])).
% 2.96/0.98  
% 2.96/0.98  fof(f46,plain,(
% 2.96/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f18])).
% 2.96/0.98  
% 2.96/0.98  fof(f73,plain,(
% 2.96/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f9,axiom,(
% 2.96/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f25,plain,(
% 2.96/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.98    inference(ennf_transformation,[],[f9])).
% 2.96/0.98  
% 2.96/0.98  fof(f55,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.96/0.98    inference(cnf_transformation,[],[f25])).
% 2.96/0.98  
% 2.96/0.98  fof(f14,axiom,(
% 2.96/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f34,plain,(
% 2.96/0.98    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.96/0.98    inference(ennf_transformation,[],[f14])).
% 2.96/0.98  
% 2.96/0.98  fof(f35,plain,(
% 2.96/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.96/0.98    inference(flattening,[],[f34])).
% 2.96/0.98  
% 2.96/0.98  fof(f66,plain,(
% 2.96/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f35])).
% 2.96/0.98  
% 2.96/0.98  fof(f75,plain,(
% 2.96/0.98    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f68,plain,(
% 2.96/0.98    ~v1_xboole_0(sK2)),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f69,plain,(
% 2.96/0.98    v1_funct_1(sK3)),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f70,plain,(
% 2.96/0.98    v1_funct_2(sK3,sK1,sK2)),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f71,plain,(
% 2.96/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f1,axiom,(
% 2.96/0.98    v1_xboole_0(k1_xboole_0)),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f45,plain,(
% 2.96/0.98    v1_xboole_0(k1_xboole_0)),
% 2.96/0.98    inference(cnf_transformation,[],[f1])).
% 2.96/0.98  
% 2.96/0.98  fof(f13,axiom,(
% 2.96/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f32,plain,(
% 2.96/0.98    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.96/0.98    inference(ennf_transformation,[],[f13])).
% 2.96/0.98  
% 2.96/0.98  fof(f33,plain,(
% 2.96/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.96/0.98    inference(flattening,[],[f32])).
% 2.96/0.98  
% 2.96/0.98  fof(f61,plain,(
% 2.96/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f33])).
% 2.96/0.98  
% 2.96/0.98  fof(f64,plain,(
% 2.96/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f35])).
% 2.96/0.98  
% 2.96/0.98  fof(f8,axiom,(
% 2.96/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f17,plain,(
% 2.96/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.96/0.98    inference(pure_predicate_removal,[],[f8])).
% 2.96/0.98  
% 2.96/0.98  fof(f24,plain,(
% 2.96/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.98    inference(ennf_transformation,[],[f17])).
% 2.96/0.98  
% 2.96/0.98  fof(f54,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.96/0.98    inference(cnf_transformation,[],[f24])).
% 2.96/0.98  
% 2.96/0.98  fof(f11,axiom,(
% 2.96/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f28,plain,(
% 2.96/0.98    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.96/0.98    inference(ennf_transformation,[],[f11])).
% 2.96/0.98  
% 2.96/0.98  fof(f29,plain,(
% 2.96/0.98    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.96/0.98    inference(flattening,[],[f28])).
% 2.96/0.98  
% 2.96/0.98  fof(f59,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f29])).
% 2.96/0.98  
% 2.96/0.98  fof(f7,axiom,(
% 2.96/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f23,plain,(
% 2.96/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.96/0.98    inference(ennf_transformation,[],[f7])).
% 2.96/0.98  
% 2.96/0.98  fof(f53,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.96/0.98    inference(cnf_transformation,[],[f23])).
% 2.96/0.98  
% 2.96/0.98  fof(f72,plain,(
% 2.96/0.98    v1_funct_1(sK4)),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f12,axiom,(
% 2.96/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f30,plain,(
% 2.96/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.96/0.98    inference(ennf_transformation,[],[f12])).
% 2.96/0.98  
% 2.96/0.98  fof(f31,plain,(
% 2.96/0.98    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.96/0.98    inference(flattening,[],[f30])).
% 2.96/0.98  
% 2.96/0.98  fof(f60,plain,(
% 2.96/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f31])).
% 2.96/0.98  
% 2.96/0.98  fof(f3,axiom,(
% 2.96/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f38,plain,(
% 2.96/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.96/0.98    inference(nnf_transformation,[],[f3])).
% 2.96/0.98  
% 2.96/0.98  fof(f39,plain,(
% 2.96/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.96/0.98    inference(flattening,[],[f38])).
% 2.96/0.98  
% 2.96/0.98  fof(f47,plain,(
% 2.96/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f39])).
% 2.96/0.98  
% 2.96/0.98  fof(f48,plain,(
% 2.96/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.96/0.98    inference(cnf_transformation,[],[f39])).
% 2.96/0.98  
% 2.96/0.98  fof(f79,plain,(
% 2.96/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.96/0.98    inference(equality_resolution,[],[f48])).
% 2.96/0.98  
% 2.96/0.98  fof(f77,plain,(
% 2.96/0.98    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 2.96/0.98    inference(cnf_transformation,[],[f44])).
% 2.96/0.98  
% 2.96/0.98  fof(f49,plain,(
% 2.96/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.96/0.98    inference(cnf_transformation,[],[f39])).
% 2.96/0.98  
% 2.96/0.98  fof(f78,plain,(
% 2.96/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.96/0.98    inference(equality_resolution,[],[f49])).
% 2.96/0.98  
% 2.96/0.98  fof(f10,axiom,(
% 2.96/0.98    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f26,plain,(
% 2.96/0.98    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.96/0.98    inference(ennf_transformation,[],[f10])).
% 2.96/0.98  
% 2.96/0.98  fof(f27,plain,(
% 2.96/0.98    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.96/0.98    inference(flattening,[],[f26])).
% 2.96/0.98  
% 2.96/0.98  fof(f57,plain,(
% 2.96/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f27])).
% 2.96/0.98  
% 2.96/0.98  fof(f6,axiom,(
% 2.96/0.98    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f22,plain,(
% 2.96/0.98    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.96/0.98    inference(ennf_transformation,[],[f6])).
% 2.96/0.98  
% 2.96/0.98  fof(f52,plain,(
% 2.96/0.98    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f22])).
% 2.96/0.98  
% 2.96/0.98  fof(f4,axiom,(
% 2.96/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.96/0.98  
% 2.96/0.98  fof(f19,plain,(
% 2.96/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.96/0.98    inference(ennf_transformation,[],[f4])).
% 2.96/0.98  
% 2.96/0.98  fof(f50,plain,(
% 2.96/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.96/0.98    inference(cnf_transformation,[],[f19])).
% 2.96/0.98  
% 2.96/0.98  cnf(c_26,negated_conjecture,
% 2.96/0.98      ( m1_subset_1(sK5,sK1) ),
% 2.96/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1036,plain,
% 2.96/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_6,plain,
% 2.96/0.98      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 2.96/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1040,plain,
% 2.96/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.96/0.98      | m1_subset_1(X0,X1) != iProver_top
% 2.96/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2986,plain,
% 2.96/0.98      ( r2_hidden(sK5,sK1) = iProver_top
% 2.96/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.96/0.98      inference(superposition,[status(thm)],[c_1036,c_1040]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_39,plain,
% 2.96/0.98      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_24,negated_conjecture,
% 2.96/0.98      ( k1_xboole_0 != sK1 ),
% 2.96/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1,plain,
% 2.96/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.96/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1250,plain,
% 2.96/0.98      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1251,plain,
% 2.96/0.98      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1321,plain,
% 2.96/0.98      ( r2_hidden(X0,sK1) | ~ m1_subset_1(X0,sK1) | v1_xboole_0(sK1) ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1520,plain,
% 2.96/0.98      ( r2_hidden(sK5,sK1) | ~ m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_1321]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1521,plain,
% 2.96/0.98      ( r2_hidden(sK5,sK1) = iProver_top
% 2.96/0.98      | m1_subset_1(sK5,sK1) != iProver_top
% 2.96/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_1520]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_3331,plain,
% 2.96/0.98      ( r2_hidden(sK5,sK1) = iProver_top ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_2986,c_39,c_24,c_1251,c_1521]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_27,negated_conjecture,
% 2.96/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.96/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1035,plain,
% 2.96/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_10,plain,
% 2.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.96/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1038,plain,
% 2.96/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.96/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2108,plain,
% 2.96/0.98      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.96/0.98      inference(superposition,[status(thm)],[c_1035,c_1038]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_18,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k1_xboole_0 = X2 ),
% 2.96/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_25,negated_conjecture,
% 2.96/0.98      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.96/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_435,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_relset_1(sK2,sK0,sK4) != X3
% 2.96/0.98      | k1_xboole_0 = X2 ),
% 2.96/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_436,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relset_1(sK2,sK0,sK4))))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_xboole_0 = X2 ),
% 2.96/0.98      inference(unflattening,[status(thm)],[c_435]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1023,plain,
% 2.96/0.98      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_xboole_0 = X1
% 2.96/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.96/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.96/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.96/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1355,plain,
% 2.96/0.98      ( sK2 = k1_xboole_0
% 2.96/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.96/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top
% 2.96/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.96/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.96/0.98      inference(equality_resolution,[status(thm)],[c_1023]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_32,negated_conjecture,
% 2.96/0.98      ( ~ v1_xboole_0(sK2) ),
% 2.96/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_31,negated_conjecture,
% 2.96/0.98      ( v1_funct_1(sK3) ),
% 2.96/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_34,plain,
% 2.96/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_30,negated_conjecture,
% 2.96/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.96/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_35,plain,
% 2.96/0.98      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_29,negated_conjecture,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.96/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_36,plain,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_0,plain,
% 2.96/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.96/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_632,plain,
% 2.96/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.96/0.98      theory(equality) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1263,plain,
% 2.96/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_632]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1265,plain,
% 2.96/0.98      ( v1_xboole_0(sK2)
% 2.96/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.96/0.98      | sK2 != k1_xboole_0 ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_1263]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1833,plain,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) = iProver_top ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_1355,c_32,c_34,c_35,c_36,c_0,c_1265]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2136,plain,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) = iProver_top ),
% 2.96/0.98      inference(demodulation,[status(thm)],[c_2108,c_1833]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_16,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ r2_hidden(X3,X1)
% 2.96/0.98      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k1_xboole_0 = X2 ),
% 2.96/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1037,plain,
% 2.96/0.98      ( k1_xboole_0 = X0
% 2.96/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 2.96/0.98      | r2_hidden(X3,X2) != iProver_top
% 2.96/0.98      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 2.96/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.96/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_3589,plain,
% 2.96/0.98      ( k1_relat_1(sK4) = k1_xboole_0
% 2.96/0.98      | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) != iProver_top
% 2.96/0.98      | r2_hidden(X0,sK1) != iProver_top
% 2.96/0.98      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.96/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.96/0.98      inference(superposition,[status(thm)],[c_2136,c_1037]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_20,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | v1_funct_2(X0,X1,X3)
% 2.96/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k1_xboole_0 = X2 ),
% 2.96/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_412,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | v1_funct_2(X0,X1,X3)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_relset_1(sK2,sK0,sK4) != X3
% 2.96/0.98      | k1_xboole_0 = X2 ),
% 2.96/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_413,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | v1_funct_2(X0,X1,k1_relset_1(sK2,sK0,sK4))
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_xboole_0 = X2 ),
% 2.96/0.98      inference(unflattening,[status(thm)],[c_412]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1024,plain,
% 2.96/0.98      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_xboole_0 = X1
% 2.96/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.96/0.98      | v1_funct_2(X2,X0,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.96/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.96/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1666,plain,
% 2.96/0.98      ( sK2 = k1_xboole_0
% 2.96/0.98      | v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top
% 2.96/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.96/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.96/0.98      | v1_funct_1(sK3) != iProver_top ),
% 2.96/0.98      inference(equality_resolution,[status(thm)],[c_1024]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1768,plain,
% 2.96/0.98      ( v1_funct_2(sK3,sK1,k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_1666,c_32,c_34,c_35,c_36,c_0,c_1265]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2137,plain,
% 2.96/0.98      ( v1_funct_2(sK3,sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.96/0.98      inference(demodulation,[status(thm)],[c_2108,c_1768]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4308,plain,
% 2.96/0.98      ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top
% 2.96/0.98      | r2_hidden(X0,sK1) != iProver_top
% 2.96/0.98      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_3589,c_34,c_2137]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4309,plain,
% 2.96/0.98      ( k1_relat_1(sK4) = k1_xboole_0
% 2.96/0.98      | r2_hidden(X0,sK1) != iProver_top
% 2.96/0.98      | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) = iProver_top ),
% 2.96/0.98      inference(renaming,[status(thm)],[c_4308]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_9,plain,
% 2.96/0.98      ( v5_relat_1(X0,X1)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.96/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_14,plain,
% 2.96/0.98      ( ~ v5_relat_1(X0,X1)
% 2.96/0.98      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.96/0.98      | ~ v1_relat_1(X0)
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.96/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_307,plain,
% 2.96/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.96/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.96/0.98      | ~ v1_relat_1(X1)
% 2.96/0.98      | ~ v1_funct_1(X1)
% 2.96/0.98      | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
% 2.96/0.98      inference(resolution,[status(thm)],[c_9,c_14]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_8,plain,
% 2.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | v1_relat_1(X0) ),
% 2.96/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_321,plain,
% 2.96/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.96/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.96/0.98      | ~ v1_funct_1(X1)
% 2.96/0.98      | k7_partfun1(X3,X1,X0) = k1_funct_1(X1,X0) ),
% 2.96/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_307,c_8]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1028,plain,
% 2.96/0.98      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 2.96/0.98      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 2.96/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 2.96/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1978,plain,
% 2.96/0.98      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.96/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.96/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.96/0.98      inference(superposition,[status(thm)],[c_1035,c_1028]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_28,negated_conjecture,
% 2.96/0.98      ( v1_funct_1(sK4) ),
% 2.96/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_37,plain,
% 2.96/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2444,plain,
% 2.96/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.96/0.98      | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_1978,c_37]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2445,plain,
% 2.96/0.98      ( k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)
% 2.96/0.98      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.96/0.98      inference(renaming,[status(thm)],[c_2444]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4318,plain,
% 2.96/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.96/0.98      | k1_relat_1(sK4) = k1_xboole_0
% 2.96/0.98      | r2_hidden(X0,sK1) != iProver_top ),
% 2.96/0.98      inference(superposition,[status(thm)],[c_4309,c_2445]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4401,plain,
% 2.96/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.96/0.98      | k1_relat_1(sK4) = k1_xboole_0 ),
% 2.96/0.98      inference(superposition,[status(thm)],[c_3331,c_4318]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_15,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 2.96/0.98      | ~ m1_subset_1(X5,X1)
% 2.96/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_funct_1(X4)
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | v1_xboole_0(X2)
% 2.96/0.98      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 2.96/0.98      | k1_xboole_0 = X1 ),
% 2.96/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_334,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ m1_subset_1(X3,X1)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | ~ v1_funct_1(X4)
% 2.96/0.98      | v1_xboole_0(X2)
% 2.96/0.98      | k2_relset_1(X1,X2,X0) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_relset_1(X2,X5,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.96/0.98      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.96/0.98      | k1_xboole_0 = X1 ),
% 2.96/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1027,plain,
% 2.96/0.98      ( k2_relset_1(X0,X1,X2) != k2_relset_1(sK1,sK2,sK3)
% 2.96/0.98      | k1_relset_1(X1,X3,X4) != k1_relset_1(sK2,sK0,sK4)
% 2.96/0.98      | k1_funct_1(k8_funct_2(X0,X1,X3,X2,X4),X5) = k1_funct_1(X4,k1_funct_1(X2,X5))
% 2.96/0.98      | k1_xboole_0 = X0
% 2.96/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.96/0.98      | m1_subset_1(X5,X0) != iProver_top
% 2.96/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.96/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 2.96/0.98      | v1_funct_1(X2) != iProver_top
% 2.96/0.98      | v1_funct_1(X4) != iProver_top
% 2.96/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1680,plain,
% 2.96/0.98      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.96/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.96/0.98      | sK1 = k1_xboole_0
% 2.96/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.96/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.96/0.98      | m1_subset_1(X2,sK1) != iProver_top
% 2.96/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.96/0.98      | v1_funct_1(X1) != iProver_top
% 2.96/0.98      | v1_funct_1(sK3) != iProver_top
% 2.96/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 2.96/0.98      inference(equality_resolution,[status(thm)],[c_1027]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_33,plain,
% 2.96/0.98      ( v1_xboole_0(sK2) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4,plain,
% 2.96/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.96/0.98      | k1_xboole_0 = X0
% 2.96/0.98      | k1_xboole_0 = X1 ),
% 2.96/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_75,plain,
% 2.96/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.96/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_3,plain,
% 2.96/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.96/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_76,plain,
% 2.96/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_631,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1275,plain,
% 2.96/0.98      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_631]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1276,plain,
% 2.96/0.98      ( sK1 != k1_xboole_0
% 2.96/0.98      | k1_xboole_0 = sK1
% 2.96/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_1275]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1839,plain,
% 2.96/0.98      ( m1_subset_1(X2,sK1) != iProver_top
% 2.96/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.96/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.96/0.98      | k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.96/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_1680,c_33,c_34,c_35,c_36,c_24,c_75,c_76,c_1276]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1840,plain,
% 2.96/0.98      ( k1_relset_1(sK2,X0,X1) != k1_relset_1(sK2,sK0,sK4)
% 2.96/0.98      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 2.96/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 2.96/0.98      | m1_subset_1(X2,sK1) != iProver_top
% 2.96/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.96/0.98      inference(renaming,[status(thm)],[c_1839]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1850,plain,
% 2.96/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.96/0.98      | m1_subset_1(X0,sK1) != iProver_top
% 2.96/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.96/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.96/0.98      inference(equality_resolution,[status(thm)],[c_1840]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_38,plain,
% 2.96/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1964,plain,
% 2.96/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 2.96/0.98      | m1_subset_1(X0,sK1) != iProver_top ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_1850,c_37,c_38]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1972,plain,
% 2.96/0.98      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.96/0.98      inference(superposition,[status(thm)],[c_1036,c_1964]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_23,negated_conjecture,
% 2.96/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.96/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2387,plain,
% 2.96/0.98      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 2.96/0.98      inference(demodulation,[status(thm)],[c_1972,c_23]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4514,plain,
% 2.96/0.98      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_4401,c_2387]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4527,plain,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.96/0.98      inference(demodulation,[status(thm)],[c_4514,c_2136]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_2,plain,
% 2.96/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.96/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_4543,plain,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.96/0.98      inference(demodulation,[status(thm)],[c_4527,c_2]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_12,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_funct_1(X0)
% 2.96/0.98      | ~ v1_xboole_0(X0)
% 2.96/0.98      | v1_xboole_0(X1)
% 2.96/0.98      | v1_xboole_0(X2) ),
% 2.96/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_7,plain,
% 2.96/0.98      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.96/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_153,plain,
% 2.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ v1_xboole_0(X0)
% 2.96/0.98      | v1_xboole_0(X1)
% 2.96/0.98      | v1_xboole_0(X2) ),
% 2.96/0.98      inference(global_propositional_subsumption,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_12,c_7]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_154,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.96/0.98      | ~ v1_xboole_0(X0)
% 2.96/0.98      | v1_xboole_0(X1)
% 2.96/0.98      | v1_xboole_0(X2) ),
% 2.96/0.98      inference(renaming,[status(thm)],[c_153]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1320,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,sK1,X1)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
% 2.96/0.98      | ~ v1_xboole_0(X0)
% 2.96/0.98      | v1_xboole_0(X1)
% 2.96/0.98      | v1_xboole_0(sK1) ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_154]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1704,plain,
% 2.96/0.98      ( ~ v1_funct_2(X0,sK1,sK2)
% 2.96/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.96/0.98      | ~ v1_xboole_0(X0)
% 2.96/0.98      | v1_xboole_0(sK2)
% 2.96/0.98      | v1_xboole_0(sK1) ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_1320]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1783,plain,
% 2.96/0.98      ( ~ v1_funct_2(sK3,sK1,sK2)
% 2.96/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.96/0.98      | v1_xboole_0(sK2)
% 2.96/0.98      | v1_xboole_0(sK1)
% 2.96/0.98      | ~ v1_xboole_0(sK3) ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_1704]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1784,plain,
% 2.96/0.98      ( v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.96/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.96/0.98      | v1_xboole_0(sK2) = iProver_top
% 2.96/0.98      | v1_xboole_0(sK1) = iProver_top
% 2.96/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_5,plain,
% 2.96/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.96/0.98      | ~ v1_xboole_0(X1)
% 2.96/0.98      | v1_xboole_0(X0) ),
% 2.96/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1489,plain,
% 2.96/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 2.96/0.98      | ~ v1_xboole_0(X0)
% 2.96/0.98      | v1_xboole_0(sK3) ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1490,plain,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 2.96/0.98      | v1_xboole_0(X0) != iProver_top
% 2.96/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_1489]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_1492,plain,
% 2.96/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.96/0.98      | v1_xboole_0(sK3) = iProver_top
% 2.96/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.96/0.98      inference(instantiation,[status(thm)],[c_1490]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(c_80,plain,
% 2.96/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.96/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.96/0.98  
% 2.96/0.98  cnf(contradiction,plain,
% 2.96/0.98      ( $false ),
% 2.96/0.98      inference(minisat,
% 2.96/0.98                [status(thm)],
% 2.96/0.98                [c_4543,c_1784,c_1492,c_1251,c_80,c_24,c_36,c_35,c_33]) ).
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.96/0.98  
% 2.96/0.98  ------                               Statistics
% 2.96/0.98  
% 2.96/0.98  ------ General
% 2.96/0.98  
% 2.96/0.98  abstr_ref_over_cycles:                  0
% 2.96/0.98  abstr_ref_under_cycles:                 0
% 2.96/0.98  gc_basic_clause_elim:                   0
% 2.96/0.98  forced_gc_time:                         0
% 2.96/0.98  parsing_time:                           0.013
% 2.96/0.98  unif_index_cands_time:                  0.
% 2.96/0.98  unif_index_add_time:                    0.
% 2.96/0.98  orderings_time:                         0.
% 2.96/0.98  out_proof_time:                         0.012
% 2.96/0.98  total_time:                             0.274
% 2.96/0.98  num_of_symbols:                         54
% 2.96/0.98  num_of_terms:                           8427
% 2.96/0.98  
% 2.96/0.98  ------ Preprocessing
% 2.96/0.98  
% 2.96/0.98  num_of_splits:                          0
% 2.96/0.98  num_of_split_atoms:                     0
% 2.96/0.98  num_of_reused_defs:                     0
% 2.96/0.98  num_eq_ax_congr_red:                    6
% 2.96/0.98  num_of_sem_filtered_clauses:            1
% 2.96/0.98  num_of_subtypes:                        0
% 2.96/0.98  monotx_restored_types:                  0
% 2.96/0.98  sat_num_of_epr_types:                   0
% 2.96/0.98  sat_num_of_non_cyclic_types:            0
% 2.96/0.98  sat_guarded_non_collapsed_types:        0
% 2.96/0.98  num_pure_diseq_elim:                    0
% 2.96/0.98  simp_replaced_by:                       0
% 2.96/0.98  res_preprocessed:                       136
% 2.96/0.98  prep_upred:                             0
% 2.96/0.98  prep_unflattend:                        4
% 2.96/0.98  smt_new_axioms:                         0
% 2.96/0.98  pred_elim_cands:                        5
% 2.96/0.98  pred_elim:                              3
% 2.96/0.98  pred_elim_cl:                           3
% 2.96/0.98  pred_elim_cycles:                       6
% 2.96/0.98  merged_defs:                            0
% 2.96/0.98  merged_defs_ncl:                        0
% 2.96/0.98  bin_hyper_res:                          0
% 2.96/0.98  prep_cycles:                            4
% 2.96/0.98  pred_elim_time:                         0.006
% 2.96/0.98  splitting_time:                         0.
% 2.96/0.98  sem_filter_time:                        0.
% 2.96/0.98  monotx_time:                            0.
% 2.96/0.98  subtype_inf_time:                       0.
% 2.96/0.98  
% 2.96/0.98  ------ Problem properties
% 2.96/0.98  
% 2.96/0.98  clauses:                                26
% 2.96/0.98  conjectures:                            9
% 2.96/0.98  epr:                                    10
% 2.96/0.98  horn:                                   19
% 2.96/0.98  ground:                                 10
% 2.96/0.98  unary:                                  12
% 2.96/0.98  binary:                                 3
% 2.96/0.98  lits:                                   75
% 2.96/0.98  lits_eq:                                21
% 2.96/0.98  fd_pure:                                0
% 2.96/0.98  fd_pseudo:                              0
% 2.96/0.98  fd_cond:                                6
% 2.96/0.98  fd_pseudo_cond:                         0
% 2.96/0.98  ac_symbols:                             0
% 2.96/0.98  
% 2.96/0.98  ------ Propositional Solver
% 2.96/0.98  
% 2.96/0.98  prop_solver_calls:                      27
% 2.96/0.98  prop_fast_solver_calls:                 1101
% 2.96/0.98  smt_solver_calls:                       0
% 2.96/0.98  smt_fast_solver_calls:                  0
% 2.96/0.98  prop_num_of_clauses:                    1817
% 2.96/0.98  prop_preprocess_simplified:             5639
% 2.96/0.98  prop_fo_subsumed:                       34
% 2.96/0.98  prop_solver_time:                       0.
% 2.96/0.98  smt_solver_time:                        0.
% 2.96/0.98  smt_fast_solver_time:                   0.
% 2.96/0.98  prop_fast_solver_time:                  0.
% 2.96/0.98  prop_unsat_core_time:                   0.
% 2.96/0.98  
% 2.96/0.98  ------ QBF
% 2.96/0.98  
% 2.96/0.98  qbf_q_res:                              0
% 2.96/0.98  qbf_num_tautologies:                    0
% 2.96/0.98  qbf_prep_cycles:                        0
% 2.96/0.98  
% 2.96/0.98  ------ BMC1
% 2.96/0.98  
% 2.96/0.98  bmc1_current_bound:                     -1
% 2.96/0.98  bmc1_last_solved_bound:                 -1
% 2.96/0.98  bmc1_unsat_core_size:                   -1
% 2.96/0.98  bmc1_unsat_core_parents_size:           -1
% 2.96/0.98  bmc1_merge_next_fun:                    0
% 2.96/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.96/0.98  
% 2.96/0.98  ------ Instantiation
% 2.96/0.98  
% 2.96/0.98  inst_num_of_clauses:                    686
% 2.96/0.98  inst_num_in_passive:                    30
% 2.96/0.98  inst_num_in_active:                     328
% 2.96/0.98  inst_num_in_unprocessed:                328
% 2.96/0.98  inst_num_of_loops:                      330
% 2.96/0.98  inst_num_of_learning_restarts:          0
% 2.96/0.98  inst_num_moves_active_passive:          0
% 2.96/0.98  inst_lit_activity:                      0
% 2.96/0.98  inst_lit_activity_moves:                0
% 2.96/0.98  inst_num_tautologies:                   0
% 2.96/0.98  inst_num_prop_implied:                  0
% 2.96/0.98  inst_num_existing_simplified:           0
% 2.96/0.98  inst_num_eq_res_simplified:             0
% 2.96/0.98  inst_num_child_elim:                    0
% 2.96/0.98  inst_num_of_dismatching_blockings:      62
% 2.96/0.98  inst_num_of_non_proper_insts:           445
% 2.96/0.98  inst_num_of_duplicates:                 0
% 2.96/0.98  inst_inst_num_from_inst_to_res:         0
% 2.96/0.98  inst_dismatching_checking_time:         0.
% 2.96/0.98  
% 2.96/0.98  ------ Resolution
% 2.96/0.98  
% 2.96/0.98  res_num_of_clauses:                     0
% 2.96/0.98  res_num_in_passive:                     0
% 2.96/0.98  res_num_in_active:                      0
% 2.96/0.98  res_num_of_loops:                       140
% 2.96/0.98  res_forward_subset_subsumed:            41
% 2.96/0.98  res_backward_subset_subsumed:           0
% 2.96/0.98  res_forward_subsumed:                   0
% 2.96/0.98  res_backward_subsumed:                  0
% 2.96/0.98  res_forward_subsumption_resolution:     1
% 2.96/0.98  res_backward_subsumption_resolution:    0
% 2.96/0.98  res_clause_to_clause_subsumption:       147
% 2.96/0.98  res_orphan_elimination:                 0
% 2.96/0.98  res_tautology_del:                      31
% 2.96/0.98  res_num_eq_res_simplified:              0
% 2.96/0.98  res_num_sel_changes:                    0
% 2.96/0.98  res_moves_from_active_to_pass:          0
% 2.96/0.98  
% 2.96/0.98  ------ Superposition
% 2.96/0.98  
% 2.96/0.98  sup_time_total:                         0.
% 2.96/0.98  sup_time_generating:                    0.
% 2.96/0.98  sup_time_sim_full:                      0.
% 2.96/0.98  sup_time_sim_immed:                     0.
% 2.96/0.98  
% 2.96/0.98  sup_num_of_clauses:                     57
% 2.96/0.98  sup_num_in_active:                      40
% 2.96/0.98  sup_num_in_passive:                     17
% 2.96/0.98  sup_num_of_loops:                       64
% 2.96/0.98  sup_fw_superposition:                   34
% 2.96/0.98  sup_bw_superposition:                   10
% 2.96/0.98  sup_immediate_simplified:               11
% 2.96/0.98  sup_given_eliminated:                   0
% 2.96/0.98  comparisons_done:                       0
% 2.96/0.98  comparisons_avoided:                    12
% 2.96/0.98  
% 2.96/0.98  ------ Simplifications
% 2.96/0.98  
% 2.96/0.98  
% 2.96/0.98  sim_fw_subset_subsumed:                 5
% 2.96/0.98  sim_bw_subset_subsumed:                 2
% 2.96/0.98  sim_fw_subsumed:                        1
% 2.96/0.98  sim_bw_subsumed:                        0
% 2.96/0.98  sim_fw_subsumption_res:                 0
% 2.96/0.98  sim_bw_subsumption_res:                 0
% 2.96/0.98  sim_tautology_del:                      1
% 2.96/0.98  sim_eq_tautology_del:                   6
% 2.96/0.98  sim_eq_res_simp:                        0
% 2.96/0.98  sim_fw_demodulated:                     4
% 2.96/0.98  sim_bw_demodulated:                     24
% 2.96/0.98  sim_light_normalised:                   4
% 2.96/0.98  sim_joinable_taut:                      0
% 2.96/0.98  sim_joinable_simp:                      0
% 2.96/0.98  sim_ac_normalised:                      0
% 2.96/0.98  sim_smt_subsumption:                    0
% 2.96/0.98  
%------------------------------------------------------------------------------
