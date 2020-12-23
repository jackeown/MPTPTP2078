%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:48 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 883 expanded)
%              Number of clauses        :  117 ( 241 expanded)
%              Number of leaves         :   22 ( 290 expanded)
%              Depth                    :   20
%              Number of atoms          :  731 (6401 expanded)
%              Number of equality atoms :  334 (1769 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
            ( k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
                ( k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
                  ( k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5)
                  & k1_xboole_0 != sK2
                  & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4))
                  & m1_subset_1(X5,sK2) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X3,sK2,sK3)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f54,f53,f52,f51])).

fof(f95,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f89,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f98,plain,(
    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f44])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2984,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3003,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4980,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2984,c_3003])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2983,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2998,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4343,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2983,c_2998])).

cnf(c_35,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2985,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4474,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4343,c_2985])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2988,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5660,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK5)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4474,c_2988])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_596,plain,
    ( sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_42])).

cnf(c_6920,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK5)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5660,c_44,c_45,c_46,c_596])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2990,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6931,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | v1_funct_2(sK4,sK2,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6920,c_2990])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2986,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4874,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,k1_relat_1(sK5)) = iProver_top
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4474,c_2986])).

cnf(c_9445,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6931,c_44,c_45,c_46,c_596,c_4874])).

cnf(c_9446,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9445])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_15,c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_494,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_14])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_494])).

cnf(c_2976,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_3691,plain,
    ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_2976])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3956,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3691,c_47])).

cnf(c_3957,plain,
    ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3956])).

cnf(c_9455,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | k1_relat_1(sK5) = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9446,c_3957])).

cnf(c_9483,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | k1_relat_1(sK5) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4980,c_9455])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_123,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_124,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2209,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3309,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_3310,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3309])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_2991,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6598,plain,
    ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4343,c_2991])).

cnf(c_43,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7085,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6598,c_43,c_47,c_48])).

cnf(c_7086,plain,
    ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7085])).

cnf(c_7096,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | sK2 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4474,c_7086])).

cnf(c_50,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3422,plain,
    ( ~ v1_funct_2(X0,X1,sK3)
    | ~ r1_tarski(k2_relset_1(X1,sK3,X0),k1_relset_1(sK3,X2,X3))
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(sK3)
    | k1_funct_1(k8_funct_2(X1,sK3,X2,X0,X3),X4) = k1_funct_1(X3,k1_funct_1(X0,X4))
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3562,plain,
    ( ~ v1_funct_2(X0,sK2,sK3)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,X0),k1_relset_1(sK3,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(X3,sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | v1_xboole_0(sK3)
    | k1_funct_1(k8_funct_2(sK2,sK3,X1,X0,X2),X3) = k1_funct_1(X2,k1_funct_1(X0,X3))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3422])).

cnf(c_4116,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ m1_subset_1(X2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK3)
    | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3562])).

cnf(c_5460,plain,
    ( ~ v1_funct_2(sK4,sK2,sK3)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    | ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK3)
    | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_4116])).

cnf(c_5461,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | k1_xboole_0 = sK2
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5460])).

cnf(c_7219,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7096,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_34,c_5461])).

cnf(c_7227,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_2984,c_7219])).

cnf(c_33,negated_conjecture,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_7638,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(demodulation,[status(thm)],[c_7227,c_33])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3005,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2981,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_550,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_12])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_16,c_14,c_12])).

cnf(c_555,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_554])).

cnf(c_2975,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_3415,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_2975])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_364,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_287])).

cnf(c_2977,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_4218,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3415,c_2977])).

cnf(c_4697,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_4218])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2992,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5788,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_2992])).

cnf(c_4344,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2981,c_2998])).

cnf(c_5798,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5788,c_4344])).

cnf(c_5871,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5798,c_45,c_596])).

cnf(c_7797,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4697,c_5871])).

cnf(c_9631,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9483,c_34,c_123,c_124,c_3310,c_7638,c_7797])).

cnf(c_9645,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9631,c_6920])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_9684,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9645,c_2])).

cnf(c_3002,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3877,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3002,c_2975])).

cnf(c_9143,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_3877])).

cnf(c_9153,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5871,c_9143])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6201,plain,
    ( r1_tarski(sK4,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6202,plain,
    ( r1_tarski(sK4,X0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6201])).

cnf(c_6204,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6202])).

cnf(c_3433,plain,
    ( ~ r1_tarski(sK2,X0)
    | ~ r2_hidden(sK0(sK2),sK2)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_3434,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | r2_hidden(sK0(sK2),sK2) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3433])).

cnf(c_3436,plain,
    ( r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(sK2),sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3434])).

cnf(c_3280,plain,
    ( r2_hidden(sK0(sK2),sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3281,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK0(sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3280])).

cnf(c_128,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9684,c_9153,c_6204,c_3436,c_3281,c_128,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.39/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/0.99  
% 3.39/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.39/0.99  
% 3.39/0.99  ------  iProver source info
% 3.39/0.99  
% 3.39/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.39/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.39/0.99  git: non_committed_changes: false
% 3.39/0.99  git: last_make_outside_of_git: false
% 3.39/0.99  
% 3.39/0.99  ------ 
% 3.39/0.99  
% 3.39/0.99  ------ Input Options
% 3.39/0.99  
% 3.39/0.99  --out_options                           all
% 3.39/0.99  --tptp_safe_out                         true
% 3.39/0.99  --problem_path                          ""
% 3.39/0.99  --include_path                          ""
% 3.39/0.99  --clausifier                            res/vclausify_rel
% 3.39/0.99  --clausifier_options                    --mode clausify
% 3.39/0.99  --stdin                                 false
% 3.39/0.99  --stats_out                             all
% 3.39/0.99  
% 3.39/0.99  ------ General Options
% 3.39/0.99  
% 3.39/0.99  --fof                                   false
% 3.39/0.99  --time_out_real                         305.
% 3.39/0.99  --time_out_virtual                      -1.
% 3.39/0.99  --symbol_type_check                     false
% 3.39/0.99  --clausify_out                          false
% 3.39/0.99  --sig_cnt_out                           false
% 3.39/0.99  --trig_cnt_out                          false
% 3.39/0.99  --trig_cnt_out_tolerance                1.
% 3.39/0.99  --trig_cnt_out_sk_spl                   false
% 3.39/0.99  --abstr_cl_out                          false
% 3.39/0.99  
% 3.39/0.99  ------ Global Options
% 3.39/0.99  
% 3.39/0.99  --schedule                              default
% 3.39/0.99  --add_important_lit                     false
% 3.39/0.99  --prop_solver_per_cl                    1000
% 3.39/0.99  --min_unsat_core                        false
% 3.39/0.99  --soft_assumptions                      false
% 3.39/0.99  --soft_lemma_size                       3
% 3.39/0.99  --prop_impl_unit_size                   0
% 3.39/0.99  --prop_impl_unit                        []
% 3.39/0.99  --share_sel_clauses                     true
% 3.39/0.99  --reset_solvers                         false
% 3.39/0.99  --bc_imp_inh                            [conj_cone]
% 3.39/0.99  --conj_cone_tolerance                   3.
% 3.39/0.99  --extra_neg_conj                        none
% 3.39/0.99  --large_theory_mode                     true
% 3.39/0.99  --prolific_symb_bound                   200
% 3.39/0.99  --lt_threshold                          2000
% 3.39/0.99  --clause_weak_htbl                      true
% 3.39/0.99  --gc_record_bc_elim                     false
% 3.39/0.99  
% 3.39/0.99  ------ Preprocessing Options
% 3.39/0.99  
% 3.39/0.99  --preprocessing_flag                    true
% 3.39/0.99  --time_out_prep_mult                    0.1
% 3.39/0.99  --splitting_mode                        input
% 3.39/0.99  --splitting_grd                         true
% 3.39/0.99  --splitting_cvd                         false
% 3.39/0.99  --splitting_cvd_svl                     false
% 3.39/0.99  --splitting_nvd                         32
% 3.39/0.99  --sub_typing                            true
% 3.39/0.99  --prep_gs_sim                           true
% 3.39/0.99  --prep_unflatten                        true
% 3.39/0.99  --prep_res_sim                          true
% 3.39/0.99  --prep_upred                            true
% 3.39/0.99  --prep_sem_filter                       exhaustive
% 3.39/0.99  --prep_sem_filter_out                   false
% 3.39/0.99  --pred_elim                             true
% 3.39/0.99  --res_sim_input                         true
% 3.39/0.99  --eq_ax_congr_red                       true
% 3.39/0.99  --pure_diseq_elim                       true
% 3.39/0.99  --brand_transform                       false
% 3.39/0.99  --non_eq_to_eq                          false
% 3.39/0.99  --prep_def_merge                        true
% 3.39/0.99  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         false
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     num_symb
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       true
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     false
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   []
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_full_bw                           [BwDemod]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  ------ Parsing...
% 3.39/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.39/1.00  ------ Proving...
% 3.39/1.00  ------ Problem Properties 
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  clauses                                 37
% 3.39/1.00  conjectures                             10
% 3.39/1.00  EPR                                     10
% 3.39/1.00  Horn                                    26
% 3.39/1.00  unary                                   14
% 3.39/1.00  binary                                  6
% 3.39/1.00  lits                                    101
% 3.39/1.00  lits eq                                 24
% 3.39/1.00  fd_pure                                 0
% 3.39/1.00  fd_pseudo                               0
% 3.39/1.00  fd_cond                                 9
% 3.39/1.00  fd_pseudo_cond                          0
% 3.39/1.00  AC symbols                              0
% 3.39/1.00  
% 3.39/1.00  ------ Schedule dynamic 5 is on 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ 
% 3.39/1.00  Current options:
% 3.39/1.00  ------ 
% 3.39/1.00  
% 3.39/1.00  ------ Input Options
% 3.39/1.00  
% 3.39/1.00  --out_options                           all
% 3.39/1.00  --tptp_safe_out                         true
% 3.39/1.00  --problem_path                          ""
% 3.39/1.00  --include_path                          ""
% 3.39/1.00  --clausifier                            res/vclausify_rel
% 3.39/1.00  --clausifier_options                    --mode clausify
% 3.39/1.00  --stdin                                 false
% 3.39/1.00  --stats_out                             all
% 3.39/1.00  
% 3.39/1.00  ------ General Options
% 3.39/1.00  
% 3.39/1.00  --fof                                   false
% 3.39/1.00  --time_out_real                         305.
% 3.39/1.00  --time_out_virtual                      -1.
% 3.39/1.00  --symbol_type_check                     false
% 3.39/1.00  --clausify_out                          false
% 3.39/1.00  --sig_cnt_out                           false
% 3.39/1.00  --trig_cnt_out                          false
% 3.39/1.00  --trig_cnt_out_tolerance                1.
% 3.39/1.00  --trig_cnt_out_sk_spl                   false
% 3.39/1.00  --abstr_cl_out                          false
% 3.39/1.00  
% 3.39/1.00  ------ Global Options
% 3.39/1.00  
% 3.39/1.00  --schedule                              default
% 3.39/1.00  --add_important_lit                     false
% 3.39/1.00  --prop_solver_per_cl                    1000
% 3.39/1.00  --min_unsat_core                        false
% 3.39/1.00  --soft_assumptions                      false
% 3.39/1.00  --soft_lemma_size                       3
% 3.39/1.00  --prop_impl_unit_size                   0
% 3.39/1.00  --prop_impl_unit                        []
% 3.39/1.00  --share_sel_clauses                     true
% 3.39/1.00  --reset_solvers                         false
% 3.39/1.00  --bc_imp_inh                            [conj_cone]
% 3.39/1.00  --conj_cone_tolerance                   3.
% 3.39/1.00  --extra_neg_conj                        none
% 3.39/1.00  --large_theory_mode                     true
% 3.39/1.00  --prolific_symb_bound                   200
% 3.39/1.00  --lt_threshold                          2000
% 3.39/1.00  --clause_weak_htbl                      true
% 3.39/1.00  --gc_record_bc_elim                     false
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing Options
% 3.39/1.00  
% 3.39/1.00  --preprocessing_flag                    true
% 3.39/1.00  --time_out_prep_mult                    0.1
% 3.39/1.00  --splitting_mode                        input
% 3.39/1.00  --splitting_grd                         true
% 3.39/1.00  --splitting_cvd                         false
% 3.39/1.00  --splitting_cvd_svl                     false
% 3.39/1.00  --splitting_nvd                         32
% 3.39/1.00  --sub_typing                            true
% 3.39/1.00  --prep_gs_sim                           true
% 3.39/1.00  --prep_unflatten                        true
% 3.39/1.00  --prep_res_sim                          true
% 3.39/1.00  --prep_upred                            true
% 3.39/1.00  --prep_sem_filter                       exhaustive
% 3.39/1.00  --prep_sem_filter_out                   false
% 3.39/1.00  --pred_elim                             true
% 3.39/1.00  --res_sim_input                         true
% 3.39/1.00  --eq_ax_congr_red                       true
% 3.39/1.00  --pure_diseq_elim                       true
% 3.39/1.00  --brand_transform                       false
% 3.39/1.00  --non_eq_to_eq                          false
% 3.39/1.00  --prep_def_merge                        true
% 3.39/1.00  --prep_def_merge_prop_impl              false
% 3.39/1.00  --prep_def_merge_mbd                    true
% 3.39/1.00  --prep_def_merge_tr_red                 false
% 3.39/1.00  --prep_def_merge_tr_cl                  false
% 3.39/1.00  --smt_preprocessing                     true
% 3.39/1.00  --smt_ac_axioms                         fast
% 3.39/1.00  --preprocessed_out                      false
% 3.39/1.00  --preprocessed_stats                    false
% 3.39/1.00  
% 3.39/1.00  ------ Abstraction refinement Options
% 3.39/1.00  
% 3.39/1.00  --abstr_ref                             []
% 3.39/1.00  --abstr_ref_prep                        false
% 3.39/1.00  --abstr_ref_until_sat                   false
% 3.39/1.00  --abstr_ref_sig_restrict                funpre
% 3.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.39/1.00  --abstr_ref_under                       []
% 3.39/1.00  
% 3.39/1.00  ------ SAT Options
% 3.39/1.00  
% 3.39/1.00  --sat_mode                              false
% 3.39/1.00  --sat_fm_restart_options                ""
% 3.39/1.00  --sat_gr_def                            false
% 3.39/1.00  --sat_epr_types                         true
% 3.39/1.00  --sat_non_cyclic_types                  false
% 3.39/1.00  --sat_finite_models                     false
% 3.39/1.00  --sat_fm_lemmas                         false
% 3.39/1.00  --sat_fm_prep                           false
% 3.39/1.00  --sat_fm_uc_incr                        true
% 3.39/1.00  --sat_out_model                         small
% 3.39/1.00  --sat_out_clauses                       false
% 3.39/1.00  
% 3.39/1.00  ------ QBF Options
% 3.39/1.00  
% 3.39/1.00  --qbf_mode                              false
% 3.39/1.00  --qbf_elim_univ                         false
% 3.39/1.00  --qbf_dom_inst                          none
% 3.39/1.00  --qbf_dom_pre_inst                      false
% 3.39/1.00  --qbf_sk_in                             false
% 3.39/1.00  --qbf_pred_elim                         true
% 3.39/1.00  --qbf_split                             512
% 3.39/1.00  
% 3.39/1.00  ------ BMC1 Options
% 3.39/1.00  
% 3.39/1.00  --bmc1_incremental                      false
% 3.39/1.00  --bmc1_axioms                           reachable_all
% 3.39/1.00  --bmc1_min_bound                        0
% 3.39/1.00  --bmc1_max_bound                        -1
% 3.39/1.00  --bmc1_max_bound_default                -1
% 3.39/1.00  --bmc1_symbol_reachability              true
% 3.39/1.00  --bmc1_property_lemmas                  false
% 3.39/1.00  --bmc1_k_induction                      false
% 3.39/1.00  --bmc1_non_equiv_states                 false
% 3.39/1.00  --bmc1_deadlock                         false
% 3.39/1.00  --bmc1_ucm                              false
% 3.39/1.00  --bmc1_add_unsat_core                   none
% 3.39/1.00  --bmc1_unsat_core_children              false
% 3.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.39/1.00  --bmc1_out_stat                         full
% 3.39/1.00  --bmc1_ground_init                      false
% 3.39/1.00  --bmc1_pre_inst_next_state              false
% 3.39/1.00  --bmc1_pre_inst_state                   false
% 3.39/1.00  --bmc1_pre_inst_reach_state             false
% 3.39/1.00  --bmc1_out_unsat_core                   false
% 3.39/1.00  --bmc1_aig_witness_out                  false
% 3.39/1.00  --bmc1_verbose                          false
% 3.39/1.00  --bmc1_dump_clauses_tptp                false
% 3.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.39/1.00  --bmc1_dump_file                        -
% 3.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.39/1.00  --bmc1_ucm_extend_mode                  1
% 3.39/1.00  --bmc1_ucm_init_mode                    2
% 3.39/1.00  --bmc1_ucm_cone_mode                    none
% 3.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.39/1.00  --bmc1_ucm_relax_model                  4
% 3.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.39/1.00  --bmc1_ucm_layered_model                none
% 3.39/1.00  --bmc1_ucm_max_lemma_size               10
% 3.39/1.00  
% 3.39/1.00  ------ AIG Options
% 3.39/1.00  
% 3.39/1.00  --aig_mode                              false
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation Options
% 3.39/1.00  
% 3.39/1.00  --instantiation_flag                    true
% 3.39/1.00  --inst_sos_flag                         false
% 3.39/1.00  --inst_sos_phase                        true
% 3.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.39/1.00  --inst_lit_sel_side                     none
% 3.39/1.00  --inst_solver_per_active                1400
% 3.39/1.00  --inst_solver_calls_frac                1.
% 3.39/1.00  --inst_passive_queue_type               priority_queues
% 3.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.39/1.00  --inst_passive_queues_freq              [25;2]
% 3.39/1.00  --inst_dismatching                      true
% 3.39/1.00  --inst_eager_unprocessed_to_passive     true
% 3.39/1.00  --inst_prop_sim_given                   true
% 3.39/1.00  --inst_prop_sim_new                     false
% 3.39/1.00  --inst_subs_new                         false
% 3.39/1.00  --inst_eq_res_simp                      false
% 3.39/1.00  --inst_subs_given                       false
% 3.39/1.00  --inst_orphan_elimination               true
% 3.39/1.00  --inst_learning_loop_flag               true
% 3.39/1.00  --inst_learning_start                   3000
% 3.39/1.00  --inst_learning_factor                  2
% 3.39/1.00  --inst_start_prop_sim_after_learn       3
% 3.39/1.00  --inst_sel_renew                        solver
% 3.39/1.00  --inst_lit_activity_flag                true
% 3.39/1.00  --inst_restr_to_given                   false
% 3.39/1.00  --inst_activity_threshold               500
% 3.39/1.00  --inst_out_proof                        true
% 3.39/1.00  
% 3.39/1.00  ------ Resolution Options
% 3.39/1.00  
% 3.39/1.00  --resolution_flag                       false
% 3.39/1.00  --res_lit_sel                           adaptive
% 3.39/1.00  --res_lit_sel_side                      none
% 3.39/1.00  --res_ordering                          kbo
% 3.39/1.00  --res_to_prop_solver                    active
% 3.39/1.00  --res_prop_simpl_new                    false
% 3.39/1.00  --res_prop_simpl_given                  true
% 3.39/1.00  --res_passive_queue_type                priority_queues
% 3.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.39/1.00  --res_passive_queues_freq               [15;5]
% 3.39/1.00  --res_forward_subs                      full
% 3.39/1.00  --res_backward_subs                     full
% 3.39/1.00  --res_forward_subs_resolution           true
% 3.39/1.00  --res_backward_subs_resolution          true
% 3.39/1.00  --res_orphan_elimination                true
% 3.39/1.00  --res_time_limit                        2.
% 3.39/1.00  --res_out_proof                         true
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Options
% 3.39/1.00  
% 3.39/1.00  --superposition_flag                    true
% 3.39/1.00  --sup_passive_queue_type                priority_queues
% 3.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.39/1.00  --demod_completeness_check              fast
% 3.39/1.00  --demod_use_ground                      true
% 3.39/1.00  --sup_to_prop_solver                    passive
% 3.39/1.00  --sup_prop_simpl_new                    true
% 3.39/1.00  --sup_prop_simpl_given                  true
% 3.39/1.00  --sup_fun_splitting                     false
% 3.39/1.00  --sup_smt_interval                      50000
% 3.39/1.00  
% 3.39/1.00  ------ Superposition Simplification Setup
% 3.39/1.00  
% 3.39/1.00  --sup_indices_passive                   []
% 3.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_full_bw                           [BwDemod]
% 3.39/1.00  --sup_immed_triv                        [TrivRules]
% 3.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_immed_bw_main                     []
% 3.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.39/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.39/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.39/1.00  
% 3.39/1.00  ------ Combination Options
% 3.39/1.00  
% 3.39/1.00  --comb_res_mult                         3
% 3.39/1.00  --comb_sup_mult                         2
% 3.39/1.00  --comb_inst_mult                        10
% 3.39/1.00  
% 3.39/1.00  ------ Debug Options
% 3.39/1.00  
% 3.39/1.00  --dbg_backtrace                         false
% 3.39/1.00  --dbg_dump_prop_clauses                 false
% 3.39/1.00  --dbg_dump_prop_clauses_file            -
% 3.39/1.00  --dbg_out_stat                          false
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  ------ Proving...
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS status Theorem for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  fof(f19,conjecture,(
% 3.39/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f20,negated_conjecture,(
% 3.39/1.00    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.39/1.00    inference(negated_conjecture,[],[f19])).
% 3.39/1.00  
% 3.39/1.00  fof(f42,plain,(
% 3.39/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.39/1.00    inference(ennf_transformation,[],[f20])).
% 3.39/1.00  
% 3.39/1.00  fof(f43,plain,(
% 3.39/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.39/1.00    inference(flattening,[],[f42])).
% 3.39/1.00  
% 3.39/1.00  fof(f54,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f53,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f52,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f51,plain,(
% 3.39/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f55,plain,(
% 3.39/1.00    (((k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f43,f54,f53,f52,f51])).
% 3.39/1.00  
% 3.39/1.00  fof(f95,plain,(
% 3.39/1.00    m1_subset_1(sK6,sK2)),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f5,axiom,(
% 3.39/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f22,plain,(
% 3.39/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f5])).
% 3.39/1.00  
% 3.39/1.00  fof(f23,plain,(
% 3.39/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.39/1.00    inference(flattening,[],[f22])).
% 3.39/1.00  
% 3.39/1.00  fof(f62,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f23])).
% 3.39/1.00  
% 3.39/1.00  fof(f94,plain,(
% 3.39/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f13,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f31,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f13])).
% 3.39/1.00  
% 3.39/1.00  fof(f73,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f31])).
% 3.39/1.00  
% 3.39/1.00  fof(f96,plain,(
% 3.39/1.00    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f18,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f40,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.39/1.00    inference(ennf_transformation,[],[f18])).
% 3.39/1.00  
% 3.39/1.00  fof(f41,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.39/1.00    inference(flattening,[],[f40])).
% 3.39/1.00  
% 3.39/1.00  fof(f87,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f41])).
% 3.39/1.00  
% 3.39/1.00  fof(f90,plain,(
% 3.39/1.00    v1_funct_1(sK4)),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f91,plain,(
% 3.39/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f92,plain,(
% 3.39/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f1,axiom,(
% 3.39/1.00    v1_xboole_0(k1_xboole_0)),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f56,plain,(
% 3.39/1.00    v1_xboole_0(k1_xboole_0)),
% 3.39/1.00    inference(cnf_transformation,[],[f1])).
% 3.39/1.00  
% 3.39/1.00  fof(f89,plain,(
% 3.39/1.00    ~v1_xboole_0(sK3)),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f17,axiom,(
% 3.39/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f38,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.39/1.00    inference(ennf_transformation,[],[f17])).
% 3.39/1.00  
% 3.39/1.00  fof(f39,plain,(
% 3.39/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.39/1.00    inference(flattening,[],[f38])).
% 3.39/1.00  
% 3.39/1.00  fof(f82,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f39])).
% 3.39/1.00  
% 3.39/1.00  fof(f85,plain,(
% 3.39/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f41])).
% 3.39/1.00  
% 3.39/1.00  fof(f12,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f30,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f12])).
% 3.39/1.00  
% 3.39/1.00  fof(f72,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f30])).
% 3.39/1.00  
% 3.39/1.00  fof(f15,axiom,(
% 3.39/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f34,plain,(
% 3.39/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.39/1.00    inference(ennf_transformation,[],[f15])).
% 3.39/1.00  
% 3.39/1.00  fof(f35,plain,(
% 3.39/1.00    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.39/1.00    inference(flattening,[],[f34])).
% 3.39/1.00  
% 3.39/1.00  fof(f80,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f35])).
% 3.39/1.00  
% 3.39/1.00  fof(f11,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f29,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f11])).
% 3.39/1.00  
% 3.39/1.00  fof(f70,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f29])).
% 3.39/1.00  
% 3.39/1.00  fof(f93,plain,(
% 3.39/1.00    v1_funct_1(sK5)),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f97,plain,(
% 3.39/1.00    k1_xboole_0 != sK2),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f3,axiom,(
% 3.39/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f46,plain,(
% 3.39/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.39/1.00    inference(nnf_transformation,[],[f3])).
% 3.39/1.00  
% 3.39/1.00  fof(f47,plain,(
% 3.39/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.39/1.00    inference(flattening,[],[f46])).
% 3.39/1.00  
% 3.39/1.00  fof(f58,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f59,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f100,plain,(
% 3.39/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.39/1.00    inference(equality_resolution,[],[f59])).
% 3.39/1.00  
% 3.39/1.00  fof(f16,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f36,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.39/1.00    inference(ennf_transformation,[],[f16])).
% 3.39/1.00  
% 3.39/1.00  fof(f37,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.39/1.00    inference(flattening,[],[f36])).
% 3.39/1.00  
% 3.39/1.00  fof(f81,plain,(
% 3.39/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f37])).
% 3.39/1.00  
% 3.39/1.00  fof(f98,plain,(
% 3.39/1.00    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 3.39/1.00    inference(cnf_transformation,[],[f55])).
% 3.39/1.00  
% 3.39/1.00  fof(f2,axiom,(
% 3.39/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f21,plain,(
% 3.39/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.39/1.00    inference(ennf_transformation,[],[f2])).
% 3.39/1.00  
% 3.39/1.00  fof(f44,plain,(
% 3.39/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.39/1.00    introduced(choice_axiom,[])).
% 3.39/1.00  
% 3.39/1.00  fof(f45,plain,(
% 3.39/1.00    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 3.39/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f44])).
% 3.39/1.00  
% 3.39/1.00  fof(f57,plain,(
% 3.39/1.00    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 3.39/1.00    inference(cnf_transformation,[],[f45])).
% 3.39/1.00  
% 3.39/1.00  fof(f71,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f30])).
% 3.39/1.00  
% 3.39/1.00  fof(f9,axiom,(
% 3.39/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f27,plain,(
% 3.39/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f9])).
% 3.39/1.00  
% 3.39/1.00  fof(f49,plain,(
% 3.39/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.39/1.00    inference(nnf_transformation,[],[f27])).
% 3.39/1.00  
% 3.39/1.00  fof(f67,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f49])).
% 3.39/1.00  
% 3.39/1.00  fof(f8,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f26,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.39/1.00    inference(ennf_transformation,[],[f8])).
% 3.39/1.00  
% 3.39/1.00  fof(f66,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f26])).
% 3.39/1.00  
% 3.39/1.00  fof(f6,axiom,(
% 3.39/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f48,plain,(
% 3.39/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.39/1.00    inference(nnf_transformation,[],[f6])).
% 3.39/1.00  
% 3.39/1.00  fof(f64,plain,(
% 3.39/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.39/1.00    inference(cnf_transformation,[],[f48])).
% 3.39/1.00  
% 3.39/1.00  fof(f14,axiom,(
% 3.39/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.39/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.39/1.00  
% 3.39/1.00  fof(f32,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(ennf_transformation,[],[f14])).
% 3.39/1.00  
% 3.39/1.00  fof(f33,plain,(
% 3.39/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(flattening,[],[f32])).
% 3.39/1.00  
% 3.39/1.00  fof(f50,plain,(
% 3.39/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.39/1.00    inference(nnf_transformation,[],[f33])).
% 3.39/1.00  
% 3.39/1.00  fof(f74,plain,(
% 3.39/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f50])).
% 3.39/1.00  
% 3.39/1.00  fof(f60,plain,(
% 3.39/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.39/1.00    inference(cnf_transformation,[],[f47])).
% 3.39/1.00  
% 3.39/1.00  fof(f99,plain,(
% 3.39/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.39/1.00    inference(equality_resolution,[],[f60])).
% 3.39/1.00  
% 3.39/1.00  fof(f63,plain,(
% 3.39/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.39/1.00    inference(cnf_transformation,[],[f48])).
% 3.39/1.00  
% 3.39/1.00  cnf(c_36,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK6,sK2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2984,plain,
% 3.39/1.00      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3003,plain,
% 3.39/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.39/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.39/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4980,plain,
% 3.39/1.00      ( r2_hidden(sK6,sK2) = iProver_top
% 3.39/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2984,c_3003]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_37,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2983,plain,
% 3.39/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_17,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2998,plain,
% 3.39/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4343,plain,
% 3.39/1.00      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2983,c_2998]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_35,negated_conjecture,
% 3.39/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2985,plain,
% 3.39/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4474,plain,
% 3.39/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_4343,c_2985]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_28,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2988,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.39/1.00      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5660,plain,
% 3.39/1.00      ( sK3 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK5)))) = iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_4474,c_2988]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_41,negated_conjecture,
% 3.39/1.00      ( v1_funct_1(sK4) ),
% 3.39/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_44,plain,
% 3.39/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_40,negated_conjecture,
% 3.39/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_45,plain,
% 3.39/1.00      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_39,negated_conjecture,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_46,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_0,plain,
% 3.39/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_42,negated_conjecture,
% 3.39/1.00      ( ~ v1_xboole_0(sK3) ),
% 3.39/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_596,plain,
% 3.39/1.00      ( sK3 != k1_xboole_0 ),
% 3.39/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_42]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6920,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK5)))) = iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5660,c_44,c_45,c_46,c_596]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_26,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ r2_hidden(X3,X1)
% 3.39/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2990,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.39/1.00      | r2_hidden(X3,X2) != iProver_top
% 3.39/1.00      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6931,plain,
% 3.39/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK4,sK2,k1_relat_1(sK5)) != iProver_top
% 3.39/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.39/1.00      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
% 3.39/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_6920,c_2990]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_30,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | v1_funct_2(X0,X1,X3)
% 3.39/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2986,plain,
% 3.39/1.00      ( k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.39/1.00      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.39/1.00      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4874,plain,
% 3.39/1.00      ( sK3 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK4,sK2,k1_relat_1(sK5)) = iProver_top
% 3.39/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_4474,c_2986]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9445,plain,
% 3.39/1.00      ( r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top
% 3.39/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.39/1.00      | k1_relat_1(sK5) = k1_xboole_0 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_6931,c_44,c_45,c_46,c_596,c_4874]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9446,plain,
% 3.39/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 3.39/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.39/1.00      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_9445]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_15,plain,
% 3.39/1.00      ( v5_relat_1(X0,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_24,plain,
% 3.39/1.00      ( ~ v5_relat_1(X0,X1)
% 3.39/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_relat_1(X0)
% 3.39/1.00      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.39/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_490,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_relat_1(X0)
% 3.39/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.39/1.00      inference(resolution,[status(thm)],[c_15,c_24]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_14,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | v1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_494,plain,
% 3.39/1.00      ( ~ v1_funct_1(X0)
% 3.39/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_490,c_14]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_495,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_494]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2976,plain,
% 3.39/1.00      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.39/1.00      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3691,plain,
% 3.39/1.00      ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
% 3.39/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.39/1.00      | v1_funct_1(sK5) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2983,c_2976]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_38,negated_conjecture,
% 3.39/1.00      ( v1_funct_1(sK5) ),
% 3.39/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_47,plain,
% 3.39/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3956,plain,
% 3.39/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.39/1.00      | k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_3691,c_47]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3957,plain,
% 3.39/1.00      ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
% 3.39/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_3956]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9455,plain,
% 3.39/1.00      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.39/1.00      | k1_relat_1(sK5) = k1_xboole_0
% 3.39/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_9446,c_3957]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9483,plain,
% 3.39/1.00      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 3.39/1.00      | k1_relat_1(sK5) = k1_xboole_0
% 3.39/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_4980,c_9455]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_34,negated_conjecture,
% 3.39/1.00      ( k1_xboole_0 != sK2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4,plain,
% 3.39/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.39/1.00      | k1_xboole_0 = X0
% 3.39/1.00      | k1_xboole_0 = X1 ),
% 3.39/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_123,plain,
% 3.39/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.39/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3,plain,
% 3.39/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_124,plain,
% 3.39/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2209,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3309,plain,
% 3.39/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_2209]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3310,plain,
% 3.39/1.00      ( sK2 != k1_xboole_0
% 3.39/1.00      | k1_xboole_0 = sK2
% 3.39/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_3309]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_25,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 3.39/1.00      | ~ m1_subset_1(X5,X1)
% 3.39/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ v1_funct_1(X4)
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | v1_xboole_0(X2)
% 3.39/1.00      | k1_funct_1(k8_funct_2(X1,X2,X3,X0,X4),X5) = k1_funct_1(X4,k1_funct_1(X0,X5))
% 3.39/1.00      | k1_xboole_0 = X1 ),
% 3.39/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2991,plain,
% 3.39/1.00      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.39/1.00      | k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.39/1.00      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.39/1.00      | m1_subset_1(X5,X0) != iProver_top
% 3.39/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.39/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.39/1.00      | v1_funct_1(X3) != iProver_top
% 3.39/1.00      | v1_funct_1(X4) != iProver_top
% 3.39/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6598,plain,
% 3.39/1.00      ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
% 3.39/1.00      | k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.39/1.00      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.39/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top
% 3.39/1.00      | v1_funct_1(sK5) != iProver_top
% 3.39/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_4343,c_2991]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_43,plain,
% 3.39/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_48,plain,
% 3.39/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7085,plain,
% 3.39/1.00      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.39/1.00      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.39/1.00      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.39/1.00      | k1_xboole_0 = X0
% 3.39/1.00      | k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
% 3.39/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_6598,c_43,c_47,c_48]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7086,plain,
% 3.39/1.00      ( k1_funct_1(k8_funct_2(X0,sK3,sK1,X1,sK5),X2) = k1_funct_1(sK5,k1_funct_1(X1,X2))
% 3.39/1.00      | k1_xboole_0 = X0
% 3.39/1.00      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.39/1.00      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,X0) != iProver_top
% 3.39/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.39/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_7085]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7096,plain,
% 3.39/1.00      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.39/1.00      | sK2 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.39/1.00      | m1_subset_1(X0,sK2) != iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK4) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_4474,c_7086]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_50,plain,
% 3.39/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3422,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,sK3)
% 3.39/1.00      | ~ r1_tarski(k2_relset_1(X1,sK3,X0),k1_relset_1(sK3,X2,X3))
% 3.39/1.00      | ~ m1_subset_1(X4,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
% 3.39/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X2)))
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X3)
% 3.39/1.00      | v1_xboole_0(sK3)
% 3.39/1.00      | k1_funct_1(k8_funct_2(X1,sK3,X2,X0,X3),X4) = k1_funct_1(X3,k1_funct_1(X0,X4))
% 3.39/1.00      | k1_xboole_0 = X1 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3562,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,sK2,sK3)
% 3.39/1.00      | ~ r1_tarski(k2_relset_1(sK2,sK3,X0),k1_relset_1(sK3,X1,X2))
% 3.39/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.39/1.00      | ~ m1_subset_1(X3,sK2)
% 3.39/1.00      | ~ v1_funct_1(X0)
% 3.39/1.00      | ~ v1_funct_1(X2)
% 3.39/1.00      | v1_xboole_0(sK3)
% 3.39/1.00      | k1_funct_1(k8_funct_2(sK2,sK3,X1,X0,X2),X3) = k1_funct_1(X2,k1_funct_1(X0,X3))
% 3.39/1.00      | k1_xboole_0 = sK2 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_3422]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4116,plain,
% 3.39/1.00      ( ~ v1_funct_2(sK4,sK2,sK3)
% 3.39/1.00      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
% 3.39/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 3.39/1.00      | ~ m1_subset_1(X2,sK2)
% 3.39/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.39/1.00      | ~ v1_funct_1(X1)
% 3.39/1.00      | ~ v1_funct_1(sK4)
% 3.39/1.00      | v1_xboole_0(sK3)
% 3.39/1.00      | k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,X1),X2) = k1_funct_1(X1,k1_funct_1(sK4,X2))
% 3.39/1.00      | k1_xboole_0 = sK2 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_3562]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5460,plain,
% 3.39/1.00      ( ~ v1_funct_2(sK4,sK2,sK3)
% 3.39/1.00      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
% 3.39/1.00      | ~ m1_subset_1(X0,sK2)
% 3.39/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.39/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.39/1.00      | ~ v1_funct_1(sK4)
% 3.39/1.00      | ~ v1_funct_1(sK5)
% 3.39/1.00      | v1_xboole_0(sK3)
% 3.39/1.00      | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.39/1.00      | k1_xboole_0 = sK2 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_4116]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5461,plain,
% 3.39/1.00      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.39/1.00      | k1_xboole_0 = sK2
% 3.39/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 3.39/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) != iProver_top
% 3.39/1.00      | m1_subset_1(X0,sK2) != iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.39/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.39/1.00      | v1_funct_1(sK4) != iProver_top
% 3.39/1.00      | v1_funct_1(sK5) != iProver_top
% 3.39/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_5460]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7219,plain,
% 3.39/1.00      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 3.39/1.00      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_7096,c_43,c_44,c_45,c_46,c_47,c_48,c_50,c_34,c_5461]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7227,plain,
% 3.39/1.00      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2984,c_7219]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_33,negated_conjecture,
% 3.39/1.00      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 3.39/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7638,plain,
% 3.39/1.00      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_7227,c_33]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_1,plain,
% 3.39/1.00      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3005,plain,
% 3.39/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2981,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_16,plain,
% 3.39/1.00      ( v4_relat_1(X0,X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.39/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_12,plain,
% 3.39/1.00      ( ~ v4_relat_1(X0,X1)
% 3.39/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.39/1.00      | ~ v1_relat_1(X0) ),
% 3.39/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_550,plain,
% 3.39/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | ~ v1_relat_1(X0) ),
% 3.39/1.00      inference(resolution,[status(thm)],[c_16,c_12]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_554,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_550,c_16,c_14,c_12]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_555,plain,
% 3.39/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.39/1.00      inference(renaming,[status(thm)],[c_554]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2975,plain,
% 3.39/1.00      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3415,plain,
% 3.39/1.00      ( r1_tarski(k1_relat_1(sK4),sK2) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2981,c_2975]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_10,plain,
% 3.39/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.39/1.00      | ~ r2_hidden(X2,X0)
% 3.39/1.00      | ~ v1_xboole_0(X1) ),
% 3.39/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_287,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.39/1.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_364,plain,
% 3.39/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 3.39/1.00      inference(bin_hyper_res,[status(thm)],[c_10,c_287]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2977,plain,
% 3.39/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.39/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.39/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4218,plain,
% 3.39/1.00      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 3.39/1.00      | v1_xboole_0(sK2) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_3415,c_2977]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4697,plain,
% 3.39/1.00      ( k1_relat_1(sK4) = k1_xboole_0 | v1_xboole_0(sK2) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_3005,c_4218]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_23,plain,
% 3.39/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.39/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.39/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.39/1.00      | k1_xboole_0 = X2 ),
% 3.39/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2992,plain,
% 3.39/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.39/1.00      | k1_xboole_0 = X1
% 3.39/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.39/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5788,plain,
% 3.39/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.39/1.00      | sK3 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2981,c_2992]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_4344,plain,
% 3.39/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_2981,c_2998]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5798,plain,
% 3.39/1.00      ( k1_relat_1(sK4) = sK2
% 3.39/1.00      | sK3 = k1_xboole_0
% 3.39/1.00      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_5788,c_4344]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_5871,plain,
% 3.39/1.00      ( k1_relat_1(sK4) = sK2 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_5798,c_45,c_596]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_7797,plain,
% 3.39/1.00      ( sK2 = k1_xboole_0 | v1_xboole_0(sK2) != iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_4697,c_5871]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9631,plain,
% 3.39/1.00      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 3.39/1.00      inference(global_propositional_subsumption,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_9483,c_34,c_123,c_124,c_3310,c_7638,c_7797]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9645,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_9631,c_6920]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_2,plain,
% 3.39/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.39/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9684,plain,
% 3.39/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.39/1.00      inference(demodulation,[status(thm)],[c_9645,c_2]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3002,plain,
% 3.39/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.39/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3877,plain,
% 3.39/1.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.39/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_3002,c_2975]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9143,plain,
% 3.39/1.00      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.39/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_3,c_3877]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_9153,plain,
% 3.39/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top
% 3.39/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 3.39/1.00      inference(superposition,[status(thm)],[c_5871,c_9143]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_8,plain,
% 3.39/1.00      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.39/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6201,plain,
% 3.39/1.00      ( r1_tarski(sK4,X0) | ~ m1_subset_1(sK4,k1_zfmisc_1(X0)) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6202,plain,
% 3.39/1.00      ( r1_tarski(sK4,X0) = iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_6201]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_6204,plain,
% 3.39/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top
% 3.39/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_6202]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3433,plain,
% 3.39/1.00      ( ~ r1_tarski(sK2,X0)
% 3.39/1.00      | ~ r2_hidden(sK0(sK2),sK2)
% 3.39/1.00      | ~ v1_xboole_0(X0) ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_364]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3434,plain,
% 3.39/1.00      ( r1_tarski(sK2,X0) != iProver_top
% 3.39/1.00      | r2_hidden(sK0(sK2),sK2) != iProver_top
% 3.39/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_3433]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3436,plain,
% 3.39/1.00      ( r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.39/1.00      | r2_hidden(sK0(sK2),sK2) != iProver_top
% 3.39/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_3434]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3280,plain,
% 3.39/1.00      ( r2_hidden(sK0(sK2),sK2) | k1_xboole_0 = sK2 ),
% 3.39/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_3281,plain,
% 3.39/1.00      ( k1_xboole_0 = sK2 | r2_hidden(sK0(sK2),sK2) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_3280]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(c_128,plain,
% 3.39/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.39/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.39/1.00  
% 3.39/1.00  cnf(contradiction,plain,
% 3.39/1.00      ( $false ),
% 3.39/1.00      inference(minisat,
% 3.39/1.00                [status(thm)],
% 3.39/1.00                [c_9684,c_9153,c_6204,c_3436,c_3281,c_128,c_34]) ).
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.39/1.00  
% 3.39/1.00  ------                               Statistics
% 3.39/1.00  
% 3.39/1.00  ------ General
% 3.39/1.00  
% 3.39/1.00  abstr_ref_over_cycles:                  0
% 3.39/1.00  abstr_ref_under_cycles:                 0
% 3.39/1.00  gc_basic_clause_elim:                   0
% 3.39/1.00  forced_gc_time:                         0
% 3.39/1.00  parsing_time:                           0.015
% 3.39/1.00  unif_index_cands_time:                  0.
% 3.39/1.00  unif_index_add_time:                    0.
% 3.39/1.00  orderings_time:                         0.
% 3.39/1.00  out_proof_time:                         0.014
% 3.39/1.00  total_time:                             0.334
% 3.39/1.00  num_of_symbols:                         56
% 3.39/1.00  num_of_terms:                           8993
% 3.39/1.00  
% 3.39/1.00  ------ Preprocessing
% 3.39/1.00  
% 3.39/1.00  num_of_splits:                          0
% 3.39/1.00  num_of_split_atoms:                     0
% 3.39/1.00  num_of_reused_defs:                     0
% 3.39/1.00  num_eq_ax_congr_red:                    11
% 3.39/1.00  num_of_sem_filtered_clauses:            1
% 3.39/1.00  num_of_subtypes:                        0
% 3.39/1.00  monotx_restored_types:                  0
% 3.39/1.00  sat_num_of_epr_types:                   0
% 3.39/1.00  sat_num_of_non_cyclic_types:            0
% 3.39/1.00  sat_guarded_non_collapsed_types:        0
% 3.39/1.00  num_pure_diseq_elim:                    0
% 3.39/1.00  simp_replaced_by:                       0
% 3.39/1.00  res_preprocessed:                       183
% 3.39/1.00  prep_upred:                             0
% 3.39/1.00  prep_unflattend:                        70
% 3.39/1.00  smt_new_axioms:                         0
% 3.39/1.00  pred_elim_cands:                        6
% 3.39/1.00  pred_elim:                              3
% 3.39/1.00  pred_elim_cl:                           4
% 3.39/1.00  pred_elim_cycles:                       8
% 3.39/1.00  merged_defs:                            8
% 3.39/1.00  merged_defs_ncl:                        0
% 3.39/1.00  bin_hyper_res:                          9
% 3.39/1.00  prep_cycles:                            4
% 3.39/1.00  pred_elim_time:                         0.029
% 3.39/1.00  splitting_time:                         0.
% 3.39/1.00  sem_filter_time:                        0.
% 3.39/1.00  monotx_time:                            0.001
% 3.39/1.00  subtype_inf_time:                       0.
% 3.39/1.00  
% 3.39/1.00  ------ Problem properties
% 3.39/1.00  
% 3.39/1.00  clauses:                                37
% 3.39/1.00  conjectures:                            10
% 3.39/1.00  epr:                                    10
% 3.39/1.00  horn:                                   26
% 3.39/1.00  ground:                                 11
% 3.39/1.00  unary:                                  14
% 3.39/1.00  binary:                                 6
% 3.39/1.00  lits:                                   101
% 3.39/1.00  lits_eq:                                24
% 3.39/1.00  fd_pure:                                0
% 3.39/1.00  fd_pseudo:                              0
% 3.39/1.00  fd_cond:                                9
% 3.39/1.00  fd_pseudo_cond:                         0
% 3.39/1.00  ac_symbols:                             0
% 3.39/1.00  
% 3.39/1.00  ------ Propositional Solver
% 3.39/1.00  
% 3.39/1.00  prop_solver_calls:                      28
% 3.39/1.00  prop_fast_solver_calls:                 1693
% 3.39/1.00  smt_solver_calls:                       0
% 3.39/1.00  smt_fast_solver_calls:                  0
% 3.39/1.00  prop_num_of_clauses:                    3021
% 3.39/1.00  prop_preprocess_simplified:             10330
% 3.39/1.00  prop_fo_subsumed:                       44
% 3.39/1.00  prop_solver_time:                       0.
% 3.39/1.00  smt_solver_time:                        0.
% 3.39/1.00  smt_fast_solver_time:                   0.
% 3.39/1.00  prop_fast_solver_time:                  0.
% 3.39/1.00  prop_unsat_core_time:                   0.
% 3.39/1.00  
% 3.39/1.00  ------ QBF
% 3.39/1.00  
% 3.39/1.00  qbf_q_res:                              0
% 3.39/1.00  qbf_num_tautologies:                    0
% 3.39/1.00  qbf_prep_cycles:                        0
% 3.39/1.00  
% 3.39/1.00  ------ BMC1
% 3.39/1.00  
% 3.39/1.00  bmc1_current_bound:                     -1
% 3.39/1.00  bmc1_last_solved_bound:                 -1
% 3.39/1.00  bmc1_unsat_core_size:                   -1
% 3.39/1.00  bmc1_unsat_core_parents_size:           -1
% 3.39/1.00  bmc1_merge_next_fun:                    0
% 3.39/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.39/1.00  
% 3.39/1.00  ------ Instantiation
% 3.39/1.00  
% 3.39/1.00  inst_num_of_clauses:                    1120
% 3.39/1.00  inst_num_in_passive:                    473
% 3.39/1.00  inst_num_in_active:                     457
% 3.39/1.00  inst_num_in_unprocessed:                192
% 3.39/1.00  inst_num_of_loops:                      560
% 3.39/1.00  inst_num_of_learning_restarts:          0
% 3.39/1.00  inst_num_moves_active_passive:          101
% 3.39/1.00  inst_lit_activity:                      0
% 3.39/1.00  inst_lit_activity_moves:                0
% 3.39/1.00  inst_num_tautologies:                   0
% 3.39/1.00  inst_num_prop_implied:                  0
% 3.39/1.00  inst_num_existing_simplified:           0
% 3.39/1.00  inst_num_eq_res_simplified:             0
% 3.39/1.00  inst_num_child_elim:                    0
% 3.39/1.00  inst_num_of_dismatching_blockings:      303
% 3.39/1.00  inst_num_of_non_proper_insts:           821
% 3.39/1.00  inst_num_of_duplicates:                 0
% 3.39/1.00  inst_inst_num_from_inst_to_res:         0
% 3.39/1.00  inst_dismatching_checking_time:         0.
% 3.39/1.00  
% 3.39/1.00  ------ Resolution
% 3.39/1.00  
% 3.39/1.00  res_num_of_clauses:                     0
% 3.39/1.00  res_num_in_passive:                     0
% 3.39/1.00  res_num_in_active:                      0
% 3.39/1.00  res_num_of_loops:                       187
% 3.39/1.00  res_forward_subset_subsumed:            61
% 3.39/1.00  res_backward_subset_subsumed:           4
% 3.39/1.00  res_forward_subsumed:                   0
% 3.39/1.00  res_backward_subsumed:                  0
% 3.39/1.00  res_forward_subsumption_resolution:     0
% 3.39/1.00  res_backward_subsumption_resolution:    0
% 3.39/1.00  res_clause_to_clause_subsumption:       595
% 3.39/1.00  res_orphan_elimination:                 0
% 3.39/1.00  res_tautology_del:                      141
% 3.39/1.00  res_num_eq_res_simplified:              0
% 3.39/1.00  res_num_sel_changes:                    0
% 3.39/1.00  res_moves_from_active_to_pass:          0
% 3.39/1.00  
% 3.39/1.00  ------ Superposition
% 3.39/1.00  
% 3.39/1.00  sup_time_total:                         0.
% 3.39/1.00  sup_time_generating:                    0.
% 3.39/1.00  sup_time_sim_full:                      0.
% 3.39/1.00  sup_time_sim_immed:                     0.
% 3.39/1.00  
% 3.39/1.00  sup_num_of_clauses:                     121
% 3.39/1.00  sup_num_in_active:                      74
% 3.39/1.00  sup_num_in_passive:                     47
% 3.39/1.00  sup_num_of_loops:                       110
% 3.39/1.00  sup_fw_superposition:                   90
% 3.39/1.00  sup_bw_superposition:                   46
% 3.39/1.00  sup_immediate_simplified:               26
% 3.39/1.00  sup_given_eliminated:                   1
% 3.39/1.00  comparisons_done:                       0
% 3.39/1.00  comparisons_avoided:                    14
% 3.39/1.00  
% 3.39/1.00  ------ Simplifications
% 3.39/1.00  
% 3.39/1.00  
% 3.39/1.00  sim_fw_subset_subsumed:                 9
% 3.39/1.00  sim_bw_subset_subsumed:                 2
% 3.39/1.00  sim_fw_subsumed:                        13
% 3.39/1.00  sim_bw_subsumed:                        0
% 3.39/1.00  sim_fw_subsumption_res:                 1
% 3.39/1.00  sim_bw_subsumption_res:                 0
% 3.39/1.00  sim_tautology_del:                      3
% 3.39/1.00  sim_eq_tautology_del:                   10
% 3.39/1.00  sim_eq_res_simp:                        0
% 3.39/1.00  sim_fw_demodulated:                     11
% 3.39/1.00  sim_bw_demodulated:                     34
% 3.39/1.00  sim_light_normalised:                   10
% 3.39/1.00  sim_joinable_taut:                      0
% 3.39/1.00  sim_joinable_simp:                      0
% 3.39/1.00  sim_ac_normalised:                      0
% 3.39/1.00  sim_smt_subsumption:                    0
% 3.39/1.00  
%------------------------------------------------------------------------------
