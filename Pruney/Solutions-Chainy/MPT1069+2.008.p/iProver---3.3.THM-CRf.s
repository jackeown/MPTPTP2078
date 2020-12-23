%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:43 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 805 expanded)
%              Number of clauses        :  122 ( 225 expanded)
%              Number of leaves         :   26 ( 266 expanded)
%              Depth                    :   22
%              Number of atoms          :  729 (5789 expanded)
%              Number of equality atoms :  312 (1598 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,conjecture,(
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

fof(f31,negated_conjecture,(
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
    inference(negated_conjecture,[],[f30])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK9,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK7,X1,X2)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
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
                  ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK5
                  & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                  & m1_subset_1(X5,sK5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    & k1_xboole_0 != sK5
    & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f66,f88,f87,f86,f85])).

fof(f145,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f89])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f146,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f89])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f148,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f89])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f96,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f147,plain,(
    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f89])).

fof(f143,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f89])).

fof(f29,axiom,(
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

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f140,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f89])).

fof(f141,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

fof(f142,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f89])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f61])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f55])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f144,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f89])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f26,axiom,(
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

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

fof(f126,plain,(
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
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f79])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f153,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f149,plain,(
    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f89])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f67])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f68,f69])).

fof(f91,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f71])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f72,f73])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f24,axiom,(
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

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f114,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f103])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_2456,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_28,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2473,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6280,plain,
    ( v5_relat_1(sK8,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_2473])).

cnf(c_53,negated_conjecture,
    ( m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_2457,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2485,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7976,plain,
    ( r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2457,c_2485])).

cnf(c_66,plain,
    ( m1_subset_1(sK9,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_51,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f148])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2880,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2881,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2880])).

cnf(c_3075,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3510,plain,
    ( ~ m1_subset_1(sK9,sK5)
    | r2_hidden(sK9,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3075])).

cnf(c_3511,plain,
    ( m1_subset_1(sK9,sK5) != iProver_top
    | r2_hidden(sK9,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3510])).

cnf(c_8194,plain,
    ( r2_hidden(sK9,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7976,c_66,c_51,c_2881,c_3511])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2471,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7314,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_2456,c_2471])).

cnf(c_52,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_2458,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_56,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2454,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_45,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2461,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_4237,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_2461])).

cnf(c_59,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_58,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_61,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_62,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1631,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2914,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_2916,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2914])).

cnf(c_4533,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4237,c_59,c_61,c_62,c_5,c_2916])).

cnf(c_4534,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4533])).

cnf(c_4542,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relset_1(sK6,sK4,sK8)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2458,c_4534])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2463,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_5125,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_xboole_0
    | v1_funct_2(sK7,sK5,k1_relset_1(sK6,sK4,sK8)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4542,c_2463])).

cnf(c_47,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_2459,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3446,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,X0) = iProver_top
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_2459])).

cnf(c_3803,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
    | v1_funct_2(sK7,sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3446,c_59,c_61,c_62,c_5,c_2916])).

cnf(c_3804,plain,
    ( v1_funct_2(sK7,sK5,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3803])).

cnf(c_3812,plain,
    ( v1_funct_2(sK7,sK5,k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2458,c_3804])).

cnf(c_5744,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | k1_relset_1(sK6,sK4,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5125,c_61,c_3812])).

cnf(c_5745,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5744])).

cnf(c_7656,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7314,c_5745])).

cnf(c_35,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2469,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12201,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
    | k1_relat_1(sK8) = k1_xboole_0
    | v5_relat_1(sK8,X0) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7656,c_2469])).

cnf(c_55,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_64,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2908,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2909,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2908])).

cnf(c_23628,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
    | k1_relat_1(sK8) = k1_xboole_0
    | v5_relat_1(sK8,X0) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12201,c_64,c_65,c_2909])).

cnf(c_23641,plain,
    ( k7_partfun1(X0,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_relat_1(sK8) = k1_xboole_0
    | v5_relat_1(sK8,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8194,c_23628])).

cnf(c_23704,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_relat_1(sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6280,c_23641])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2470,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7183,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2454,c_2470])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2468,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_9720,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7183,c_2468])).

cnf(c_60,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_63,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_150,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f153])).

cnf(c_151,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1630,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2964,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_2965,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_13920,plain,
    ( m1_subset_1(X2,sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9720,c_60,c_61,c_62,c_63,c_51,c_150,c_151,c_2965])).

cnf(c_13921,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
    | m1_subset_1(X2,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13920])).

cnf(c_13932,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
    | m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7314,c_13921])).

cnf(c_7503,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7183,c_2458])).

cnf(c_7784,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7503,c_7314])).

cnf(c_14006,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13932,c_64,c_65,c_7784])).

cnf(c_14007,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_14006])).

cnf(c_14014,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(superposition,[status(thm)],[c_2457,c_14007])).

cnf(c_50,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_14016,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    inference(demodulation,[status(thm)],[c_14014,c_50])).

cnf(c_23831,plain,
    ( k1_relat_1(sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23704,c_14016])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2497,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2493,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8996,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7784,c_2493])).

cnf(c_14560,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7)),k1_relat_1(sK8)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2497,c_8996])).

cnf(c_165,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_24,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33,c_24])).

cnf(c_304,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_303])).

cnf(c_2450,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_2994,plain,
    ( v1_funct_2(sK7,sK5,sK6) != iProver_top
    | v1_xboole_0(sK7) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2454,c_2450])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2494,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2496,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5272,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2494,c_2496])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f152])).

cnf(c_7499,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK7),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7183,c_4534])).

cnf(c_9410,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK7),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_7499])).

cnf(c_14765,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5272,c_9410])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_2472])).

cnf(c_18496,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_14765,c_9021])).

cnf(c_18553,plain,
    ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18496])).

cnf(c_18721,plain,
    ( r2_hidden(sK0(k2_relat_1(sK7)),k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14560,c_60,c_62,c_51,c_165,c_2881,c_2994,c_18553])).

cnf(c_18726,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18721,c_2496])).

cnf(c_23838,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23831,c_18726])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23838,c_165])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.42/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.42/1.51  
% 6.42/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.42/1.51  
% 6.42/1.51  ------  iProver source info
% 6.42/1.51  
% 6.42/1.51  git: date: 2020-06-30 10:37:57 +0100
% 6.42/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.42/1.51  git: non_committed_changes: false
% 6.42/1.51  git: last_make_outside_of_git: false
% 6.42/1.51  
% 6.42/1.51  ------ 
% 6.42/1.51  
% 6.42/1.51  ------ Input Options
% 6.42/1.51  
% 6.42/1.51  --out_options                           all
% 6.42/1.51  --tptp_safe_out                         true
% 6.42/1.51  --problem_path                          ""
% 6.42/1.51  --include_path                          ""
% 6.42/1.51  --clausifier                            res/vclausify_rel
% 6.42/1.51  --clausifier_options                    --mode clausify
% 6.42/1.51  --stdin                                 false
% 6.42/1.51  --stats_out                             all
% 6.42/1.51  
% 6.42/1.51  ------ General Options
% 6.42/1.51  
% 6.42/1.51  --fof                                   false
% 6.42/1.51  --time_out_real                         305.
% 6.42/1.51  --time_out_virtual                      -1.
% 6.42/1.51  --symbol_type_check                     false
% 6.42/1.51  --clausify_out                          false
% 6.42/1.51  --sig_cnt_out                           false
% 6.42/1.51  --trig_cnt_out                          false
% 6.42/1.51  --trig_cnt_out_tolerance                1.
% 6.42/1.51  --trig_cnt_out_sk_spl                   false
% 6.42/1.51  --abstr_cl_out                          false
% 6.42/1.51  
% 6.42/1.51  ------ Global Options
% 6.42/1.51  
% 6.42/1.51  --schedule                              default
% 6.42/1.51  --add_important_lit                     false
% 6.42/1.51  --prop_solver_per_cl                    1000
% 6.42/1.51  --min_unsat_core                        false
% 6.42/1.51  --soft_assumptions                      false
% 6.42/1.51  --soft_lemma_size                       3
% 6.42/1.51  --prop_impl_unit_size                   0
% 6.42/1.51  --prop_impl_unit                        []
% 6.42/1.51  --share_sel_clauses                     true
% 6.42/1.51  --reset_solvers                         false
% 6.42/1.51  --bc_imp_inh                            [conj_cone]
% 6.42/1.51  --conj_cone_tolerance                   3.
% 6.42/1.51  --extra_neg_conj                        none
% 6.42/1.51  --large_theory_mode                     true
% 6.42/1.51  --prolific_symb_bound                   200
% 6.42/1.51  --lt_threshold                          2000
% 6.42/1.51  --clause_weak_htbl                      true
% 6.42/1.51  --gc_record_bc_elim                     false
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing Options
% 6.42/1.51  
% 6.42/1.51  --preprocessing_flag                    true
% 6.42/1.51  --time_out_prep_mult                    0.1
% 6.42/1.51  --splitting_mode                        input
% 6.42/1.51  --splitting_grd                         true
% 6.42/1.51  --splitting_cvd                         false
% 6.42/1.51  --splitting_cvd_svl                     false
% 6.42/1.51  --splitting_nvd                         32
% 6.42/1.51  --sub_typing                            true
% 6.42/1.51  --prep_gs_sim                           true
% 6.42/1.51  --prep_unflatten                        true
% 6.42/1.51  --prep_res_sim                          true
% 6.42/1.51  --prep_upred                            true
% 6.42/1.51  --prep_sem_filter                       exhaustive
% 6.42/1.51  --prep_sem_filter_out                   false
% 6.42/1.51  --pred_elim                             true
% 6.42/1.51  --res_sim_input                         true
% 6.42/1.51  --eq_ax_congr_red                       true
% 6.42/1.51  --pure_diseq_elim                       true
% 6.42/1.51  --brand_transform                       false
% 6.42/1.51  --non_eq_to_eq                          false
% 6.42/1.51  --prep_def_merge                        true
% 6.42/1.51  --prep_def_merge_prop_impl              false
% 6.42/1.51  --prep_def_merge_mbd                    true
% 6.42/1.51  --prep_def_merge_tr_red                 false
% 6.42/1.51  --prep_def_merge_tr_cl                  false
% 6.42/1.51  --smt_preprocessing                     true
% 6.42/1.51  --smt_ac_axioms                         fast
% 6.42/1.51  --preprocessed_out                      false
% 6.42/1.51  --preprocessed_stats                    false
% 6.42/1.51  
% 6.42/1.51  ------ Abstraction refinement Options
% 6.42/1.51  
% 6.42/1.51  --abstr_ref                             []
% 6.42/1.51  --abstr_ref_prep                        false
% 6.42/1.51  --abstr_ref_until_sat                   false
% 6.42/1.51  --abstr_ref_sig_restrict                funpre
% 6.42/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.42/1.51  --abstr_ref_under                       []
% 6.42/1.51  
% 6.42/1.51  ------ SAT Options
% 6.42/1.51  
% 6.42/1.51  --sat_mode                              false
% 6.42/1.51  --sat_fm_restart_options                ""
% 6.42/1.51  --sat_gr_def                            false
% 6.42/1.51  --sat_epr_types                         true
% 6.42/1.51  --sat_non_cyclic_types                  false
% 6.42/1.51  --sat_finite_models                     false
% 6.42/1.51  --sat_fm_lemmas                         false
% 6.42/1.51  --sat_fm_prep                           false
% 6.42/1.51  --sat_fm_uc_incr                        true
% 6.42/1.51  --sat_out_model                         small
% 6.42/1.51  --sat_out_clauses                       false
% 6.42/1.51  
% 6.42/1.51  ------ QBF Options
% 6.42/1.51  
% 6.42/1.51  --qbf_mode                              false
% 6.42/1.51  --qbf_elim_univ                         false
% 6.42/1.51  --qbf_dom_inst                          none
% 6.42/1.51  --qbf_dom_pre_inst                      false
% 6.42/1.51  --qbf_sk_in                             false
% 6.42/1.51  --qbf_pred_elim                         true
% 6.42/1.51  --qbf_split                             512
% 6.42/1.51  
% 6.42/1.51  ------ BMC1 Options
% 6.42/1.51  
% 6.42/1.51  --bmc1_incremental                      false
% 6.42/1.51  --bmc1_axioms                           reachable_all
% 6.42/1.51  --bmc1_min_bound                        0
% 6.42/1.51  --bmc1_max_bound                        -1
% 6.42/1.51  --bmc1_max_bound_default                -1
% 6.42/1.51  --bmc1_symbol_reachability              true
% 6.42/1.51  --bmc1_property_lemmas                  false
% 6.42/1.51  --bmc1_k_induction                      false
% 6.42/1.51  --bmc1_non_equiv_states                 false
% 6.42/1.51  --bmc1_deadlock                         false
% 6.42/1.51  --bmc1_ucm                              false
% 6.42/1.51  --bmc1_add_unsat_core                   none
% 6.42/1.51  --bmc1_unsat_core_children              false
% 6.42/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.42/1.51  --bmc1_out_stat                         full
% 6.42/1.51  --bmc1_ground_init                      false
% 6.42/1.51  --bmc1_pre_inst_next_state              false
% 6.42/1.51  --bmc1_pre_inst_state                   false
% 6.42/1.51  --bmc1_pre_inst_reach_state             false
% 6.42/1.51  --bmc1_out_unsat_core                   false
% 6.42/1.51  --bmc1_aig_witness_out                  false
% 6.42/1.51  --bmc1_verbose                          false
% 6.42/1.51  --bmc1_dump_clauses_tptp                false
% 6.42/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.42/1.51  --bmc1_dump_file                        -
% 6.42/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.42/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.42/1.51  --bmc1_ucm_extend_mode                  1
% 6.42/1.51  --bmc1_ucm_init_mode                    2
% 6.42/1.51  --bmc1_ucm_cone_mode                    none
% 6.42/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.42/1.51  --bmc1_ucm_relax_model                  4
% 6.42/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.42/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.42/1.51  --bmc1_ucm_layered_model                none
% 6.42/1.51  --bmc1_ucm_max_lemma_size               10
% 6.42/1.51  
% 6.42/1.51  ------ AIG Options
% 6.42/1.51  
% 6.42/1.51  --aig_mode                              false
% 6.42/1.51  
% 6.42/1.51  ------ Instantiation Options
% 6.42/1.51  
% 6.42/1.51  --instantiation_flag                    true
% 6.42/1.51  --inst_sos_flag                         false
% 6.42/1.51  --inst_sos_phase                        true
% 6.42/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel_side                     num_symb
% 6.42/1.51  --inst_solver_per_active                1400
% 6.42/1.51  --inst_solver_calls_frac                1.
% 6.42/1.51  --inst_passive_queue_type               priority_queues
% 6.42/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.42/1.51  --inst_passive_queues_freq              [25;2]
% 6.42/1.51  --inst_dismatching                      true
% 6.42/1.51  --inst_eager_unprocessed_to_passive     true
% 6.42/1.51  --inst_prop_sim_given                   true
% 6.42/1.51  --inst_prop_sim_new                     false
% 6.42/1.51  --inst_subs_new                         false
% 6.42/1.51  --inst_eq_res_simp                      false
% 6.42/1.51  --inst_subs_given                       false
% 6.42/1.51  --inst_orphan_elimination               true
% 6.42/1.51  --inst_learning_loop_flag               true
% 6.42/1.51  --inst_learning_start                   3000
% 6.42/1.51  --inst_learning_factor                  2
% 6.42/1.51  --inst_start_prop_sim_after_learn       3
% 6.42/1.51  --inst_sel_renew                        solver
% 6.42/1.51  --inst_lit_activity_flag                true
% 6.42/1.51  --inst_restr_to_given                   false
% 6.42/1.51  --inst_activity_threshold               500
% 6.42/1.51  --inst_out_proof                        true
% 6.42/1.51  
% 6.42/1.51  ------ Resolution Options
% 6.42/1.51  
% 6.42/1.51  --resolution_flag                       true
% 6.42/1.51  --res_lit_sel                           adaptive
% 6.42/1.51  --res_lit_sel_side                      none
% 6.42/1.51  --res_ordering                          kbo
% 6.42/1.51  --res_to_prop_solver                    active
% 6.42/1.51  --res_prop_simpl_new                    false
% 6.42/1.51  --res_prop_simpl_given                  true
% 6.42/1.51  --res_passive_queue_type                priority_queues
% 6.42/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.42/1.51  --res_passive_queues_freq               [15;5]
% 6.42/1.51  --res_forward_subs                      full
% 6.42/1.51  --res_backward_subs                     full
% 6.42/1.51  --res_forward_subs_resolution           true
% 6.42/1.51  --res_backward_subs_resolution          true
% 6.42/1.51  --res_orphan_elimination                true
% 6.42/1.51  --res_time_limit                        2.
% 6.42/1.51  --res_out_proof                         true
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Options
% 6.42/1.51  
% 6.42/1.51  --superposition_flag                    true
% 6.42/1.51  --sup_passive_queue_type                priority_queues
% 6.42/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.42/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.42/1.51  --demod_completeness_check              fast
% 6.42/1.51  --demod_use_ground                      true
% 6.42/1.51  --sup_to_prop_solver                    passive
% 6.42/1.51  --sup_prop_simpl_new                    true
% 6.42/1.51  --sup_prop_simpl_given                  true
% 6.42/1.51  --sup_fun_splitting                     false
% 6.42/1.51  --sup_smt_interval                      50000
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Simplification Setup
% 6.42/1.51  
% 6.42/1.51  --sup_indices_passive                   []
% 6.42/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.42/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_full_bw                           [BwDemod]
% 6.42/1.51  --sup_immed_triv                        [TrivRules]
% 6.42/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.42/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_immed_bw_main                     []
% 6.42/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.42/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.51  
% 6.42/1.51  ------ Combination Options
% 6.42/1.51  
% 6.42/1.51  --comb_res_mult                         3
% 6.42/1.51  --comb_sup_mult                         2
% 6.42/1.51  --comb_inst_mult                        10
% 6.42/1.51  
% 6.42/1.51  ------ Debug Options
% 6.42/1.51  
% 6.42/1.51  --dbg_backtrace                         false
% 6.42/1.51  --dbg_dump_prop_clauses                 false
% 6.42/1.51  --dbg_dump_prop_clauses_file            -
% 6.42/1.51  --dbg_out_stat                          false
% 6.42/1.51  ------ Parsing...
% 6.42/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.42/1.51  ------ Proving...
% 6.42/1.51  ------ Problem Properties 
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  clauses                                 53
% 6.42/1.51  conjectures                             10
% 6.42/1.51  EPR                                     15
% 6.42/1.51  Horn                                    41
% 6.42/1.51  unary                                   17
% 6.42/1.51  binary                                  12
% 6.42/1.51  lits                                    143
% 6.42/1.51  lits eq                                 22
% 6.42/1.51  fd_pure                                 0
% 6.42/1.51  fd_pseudo                               0
% 6.42/1.51  fd_cond                                 7
% 6.42/1.51  fd_pseudo_cond                          1
% 6.42/1.51  AC symbols                              0
% 6.42/1.51  
% 6.42/1.51  ------ Schedule dynamic 5 is on 
% 6.42/1.51  
% 6.42/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  ------ 
% 6.42/1.51  Current options:
% 6.42/1.51  ------ 
% 6.42/1.51  
% 6.42/1.51  ------ Input Options
% 6.42/1.51  
% 6.42/1.51  --out_options                           all
% 6.42/1.51  --tptp_safe_out                         true
% 6.42/1.51  --problem_path                          ""
% 6.42/1.51  --include_path                          ""
% 6.42/1.51  --clausifier                            res/vclausify_rel
% 6.42/1.51  --clausifier_options                    --mode clausify
% 6.42/1.51  --stdin                                 false
% 6.42/1.51  --stats_out                             all
% 6.42/1.51  
% 6.42/1.51  ------ General Options
% 6.42/1.51  
% 6.42/1.51  --fof                                   false
% 6.42/1.51  --time_out_real                         305.
% 6.42/1.51  --time_out_virtual                      -1.
% 6.42/1.51  --symbol_type_check                     false
% 6.42/1.51  --clausify_out                          false
% 6.42/1.51  --sig_cnt_out                           false
% 6.42/1.51  --trig_cnt_out                          false
% 6.42/1.51  --trig_cnt_out_tolerance                1.
% 6.42/1.51  --trig_cnt_out_sk_spl                   false
% 6.42/1.51  --abstr_cl_out                          false
% 6.42/1.51  
% 6.42/1.51  ------ Global Options
% 6.42/1.51  
% 6.42/1.51  --schedule                              default
% 6.42/1.51  --add_important_lit                     false
% 6.42/1.51  --prop_solver_per_cl                    1000
% 6.42/1.51  --min_unsat_core                        false
% 6.42/1.51  --soft_assumptions                      false
% 6.42/1.51  --soft_lemma_size                       3
% 6.42/1.51  --prop_impl_unit_size                   0
% 6.42/1.51  --prop_impl_unit                        []
% 6.42/1.51  --share_sel_clauses                     true
% 6.42/1.51  --reset_solvers                         false
% 6.42/1.51  --bc_imp_inh                            [conj_cone]
% 6.42/1.51  --conj_cone_tolerance                   3.
% 6.42/1.51  --extra_neg_conj                        none
% 6.42/1.51  --large_theory_mode                     true
% 6.42/1.51  --prolific_symb_bound                   200
% 6.42/1.51  --lt_threshold                          2000
% 6.42/1.51  --clause_weak_htbl                      true
% 6.42/1.51  --gc_record_bc_elim                     false
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing Options
% 6.42/1.51  
% 6.42/1.51  --preprocessing_flag                    true
% 6.42/1.51  --time_out_prep_mult                    0.1
% 6.42/1.51  --splitting_mode                        input
% 6.42/1.51  --splitting_grd                         true
% 6.42/1.51  --splitting_cvd                         false
% 6.42/1.51  --splitting_cvd_svl                     false
% 6.42/1.51  --splitting_nvd                         32
% 6.42/1.51  --sub_typing                            true
% 6.42/1.51  --prep_gs_sim                           true
% 6.42/1.51  --prep_unflatten                        true
% 6.42/1.51  --prep_res_sim                          true
% 6.42/1.51  --prep_upred                            true
% 6.42/1.51  --prep_sem_filter                       exhaustive
% 6.42/1.51  --prep_sem_filter_out                   false
% 6.42/1.51  --pred_elim                             true
% 6.42/1.51  --res_sim_input                         true
% 6.42/1.51  --eq_ax_congr_red                       true
% 6.42/1.51  --pure_diseq_elim                       true
% 6.42/1.51  --brand_transform                       false
% 6.42/1.51  --non_eq_to_eq                          false
% 6.42/1.51  --prep_def_merge                        true
% 6.42/1.51  --prep_def_merge_prop_impl              false
% 6.42/1.51  --prep_def_merge_mbd                    true
% 6.42/1.51  --prep_def_merge_tr_red                 false
% 6.42/1.51  --prep_def_merge_tr_cl                  false
% 6.42/1.51  --smt_preprocessing                     true
% 6.42/1.51  --smt_ac_axioms                         fast
% 6.42/1.51  --preprocessed_out                      false
% 6.42/1.51  --preprocessed_stats                    false
% 6.42/1.51  
% 6.42/1.51  ------ Abstraction refinement Options
% 6.42/1.51  
% 6.42/1.51  --abstr_ref                             []
% 6.42/1.51  --abstr_ref_prep                        false
% 6.42/1.51  --abstr_ref_until_sat                   false
% 6.42/1.51  --abstr_ref_sig_restrict                funpre
% 6.42/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.42/1.51  --abstr_ref_under                       []
% 6.42/1.51  
% 6.42/1.51  ------ SAT Options
% 6.42/1.51  
% 6.42/1.51  --sat_mode                              false
% 6.42/1.51  --sat_fm_restart_options                ""
% 6.42/1.51  --sat_gr_def                            false
% 6.42/1.51  --sat_epr_types                         true
% 6.42/1.51  --sat_non_cyclic_types                  false
% 6.42/1.51  --sat_finite_models                     false
% 6.42/1.51  --sat_fm_lemmas                         false
% 6.42/1.51  --sat_fm_prep                           false
% 6.42/1.51  --sat_fm_uc_incr                        true
% 6.42/1.51  --sat_out_model                         small
% 6.42/1.51  --sat_out_clauses                       false
% 6.42/1.51  
% 6.42/1.51  ------ QBF Options
% 6.42/1.51  
% 6.42/1.51  --qbf_mode                              false
% 6.42/1.51  --qbf_elim_univ                         false
% 6.42/1.51  --qbf_dom_inst                          none
% 6.42/1.51  --qbf_dom_pre_inst                      false
% 6.42/1.51  --qbf_sk_in                             false
% 6.42/1.51  --qbf_pred_elim                         true
% 6.42/1.51  --qbf_split                             512
% 6.42/1.51  
% 6.42/1.51  ------ BMC1 Options
% 6.42/1.51  
% 6.42/1.51  --bmc1_incremental                      false
% 6.42/1.51  --bmc1_axioms                           reachable_all
% 6.42/1.51  --bmc1_min_bound                        0
% 6.42/1.51  --bmc1_max_bound                        -1
% 6.42/1.51  --bmc1_max_bound_default                -1
% 6.42/1.51  --bmc1_symbol_reachability              true
% 6.42/1.51  --bmc1_property_lemmas                  false
% 6.42/1.51  --bmc1_k_induction                      false
% 6.42/1.51  --bmc1_non_equiv_states                 false
% 6.42/1.51  --bmc1_deadlock                         false
% 6.42/1.51  --bmc1_ucm                              false
% 6.42/1.51  --bmc1_add_unsat_core                   none
% 6.42/1.51  --bmc1_unsat_core_children              false
% 6.42/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.42/1.51  --bmc1_out_stat                         full
% 6.42/1.51  --bmc1_ground_init                      false
% 6.42/1.51  --bmc1_pre_inst_next_state              false
% 6.42/1.51  --bmc1_pre_inst_state                   false
% 6.42/1.51  --bmc1_pre_inst_reach_state             false
% 6.42/1.51  --bmc1_out_unsat_core                   false
% 6.42/1.51  --bmc1_aig_witness_out                  false
% 6.42/1.51  --bmc1_verbose                          false
% 6.42/1.51  --bmc1_dump_clauses_tptp                false
% 6.42/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.42/1.51  --bmc1_dump_file                        -
% 6.42/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.42/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.42/1.51  --bmc1_ucm_extend_mode                  1
% 6.42/1.51  --bmc1_ucm_init_mode                    2
% 6.42/1.51  --bmc1_ucm_cone_mode                    none
% 6.42/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.42/1.51  --bmc1_ucm_relax_model                  4
% 6.42/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.42/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.42/1.51  --bmc1_ucm_layered_model                none
% 6.42/1.51  --bmc1_ucm_max_lemma_size               10
% 6.42/1.51  
% 6.42/1.51  ------ AIG Options
% 6.42/1.51  
% 6.42/1.51  --aig_mode                              false
% 6.42/1.51  
% 6.42/1.51  ------ Instantiation Options
% 6.42/1.51  
% 6.42/1.51  --instantiation_flag                    true
% 6.42/1.51  --inst_sos_flag                         false
% 6.42/1.51  --inst_sos_phase                        true
% 6.42/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel_side                     none
% 6.42/1.51  --inst_solver_per_active                1400
% 6.42/1.51  --inst_solver_calls_frac                1.
% 6.42/1.51  --inst_passive_queue_type               priority_queues
% 6.42/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.42/1.51  --inst_passive_queues_freq              [25;2]
% 6.42/1.51  --inst_dismatching                      true
% 6.42/1.51  --inst_eager_unprocessed_to_passive     true
% 6.42/1.51  --inst_prop_sim_given                   true
% 6.42/1.51  --inst_prop_sim_new                     false
% 6.42/1.51  --inst_subs_new                         false
% 6.42/1.51  --inst_eq_res_simp                      false
% 6.42/1.51  --inst_subs_given                       false
% 6.42/1.51  --inst_orphan_elimination               true
% 6.42/1.51  --inst_learning_loop_flag               true
% 6.42/1.51  --inst_learning_start                   3000
% 6.42/1.51  --inst_learning_factor                  2
% 6.42/1.51  --inst_start_prop_sim_after_learn       3
% 6.42/1.51  --inst_sel_renew                        solver
% 6.42/1.51  --inst_lit_activity_flag                true
% 6.42/1.51  --inst_restr_to_given                   false
% 6.42/1.51  --inst_activity_threshold               500
% 6.42/1.51  --inst_out_proof                        true
% 6.42/1.51  
% 6.42/1.51  ------ Resolution Options
% 6.42/1.51  
% 6.42/1.51  --resolution_flag                       false
% 6.42/1.51  --res_lit_sel                           adaptive
% 6.42/1.51  --res_lit_sel_side                      none
% 6.42/1.51  --res_ordering                          kbo
% 6.42/1.51  --res_to_prop_solver                    active
% 6.42/1.51  --res_prop_simpl_new                    false
% 6.42/1.51  --res_prop_simpl_given                  true
% 6.42/1.51  --res_passive_queue_type                priority_queues
% 6.42/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.42/1.51  --res_passive_queues_freq               [15;5]
% 6.42/1.51  --res_forward_subs                      full
% 6.42/1.51  --res_backward_subs                     full
% 6.42/1.51  --res_forward_subs_resolution           true
% 6.42/1.51  --res_backward_subs_resolution          true
% 6.42/1.51  --res_orphan_elimination                true
% 6.42/1.51  --res_time_limit                        2.
% 6.42/1.51  --res_out_proof                         true
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Options
% 6.42/1.51  
% 6.42/1.51  --superposition_flag                    true
% 6.42/1.51  --sup_passive_queue_type                priority_queues
% 6.42/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.42/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.42/1.51  --demod_completeness_check              fast
% 6.42/1.51  --demod_use_ground                      true
% 6.42/1.51  --sup_to_prop_solver                    passive
% 6.42/1.51  --sup_prop_simpl_new                    true
% 6.42/1.51  --sup_prop_simpl_given                  true
% 6.42/1.51  --sup_fun_splitting                     false
% 6.42/1.51  --sup_smt_interval                      50000
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Simplification Setup
% 6.42/1.51  
% 6.42/1.51  --sup_indices_passive                   []
% 6.42/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.42/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_full_bw                           [BwDemod]
% 6.42/1.51  --sup_immed_triv                        [TrivRules]
% 6.42/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.42/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.52  --sup_immed_bw_main                     []
% 6.42/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.42/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.52  
% 6.42/1.52  ------ Combination Options
% 6.42/1.52  
% 6.42/1.52  --comb_res_mult                         3
% 6.42/1.52  --comb_sup_mult                         2
% 6.42/1.52  --comb_inst_mult                        10
% 6.42/1.52  
% 6.42/1.52  ------ Debug Options
% 6.42/1.52  
% 6.42/1.52  --dbg_backtrace                         false
% 6.42/1.52  --dbg_dump_prop_clauses                 false
% 6.42/1.52  --dbg_dump_prop_clauses_file            -
% 6.42/1.52  --dbg_out_stat                          false
% 6.42/1.52  
% 6.42/1.52  
% 6.42/1.52  
% 6.42/1.52  
% 6.42/1.52  ------ Proving...
% 6.42/1.52  
% 6.42/1.52  
% 6.42/1.52  % SZS status Theorem for theBenchmark.p
% 6.42/1.52  
% 6.42/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 6.42/1.52  
% 6.42/1.52  fof(f30,conjecture,(
% 6.42/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f31,negated_conjecture,(
% 6.42/1.52    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 6.42/1.52    inference(negated_conjecture,[],[f30])).
% 6.42/1.52  
% 6.42/1.52  fof(f65,plain,(
% 6.42/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 6.42/1.52    inference(ennf_transformation,[],[f31])).
% 6.42/1.52  
% 6.42/1.52  fof(f66,plain,(
% 6.42/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 6.42/1.52    inference(flattening,[],[f65])).
% 6.42/1.52  
% 6.42/1.52  fof(f88,plain,(
% 6.42/1.52    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK9) != k7_partfun1(X0,X4,k1_funct_1(X3,sK9)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK9,X1))) )),
% 6.42/1.52    introduced(choice_axiom,[])).
% 6.42/1.52  
% 6.42/1.52  fof(f87,plain,(
% 6.42/1.52    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK8),X5) != k7_partfun1(X0,sK8,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK8)) & m1_subset_1(X5,X1)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK8))) )),
% 6.42/1.52    introduced(choice_axiom,[])).
% 6.42/1.52  
% 6.42/1.52  fof(f86,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK7,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK7),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK7,X1,X2) & v1_funct_1(sK7))) )),
% 6.42/1.52    introduced(choice_axiom,[])).
% 6.42/1.52  
% 6.42/1.52  fof(f85,plain,(
% 6.42/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 6.42/1.52    introduced(choice_axiom,[])).
% 6.42/1.52  
% 6.42/1.52  fof(f89,plain,(
% 6.42/1.52    (((k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)),
% 6.42/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f66,f88,f87,f86,f85])).
% 6.42/1.52  
% 6.42/1.52  fof(f145,plain,(
% 6.42/1.52    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f20,axiom,(
% 6.42/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f32,plain,(
% 6.42/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 6.42/1.52    inference(pure_predicate_removal,[],[f20])).
% 6.42/1.52  
% 6.42/1.52  fof(f49,plain,(
% 6.42/1.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.42/1.52    inference(ennf_transformation,[],[f32])).
% 6.42/1.52  
% 6.42/1.52  fof(f118,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.42/1.52    inference(cnf_transformation,[],[f49])).
% 6.42/1.52  
% 6.42/1.52  fof(f146,plain,(
% 6.42/1.52    m1_subset_1(sK9,sK5)),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f10,axiom,(
% 6.42/1.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f36,plain,(
% 6.42/1.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 6.42/1.52    inference(ennf_transformation,[],[f10])).
% 6.42/1.52  
% 6.42/1.52  fof(f37,plain,(
% 6.42/1.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 6.42/1.52    inference(flattening,[],[f36])).
% 6.42/1.52  
% 6.42/1.52  fof(f106,plain,(
% 6.42/1.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f37])).
% 6.42/1.52  
% 6.42/1.52  fof(f148,plain,(
% 6.42/1.52    k1_xboole_0 != sK5),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f4,axiom,(
% 6.42/1.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f34,plain,(
% 6.42/1.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 6.42/1.52    inference(ennf_transformation,[],[f4])).
% 6.42/1.52  
% 6.42/1.52  fof(f96,plain,(
% 6.42/1.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f34])).
% 6.42/1.52  
% 6.42/1.52  fof(f22,axiom,(
% 6.42/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f51,plain,(
% 6.42/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.42/1.52    inference(ennf_transformation,[],[f22])).
% 6.42/1.52  
% 6.42/1.52  fof(f120,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.42/1.52    inference(cnf_transformation,[],[f51])).
% 6.42/1.52  
% 6.42/1.52  fof(f147,plain,(
% 6.42/1.52    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f143,plain,(
% 6.42/1.52    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f29,axiom,(
% 6.42/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f63,plain,(
% 6.42/1.52    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 6.42/1.52    inference(ennf_transformation,[],[f29])).
% 6.42/1.52  
% 6.42/1.52  fof(f64,plain,(
% 6.42/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 6.42/1.52    inference(flattening,[],[f63])).
% 6.42/1.52  
% 6.42/1.52  fof(f138,plain,(
% 6.42/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f64])).
% 6.42/1.52  
% 6.42/1.52  fof(f140,plain,(
% 6.42/1.52    ~v1_xboole_0(sK6)),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f141,plain,(
% 6.42/1.52    v1_funct_1(sK7)),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f142,plain,(
% 6.42/1.52    v1_funct_2(sK7,sK5,sK6)),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f3,axiom,(
% 6.42/1.52    v1_xboole_0(k1_xboole_0)),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f95,plain,(
% 6.42/1.52    v1_xboole_0(k1_xboole_0)),
% 6.42/1.52    inference(cnf_transformation,[],[f3])).
% 6.42/1.52  
% 6.42/1.52  fof(f28,axiom,(
% 6.42/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f61,plain,(
% 6.42/1.52    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 6.42/1.52    inference(ennf_transformation,[],[f28])).
% 6.42/1.52  
% 6.42/1.52  fof(f62,plain,(
% 6.42/1.52    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 6.42/1.52    inference(flattening,[],[f61])).
% 6.42/1.52  
% 6.42/1.52  fof(f133,plain,(
% 6.42/1.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f62])).
% 6.42/1.52  
% 6.42/1.52  fof(f136,plain,(
% 6.42/1.52    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f64])).
% 6.42/1.52  
% 6.42/1.52  fof(f25,axiom,(
% 6.42/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f55,plain,(
% 6.42/1.52    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.42/1.52    inference(ennf_transformation,[],[f25])).
% 6.42/1.52  
% 6.42/1.52  fof(f56,plain,(
% 6.42/1.52    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.42/1.52    inference(flattening,[],[f55])).
% 6.42/1.52  
% 6.42/1.52  fof(f125,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f56])).
% 6.42/1.52  
% 6.42/1.52  fof(f144,plain,(
% 6.42/1.52    v1_funct_1(sK8)),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f19,axiom,(
% 6.42/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f48,plain,(
% 6.42/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.42/1.52    inference(ennf_transformation,[],[f19])).
% 6.42/1.52  
% 6.42/1.52  fof(f117,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.42/1.52    inference(cnf_transformation,[],[f48])).
% 6.42/1.52  
% 6.42/1.52  fof(f23,axiom,(
% 6.42/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f52,plain,(
% 6.42/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.42/1.52    inference(ennf_transformation,[],[f23])).
% 6.42/1.52  
% 6.42/1.52  fof(f121,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.42/1.52    inference(cnf_transformation,[],[f52])).
% 6.42/1.52  
% 6.42/1.52  fof(f26,axiom,(
% 6.42/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f57,plain,(
% 6.42/1.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 6.42/1.52    inference(ennf_transformation,[],[f26])).
% 6.42/1.52  
% 6.42/1.52  fof(f58,plain,(
% 6.42/1.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 6.42/1.52    inference(flattening,[],[f57])).
% 6.42/1.52  
% 6.42/1.52  fof(f126,plain,(
% 6.42/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f58])).
% 6.42/1.52  
% 6.42/1.52  fof(f7,axiom,(
% 6.42/1.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f79,plain,(
% 6.42/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.42/1.52    inference(nnf_transformation,[],[f7])).
% 6.42/1.52  
% 6.42/1.52  fof(f80,plain,(
% 6.42/1.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.42/1.52    inference(flattening,[],[f79])).
% 6.42/1.52  
% 6.42/1.52  fof(f101,plain,(
% 6.42/1.52    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f80])).
% 6.42/1.52  
% 6.42/1.52  fof(f102,plain,(
% 6.42/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 6.42/1.52    inference(cnf_transformation,[],[f80])).
% 6.42/1.52  
% 6.42/1.52  fof(f153,plain,(
% 6.42/1.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 6.42/1.52    inference(equality_resolution,[],[f102])).
% 6.42/1.52  
% 6.42/1.52  fof(f149,plain,(
% 6.42/1.52    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))),
% 6.42/1.52    inference(cnf_transformation,[],[f89])).
% 6.42/1.52  
% 6.42/1.52  fof(f1,axiom,(
% 6.42/1.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f67,plain,(
% 6.42/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.42/1.52    inference(nnf_transformation,[],[f1])).
% 6.42/1.52  
% 6.42/1.52  fof(f68,plain,(
% 6.42/1.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.42/1.52    inference(rectify,[],[f67])).
% 6.42/1.52  
% 6.42/1.52  fof(f69,plain,(
% 6.42/1.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 6.42/1.52    introduced(choice_axiom,[])).
% 6.42/1.52  
% 6.42/1.52  fof(f70,plain,(
% 6.42/1.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.42/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f68,f69])).
% 6.42/1.52  
% 6.42/1.52  fof(f91,plain,(
% 6.42/1.52    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f70])).
% 6.42/1.52  
% 6.42/1.52  fof(f2,axiom,(
% 6.42/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f33,plain,(
% 6.42/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.42/1.52    inference(ennf_transformation,[],[f2])).
% 6.42/1.52  
% 6.42/1.52  fof(f71,plain,(
% 6.42/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.42/1.52    inference(nnf_transformation,[],[f33])).
% 6.42/1.52  
% 6.42/1.52  fof(f72,plain,(
% 6.42/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.42/1.52    inference(rectify,[],[f71])).
% 6.42/1.52  
% 6.42/1.52  fof(f73,plain,(
% 6.42/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 6.42/1.52    introduced(choice_axiom,[])).
% 6.42/1.52  
% 6.42/1.52  fof(f74,plain,(
% 6.42/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.42/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f72,f73])).
% 6.42/1.52  
% 6.42/1.52  fof(f92,plain,(
% 6.42/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f74])).
% 6.42/1.52  
% 6.42/1.52  fof(f24,axiom,(
% 6.42/1.52    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f53,plain,(
% 6.42/1.52    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.42/1.52    inference(ennf_transformation,[],[f24])).
% 6.42/1.52  
% 6.42/1.52  fof(f54,plain,(
% 6.42/1.52    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.42/1.52    inference(flattening,[],[f53])).
% 6.42/1.52  
% 6.42/1.52  fof(f123,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f54])).
% 6.42/1.52  
% 6.42/1.52  fof(f16,axiom,(
% 6.42/1.52    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f44,plain,(
% 6.42/1.52    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 6.42/1.52    inference(ennf_transformation,[],[f16])).
% 6.42/1.52  
% 6.42/1.52  fof(f114,plain,(
% 6.42/1.52    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f44])).
% 6.42/1.52  
% 6.42/1.52  fof(f93,plain,(
% 6.42/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f74])).
% 6.42/1.52  
% 6.42/1.52  fof(f90,plain,(
% 6.42/1.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f70])).
% 6.42/1.52  
% 6.42/1.52  fof(f103,plain,(
% 6.42/1.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 6.42/1.52    inference(cnf_transformation,[],[f80])).
% 6.42/1.52  
% 6.42/1.52  fof(f152,plain,(
% 6.42/1.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.42/1.52    inference(equality_resolution,[],[f103])).
% 6.42/1.52  
% 6.42/1.52  fof(f21,axiom,(
% 6.42/1.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 6.42/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.42/1.52  
% 6.42/1.52  fof(f50,plain,(
% 6.42/1.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 6.42/1.52    inference(ennf_transformation,[],[f21])).
% 6.42/1.52  
% 6.42/1.52  fof(f119,plain,(
% 6.42/1.52    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 6.42/1.52    inference(cnf_transformation,[],[f50])).
% 6.42/1.52  
% 6.42/1.52  cnf(c_54,negated_conjecture,
% 6.42/1.52      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 6.42/1.52      inference(cnf_transformation,[],[f145]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2456,plain,
% 6.42/1.52      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_28,plain,
% 6.42/1.52      ( v5_relat_1(X0,X1)
% 6.42/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 6.42/1.52      inference(cnf_transformation,[],[f118]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2473,plain,
% 6.42/1.52      ( v5_relat_1(X0,X1) = iProver_top
% 6.42/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_6280,plain,
% 6.42/1.52      ( v5_relat_1(sK8,sK4) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2456,c_2473]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_53,negated_conjecture,
% 6.42/1.52      ( m1_subset_1(sK9,sK5) ),
% 6.42/1.52      inference(cnf_transformation,[],[f146]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2457,plain,
% 6.42/1.52      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_16,plain,
% 6.42/1.52      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.42/1.52      inference(cnf_transformation,[],[f106]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2485,plain,
% 6.42/1.52      ( m1_subset_1(X0,X1) != iProver_top
% 6.42/1.52      | r2_hidden(X0,X1) = iProver_top
% 6.42/1.52      | v1_xboole_0(X1) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_7976,plain,
% 6.42/1.52      ( r2_hidden(sK9,sK5) = iProver_top
% 6.42/1.52      | v1_xboole_0(sK5) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2457,c_2485]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_66,plain,
% 6.42/1.52      ( m1_subset_1(sK9,sK5) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_51,negated_conjecture,
% 6.42/1.52      ( k1_xboole_0 != sK5 ),
% 6.42/1.52      inference(cnf_transformation,[],[f148]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_6,plain,
% 6.42/1.52      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 6.42/1.52      inference(cnf_transformation,[],[f96]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2880,plain,
% 6.42/1.52      ( ~ v1_xboole_0(sK5) | k1_xboole_0 = sK5 ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2881,plain,
% 6.42/1.52      ( k1_xboole_0 = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_2880]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3075,plain,
% 6.42/1.52      ( ~ m1_subset_1(X0,sK5) | r2_hidden(X0,sK5) | v1_xboole_0(sK5) ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_16]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3510,plain,
% 6.42/1.52      ( ~ m1_subset_1(sK9,sK5) | r2_hidden(sK9,sK5) | v1_xboole_0(sK5) ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_3075]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3511,plain,
% 6.42/1.52      ( m1_subset_1(sK9,sK5) != iProver_top
% 6.42/1.52      | r2_hidden(sK9,sK5) = iProver_top
% 6.42/1.52      | v1_xboole_0(sK5) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_3510]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_8194,plain,
% 6.42/1.52      ( r2_hidden(sK9,sK5) = iProver_top ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_7976,c_66,c_51,c_2881,c_3511]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_30,plain,
% 6.42/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f120]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2471,plain,
% 6.42/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 6.42/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_7314,plain,
% 6.42/1.52      ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2456,c_2471]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_52,negated_conjecture,
% 6.42/1.52      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
% 6.42/1.52      inference(cnf_transformation,[],[f147]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2458,plain,
% 6.42/1.52      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_56,negated_conjecture,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 6.42/1.52      inference(cnf_transformation,[],[f143]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2454,plain,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_45,plain,
% 6.42/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.42/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 6.42/1.52      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 6.42/1.52      | ~ v1_funct_1(X0)
% 6.42/1.52      | k1_xboole_0 = X2 ),
% 6.42/1.52      inference(cnf_transformation,[],[f138]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2461,plain,
% 6.42/1.52      ( k1_xboole_0 = X0
% 6.42/1.52      | v1_funct_2(X1,X2,X0) != iProver_top
% 6.42/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 6.42/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 6.42/1.52      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 6.42/1.52      | v1_funct_1(X1) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_4237,plain,
% 6.42/1.52      ( sK6 = k1_xboole_0
% 6.42/1.52      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 6.42/1.52      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
% 6.42/1.52      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 6.42/1.52      | v1_funct_1(sK7) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2454,c_2461]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_59,negated_conjecture,
% 6.42/1.52      ( ~ v1_xboole_0(sK6) ),
% 6.42/1.52      inference(cnf_transformation,[],[f140]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_58,negated_conjecture,
% 6.42/1.52      ( v1_funct_1(sK7) ),
% 6.42/1.52      inference(cnf_transformation,[],[f141]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_61,plain,
% 6.42/1.52      ( v1_funct_1(sK7) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_57,negated_conjecture,
% 6.42/1.52      ( v1_funct_2(sK7,sK5,sK6) ),
% 6.42/1.52      inference(cnf_transformation,[],[f142]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_62,plain,
% 6.42/1.52      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_5,plain,
% 6.42/1.52      ( v1_xboole_0(k1_xboole_0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f95]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_1631,plain,
% 6.42/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.42/1.52      theory(equality) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2914,plain,
% 6.42/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_1631]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2916,plain,
% 6.42/1.52      ( v1_xboole_0(sK6)
% 6.42/1.52      | ~ v1_xboole_0(k1_xboole_0)
% 6.42/1.52      | sK6 != k1_xboole_0 ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_2914]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_4533,plain,
% 6.42/1.52      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 6.42/1.52      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_4237,c_59,c_61,c_62,c_5,c_2916]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_4534,plain,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
% 6.42/1.52      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
% 6.42/1.52      inference(renaming,[status(thm)],[c_4533]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_4542,plain,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relset_1(sK6,sK4,sK8)))) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2458,c_4534]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_43,plain,
% 6.42/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.42/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | ~ r2_hidden(X3,X1)
% 6.42/1.52      | r2_hidden(k1_funct_1(X0,X3),X2)
% 6.42/1.52      | ~ v1_funct_1(X0)
% 6.42/1.52      | k1_xboole_0 = X2 ),
% 6.42/1.52      inference(cnf_transformation,[],[f133]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2463,plain,
% 6.42/1.52      ( k1_xboole_0 = X0
% 6.42/1.52      | v1_funct_2(X1,X2,X0) != iProver_top
% 6.42/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 6.42/1.52      | r2_hidden(X3,X2) != iProver_top
% 6.42/1.52      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 6.42/1.52      | v1_funct_1(X1) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_5125,plain,
% 6.42/1.52      ( k1_relset_1(sK6,sK4,sK8) = k1_xboole_0
% 6.42/1.52      | v1_funct_2(sK7,sK5,k1_relset_1(sK6,sK4,sK8)) != iProver_top
% 6.42/1.52      | r2_hidden(X0,sK5) != iProver_top
% 6.42/1.52      | r2_hidden(k1_funct_1(sK7,X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
% 6.42/1.52      | v1_funct_1(sK7) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_4542,c_2463]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_47,plain,
% 6.42/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.42/1.52      | v1_funct_2(X0,X1,X3)
% 6.42/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 6.42/1.52      | ~ v1_funct_1(X0)
% 6.42/1.52      | k1_xboole_0 = X2 ),
% 6.42/1.52      inference(cnf_transformation,[],[f136]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2459,plain,
% 6.42/1.52      ( k1_xboole_0 = X0
% 6.42/1.52      | v1_funct_2(X1,X2,X0) != iProver_top
% 6.42/1.52      | v1_funct_2(X1,X2,X3) = iProver_top
% 6.42/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 6.42/1.52      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 6.42/1.52      | v1_funct_1(X1) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3446,plain,
% 6.42/1.52      ( sK6 = k1_xboole_0
% 6.42/1.52      | v1_funct_2(sK7,sK5,X0) = iProver_top
% 6.42/1.52      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 6.42/1.52      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 6.42/1.52      | v1_funct_1(sK7) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2454,c_2459]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3803,plain,
% 6.42/1.52      ( r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top
% 6.42/1.52      | v1_funct_2(sK7,sK5,X0) = iProver_top ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_3446,c_59,c_61,c_62,c_5,c_2916]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3804,plain,
% 6.42/1.52      ( v1_funct_2(sK7,sK5,X0) = iProver_top
% 6.42/1.52      | r1_tarski(k2_relset_1(sK5,sK6,sK7),X0) != iProver_top ),
% 6.42/1.52      inference(renaming,[status(thm)],[c_3803]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3812,plain,
% 6.42/1.52      ( v1_funct_2(sK7,sK5,k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2458,c_3804]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_5744,plain,
% 6.42/1.52      ( r2_hidden(k1_funct_1(sK7,X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top
% 6.42/1.52      | r2_hidden(X0,sK5) != iProver_top
% 6.42/1.52      | k1_relset_1(sK6,sK4,sK8) = k1_xboole_0 ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_5125,c_61,c_3812]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_5745,plain,
% 6.42/1.52      ( k1_relset_1(sK6,sK4,sK8) = k1_xboole_0
% 6.42/1.52      | r2_hidden(X0,sK5) != iProver_top
% 6.42/1.52      | r2_hidden(k1_funct_1(sK7,X0),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 6.42/1.52      inference(renaming,[status(thm)],[c_5744]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_7656,plain,
% 6.42/1.52      ( k1_relat_1(sK8) = k1_xboole_0
% 6.42/1.52      | r2_hidden(X0,sK5) != iProver_top
% 6.42/1.52      | r2_hidden(k1_funct_1(sK7,X0),k1_relat_1(sK8)) = iProver_top ),
% 6.42/1.52      inference(demodulation,[status(thm)],[c_7314,c_5745]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_35,plain,
% 6.42/1.52      ( ~ v5_relat_1(X0,X1)
% 6.42/1.52      | ~ r2_hidden(X2,k1_relat_1(X0))
% 6.42/1.52      | ~ v1_funct_1(X0)
% 6.42/1.52      | ~ v1_relat_1(X0)
% 6.42/1.52      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 6.42/1.52      inference(cnf_transformation,[],[f125]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2469,plain,
% 6.42/1.52      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 6.42/1.52      | v5_relat_1(X1,X0) != iProver_top
% 6.42/1.52      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 6.42/1.52      | v1_funct_1(X1) != iProver_top
% 6.42/1.52      | v1_relat_1(X1) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_12201,plain,
% 6.42/1.52      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
% 6.42/1.52      | k1_relat_1(sK8) = k1_xboole_0
% 6.42/1.52      | v5_relat_1(sK8,X0) != iProver_top
% 6.42/1.52      | r2_hidden(X1,sK5) != iProver_top
% 6.42/1.52      | v1_funct_1(sK8) != iProver_top
% 6.42/1.52      | v1_relat_1(sK8) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_7656,c_2469]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_55,negated_conjecture,
% 6.42/1.52      ( v1_funct_1(sK8) ),
% 6.42/1.52      inference(cnf_transformation,[],[f144]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_64,plain,
% 6.42/1.52      ( v1_funct_1(sK8) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_65,plain,
% 6.42/1.52      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_27,plain,
% 6.42/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | v1_relat_1(X0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f117]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2908,plain,
% 6.42/1.52      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
% 6.42/1.52      | v1_relat_1(sK8) ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_27]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2909,plain,
% 6.42/1.52      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
% 6.42/1.52      | v1_relat_1(sK8) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_2908]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_23628,plain,
% 6.42/1.52      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,X1)) = k1_funct_1(sK8,k1_funct_1(sK7,X1))
% 6.42/1.52      | k1_relat_1(sK8) = k1_xboole_0
% 6.42/1.52      | v5_relat_1(sK8,X0) != iProver_top
% 6.42/1.52      | r2_hidden(X1,sK5) != iProver_top ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_12201,c_64,c_65,c_2909]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_23641,plain,
% 6.42/1.52      ( k7_partfun1(X0,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 6.42/1.52      | k1_relat_1(sK8) = k1_xboole_0
% 6.42/1.52      | v5_relat_1(sK8,X0) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_8194,c_23628]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_23704,plain,
% 6.42/1.52      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
% 6.42/1.52      | k1_relat_1(sK8) = k1_xboole_0 ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_6280,c_23641]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_31,plain,
% 6.42/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f121]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2470,plain,
% 6.42/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.42/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_7183,plain,
% 6.42/1.52      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2454,c_2470]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_36,plain,
% 6.42/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.42/1.52      | ~ m1_subset_1(X3,X1)
% 6.42/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 6.42/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 6.42/1.52      | ~ v1_funct_1(X4)
% 6.42/1.52      | ~ v1_funct_1(X0)
% 6.42/1.52      | v1_xboole_0(X2)
% 6.42/1.52      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 6.42/1.52      | k1_xboole_0 = X1 ),
% 6.42/1.52      inference(cnf_transformation,[],[f126]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2468,plain,
% 6.42/1.52      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 6.42/1.52      | k1_xboole_0 = X0
% 6.42/1.52      | v1_funct_2(X3,X0,X1) != iProver_top
% 6.42/1.52      | m1_subset_1(X5,X0) != iProver_top
% 6.42/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.42/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.42/1.52      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 6.42/1.52      | v1_funct_1(X3) != iProver_top
% 6.42/1.52      | v1_funct_1(X4) != iProver_top
% 6.42/1.52      | v1_xboole_0(X1) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_9720,plain,
% 6.42/1.52      ( k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 6.42/1.52      | sK5 = k1_xboole_0
% 6.42/1.52      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 6.42/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 6.42/1.52      | m1_subset_1(X2,sK5) != iProver_top
% 6.42/1.52      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 6.42/1.52      | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
% 6.42/1.52      | v1_funct_1(X1) != iProver_top
% 6.42/1.52      | v1_funct_1(sK7) != iProver_top
% 6.42/1.52      | v1_xboole_0(sK6) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_7183,c_2468]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_60,plain,
% 6.42/1.52      ( v1_xboole_0(sK6) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_63,plain,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_13,plain,
% 6.42/1.52      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 6.42/1.52      | k1_xboole_0 = X0
% 6.42/1.52      | k1_xboole_0 = X1 ),
% 6.42/1.52      inference(cnf_transformation,[],[f101]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_150,plain,
% 6.42/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 6.42/1.52      | k1_xboole_0 = k1_xboole_0 ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_13]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_12,plain,
% 6.42/1.52      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 6.42/1.52      inference(cnf_transformation,[],[f153]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_151,plain,
% 6.42/1.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_12]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_1630,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2964,plain,
% 6.42/1.52      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_1630]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2965,plain,
% 6.42/1.52      ( sK5 != k1_xboole_0
% 6.42/1.52      | k1_xboole_0 = sK5
% 6.42/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_2964]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_13920,plain,
% 6.42/1.52      ( m1_subset_1(X2,sK5) != iProver_top
% 6.42/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 6.42/1.52      | k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 6.42/1.52      | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
% 6.42/1.52      | v1_funct_1(X1) != iProver_top ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_9720,c_60,c_61,c_62,c_63,c_51,c_150,c_151,c_2965]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_13921,plain,
% 6.42/1.52      ( k1_funct_1(k8_funct_2(sK5,sK6,X0,sK7,X1),X2) = k1_funct_1(X1,k1_funct_1(sK7,X2))
% 6.42/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) != iProver_top
% 6.42/1.52      | m1_subset_1(X2,sK5) != iProver_top
% 6.42/1.52      | r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,X0,X1)) != iProver_top
% 6.42/1.52      | v1_funct_1(X1) != iProver_top ),
% 6.42/1.52      inference(renaming,[status(thm)],[c_13920]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_13932,plain,
% 6.42/1.52      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
% 6.42/1.52      | m1_subset_1(X0,sK5) != iProver_top
% 6.42/1.52      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
% 6.42/1.52      | r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) != iProver_top
% 6.42/1.52      | v1_funct_1(sK8) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_7314,c_13921]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_7503,plain,
% 6.42/1.52      ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) = iProver_top ),
% 6.42/1.52      inference(demodulation,[status(thm)],[c_7183,c_2458]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_7784,plain,
% 6.42/1.52      ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) = iProver_top ),
% 6.42/1.52      inference(light_normalisation,[status(thm)],[c_7503,c_7314]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_14006,plain,
% 6.42/1.52      ( m1_subset_1(X0,sK5) != iProver_top
% 6.42/1.52      | k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0)) ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_13932,c_64,c_65,c_7784]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_14007,plain,
% 6.42/1.52      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X0) = k1_funct_1(sK8,k1_funct_1(sK7,X0))
% 6.42/1.52      | m1_subset_1(X0,sK5) != iProver_top ),
% 6.42/1.52      inference(renaming,[status(thm)],[c_14006]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_14014,plain,
% 6.42/1.52      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2457,c_14007]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_50,negated_conjecture,
% 6.42/1.52      ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
% 6.42/1.52      inference(cnf_transformation,[],[f149]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_14016,plain,
% 6.42/1.52      ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
% 6.42/1.52      inference(demodulation,[status(thm)],[c_14014,c_50]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_23831,plain,
% 6.42/1.52      ( k1_relat_1(sK8) = k1_xboole_0 ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_23704,c_14016]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_0,plain,
% 6.42/1.52      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f91]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2497,plain,
% 6.42/1.52      ( r2_hidden(sK0(X0),X0) = iProver_top
% 6.42/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_4,plain,
% 6.42/1.52      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 6.42/1.52      inference(cnf_transformation,[],[f92]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2493,plain,
% 6.42/1.52      ( r1_tarski(X0,X1) != iProver_top
% 6.42/1.52      | r2_hidden(X2,X0) != iProver_top
% 6.42/1.52      | r2_hidden(X2,X1) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_8996,plain,
% 6.42/1.52      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 6.42/1.52      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_7784,c_2493]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_14560,plain,
% 6.42/1.52      ( r2_hidden(sK0(k2_relat_1(sK7)),k1_relat_1(sK8)) = iProver_top
% 6.42/1.52      | v1_xboole_0(k2_relat_1(sK7)) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2497,c_8996]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_165,plain,
% 6.42/1.52      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_33,plain,
% 6.42/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.42/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | ~ v1_funct_1(X0)
% 6.42/1.52      | ~ v1_xboole_0(X0)
% 6.42/1.52      | v1_xboole_0(X1)
% 6.42/1.52      | v1_xboole_0(X2) ),
% 6.42/1.52      inference(cnf_transformation,[],[f123]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_24,plain,
% 6.42/1.52      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f114]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_303,plain,
% 6.42/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | ~ v1_funct_2(X0,X1,X2)
% 6.42/1.52      | ~ v1_xboole_0(X0)
% 6.42/1.52      | v1_xboole_0(X1)
% 6.42/1.52      | v1_xboole_0(X2) ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_33,c_24]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_304,plain,
% 6.42/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.42/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | ~ v1_xboole_0(X0)
% 6.42/1.52      | v1_xboole_0(X1)
% 6.42/1.52      | v1_xboole_0(X2) ),
% 6.42/1.52      inference(renaming,[status(thm)],[c_303]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2450,plain,
% 6.42/1.52      ( v1_funct_2(X0,X1,X2) != iProver_top
% 6.42/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.42/1.52      | v1_xboole_0(X0) != iProver_top
% 6.42/1.52      | v1_xboole_0(X2) = iProver_top
% 6.42/1.52      | v1_xboole_0(X1) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2994,plain,
% 6.42/1.52      ( v1_funct_2(sK7,sK5,sK6) != iProver_top
% 6.42/1.52      | v1_xboole_0(sK7) != iProver_top
% 6.42/1.52      | v1_xboole_0(sK6) = iProver_top
% 6.42/1.52      | v1_xboole_0(sK5) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2454,c_2450]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_3,plain,
% 6.42/1.52      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f93]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2494,plain,
% 6.42/1.52      ( r1_tarski(X0,X1) = iProver_top
% 6.42/1.52      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_1,plain,
% 6.42/1.52      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.42/1.52      inference(cnf_transformation,[],[f90]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2496,plain,
% 6.42/1.52      ( r2_hidden(X0,X1) != iProver_top
% 6.42/1.52      | v1_xboole_0(X1) != iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_5272,plain,
% 6.42/1.52      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_2494,c_2496]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_11,plain,
% 6.42/1.52      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.42/1.52      inference(cnf_transformation,[],[f152]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_7499,plain,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) = iProver_top
% 6.42/1.52      | r1_tarski(k2_relat_1(sK7),X0) != iProver_top ),
% 6.42/1.52      inference(demodulation,[status(thm)],[c_7183,c_4534]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_9410,plain,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.42/1.52      | r1_tarski(k2_relat_1(sK7),k1_xboole_0) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_11,c_7499]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_14765,plain,
% 6.42/1.52      ( m1_subset_1(sK7,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 6.42/1.52      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_5272,c_9410]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_29,plain,
% 6.42/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.42/1.52      | ~ v1_xboole_0(X1)
% 6.42/1.52      | v1_xboole_0(X0) ),
% 6.42/1.52      inference(cnf_transformation,[],[f119]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_2472,plain,
% 6.42/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.42/1.52      | v1_xboole_0(X1) != iProver_top
% 6.42/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.42/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_9021,plain,
% 6.42/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 6.42/1.52      | v1_xboole_0(X1) != iProver_top
% 6.42/1.52      | v1_xboole_0(X0) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_11,c_2472]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_18496,plain,
% 6.42/1.52      ( v1_xboole_0(X0) != iProver_top
% 6.42/1.52      | v1_xboole_0(k2_relat_1(sK7)) != iProver_top
% 6.42/1.52      | v1_xboole_0(sK7) = iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_14765,c_9021]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_18553,plain,
% 6.42/1.52      ( v1_xboole_0(k2_relat_1(sK7)) != iProver_top
% 6.42/1.52      | v1_xboole_0(sK7) = iProver_top
% 6.42/1.52      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.42/1.52      inference(instantiation,[status(thm)],[c_18496]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_18721,plain,
% 6.42/1.52      ( r2_hidden(sK0(k2_relat_1(sK7)),k1_relat_1(sK8)) = iProver_top ),
% 6.42/1.52      inference(global_propositional_subsumption,
% 6.42/1.52                [status(thm)],
% 6.42/1.52                [c_14560,c_60,c_62,c_51,c_165,c_2881,c_2994,c_18553]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_18726,plain,
% 6.42/1.52      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 6.42/1.52      inference(superposition,[status(thm)],[c_18721,c_2496]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(c_23838,plain,
% 6.42/1.52      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 6.42/1.52      inference(demodulation,[status(thm)],[c_23831,c_18726]) ).
% 6.42/1.52  
% 6.42/1.52  cnf(contradiction,plain,
% 6.42/1.52      ( $false ),
% 6.42/1.52      inference(minisat,[status(thm)],[c_23838,c_165]) ).
% 6.42/1.52  
% 6.42/1.52  
% 6.42/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 6.42/1.52  
% 6.42/1.52  ------                               Statistics
% 6.42/1.52  
% 6.42/1.52  ------ General
% 6.42/1.52  
% 6.42/1.52  abstr_ref_over_cycles:                  0
% 6.42/1.52  abstr_ref_under_cycles:                 0
% 6.42/1.52  gc_basic_clause_elim:                   0
% 6.42/1.52  forced_gc_time:                         0
% 6.42/1.52  parsing_time:                           0.028
% 6.42/1.52  unif_index_cands_time:                  0.
% 6.42/1.52  unif_index_add_time:                    0.
% 6.42/1.52  orderings_time:                         0.
% 6.42/1.52  out_proof_time:                         0.016
% 6.42/1.52  total_time:                             0.741
% 6.42/1.52  num_of_symbols:                         59
% 6.42/1.52  num_of_terms:                           22378
% 6.42/1.52  
% 6.42/1.52  ------ Preprocessing
% 6.42/1.52  
% 6.42/1.52  num_of_splits:                          0
% 6.42/1.52  num_of_split_atoms:                     0
% 6.42/1.52  num_of_reused_defs:                     0
% 6.42/1.52  num_eq_ax_congr_red:                    30
% 6.42/1.52  num_of_sem_filtered_clauses:            1
% 6.42/1.52  num_of_subtypes:                        0
% 6.42/1.52  monotx_restored_types:                  0
% 6.42/1.52  sat_num_of_epr_types:                   0
% 6.42/1.52  sat_num_of_non_cyclic_types:            0
% 6.42/1.52  sat_guarded_non_collapsed_types:        0
% 6.42/1.52  num_pure_diseq_elim:                    0
% 6.42/1.52  simp_replaced_by:                       0
% 6.42/1.52  res_preprocessed:                       247
% 6.42/1.52  prep_upred:                             0
% 6.42/1.52  prep_unflattend:                        24
% 6.42/1.52  smt_new_axioms:                         0
% 6.42/1.52  pred_elim_cands:                        8
% 6.42/1.52  pred_elim:                              0
% 6.42/1.52  pred_elim_cl:                           0
% 6.42/1.52  pred_elim_cycles:                       2
% 6.42/1.52  merged_defs:                            0
% 6.42/1.52  merged_defs_ncl:                        0
% 6.42/1.52  bin_hyper_res:                          0
% 6.42/1.52  prep_cycles:                            4
% 6.42/1.52  pred_elim_time:                         0.02
% 6.42/1.52  splitting_time:                         0.
% 6.42/1.52  sem_filter_time:                        0.
% 6.42/1.52  monotx_time:                            0.001
% 6.42/1.52  subtype_inf_time:                       0.
% 6.42/1.52  
% 6.42/1.52  ------ Problem properties
% 6.42/1.52  
% 6.42/1.52  clauses:                                53
% 6.42/1.52  conjectures:                            10
% 6.42/1.52  epr:                                    15
% 6.42/1.52  horn:                                   41
% 6.42/1.52  ground:                                 11
% 6.42/1.52  unary:                                  17
% 6.42/1.52  binary:                                 12
% 6.42/1.52  lits:                                   143
% 6.42/1.52  lits_eq:                                22
% 6.42/1.52  fd_pure:                                0
% 6.42/1.52  fd_pseudo:                              0
% 6.42/1.52  fd_cond:                                7
% 6.42/1.52  fd_pseudo_cond:                         1
% 6.42/1.52  ac_symbols:                             0
% 6.42/1.52  
% 6.42/1.52  ------ Propositional Solver
% 6.42/1.52  
% 6.42/1.52  prop_solver_calls:                      28
% 6.42/1.52  prop_fast_solver_calls:                 2560
% 6.42/1.52  smt_solver_calls:                       0
% 6.42/1.52  smt_fast_solver_calls:                  0
% 6.42/1.52  prop_num_of_clauses:                    8772
% 6.42/1.52  prop_preprocess_simplified:             23206
% 6.42/1.52  prop_fo_subsumed:                       109
% 6.42/1.52  prop_solver_time:                       0.
% 6.42/1.52  smt_solver_time:                        0.
% 6.42/1.52  smt_fast_solver_time:                   0.
% 6.42/1.52  prop_fast_solver_time:                  0.
% 6.42/1.52  prop_unsat_core_time:                   0.001
% 6.42/1.52  
% 6.42/1.52  ------ QBF
% 6.42/1.52  
% 6.42/1.52  qbf_q_res:                              0
% 6.42/1.52  qbf_num_tautologies:                    0
% 6.42/1.52  qbf_prep_cycles:                        0
% 6.42/1.52  
% 6.42/1.52  ------ BMC1
% 6.42/1.52  
% 6.42/1.52  bmc1_current_bound:                     -1
% 6.42/1.52  bmc1_last_solved_bound:                 -1
% 6.42/1.52  bmc1_unsat_core_size:                   -1
% 6.42/1.52  bmc1_unsat_core_parents_size:           -1
% 6.42/1.52  bmc1_merge_next_fun:                    0
% 6.42/1.52  bmc1_unsat_core_clauses_time:           0.
% 6.42/1.52  
% 6.42/1.52  ------ Instantiation
% 6.42/1.52  
% 6.42/1.52  inst_num_of_clauses:                    2612
% 6.42/1.52  inst_num_in_passive:                    1383
% 6.42/1.52  inst_num_in_active:                     955
% 6.42/1.52  inst_num_in_unprocessed:                274
% 6.42/1.52  inst_num_of_loops:                      1220
% 6.42/1.52  inst_num_of_learning_restarts:          0
% 6.42/1.52  inst_num_moves_active_passive:          264
% 6.42/1.52  inst_lit_activity:                      0
% 6.42/1.52  inst_lit_activity_moves:                0
% 6.42/1.52  inst_num_tautologies:                   0
% 6.42/1.52  inst_num_prop_implied:                  0
% 6.42/1.52  inst_num_existing_simplified:           0
% 6.42/1.52  inst_num_eq_res_simplified:             0
% 6.42/1.52  inst_num_child_elim:                    0
% 6.42/1.52  inst_num_of_dismatching_blockings:      1002
% 6.42/1.52  inst_num_of_non_proper_insts:           2410
% 6.42/1.52  inst_num_of_duplicates:                 0
% 6.42/1.52  inst_inst_num_from_inst_to_res:         0
% 6.42/1.52  inst_dismatching_checking_time:         0.
% 6.42/1.52  
% 6.42/1.52  ------ Resolution
% 6.42/1.52  
% 6.42/1.52  res_num_of_clauses:                     0
% 6.42/1.52  res_num_in_passive:                     0
% 6.42/1.52  res_num_in_active:                      0
% 6.42/1.52  res_num_of_loops:                       251
% 6.42/1.52  res_forward_subset_subsumed:            171
% 6.42/1.52  res_backward_subset_subsumed:           0
% 6.42/1.52  res_forward_subsumed:                   0
% 6.42/1.52  res_backward_subsumed:                  0
% 6.42/1.52  res_forward_subsumption_resolution:     0
% 6.42/1.52  res_backward_subsumption_resolution:    0
% 6.42/1.52  res_clause_to_clause_subsumption:       1353
% 6.42/1.52  res_orphan_elimination:                 0
% 6.42/1.52  res_tautology_del:                      156
% 6.42/1.52  res_num_eq_res_simplified:              0
% 6.42/1.52  res_num_sel_changes:                    0
% 6.42/1.52  res_moves_from_active_to_pass:          0
% 6.42/1.52  
% 6.42/1.52  ------ Superposition
% 6.42/1.52  
% 6.42/1.52  sup_time_total:                         0.
% 6.42/1.52  sup_time_generating:                    0.
% 6.42/1.52  sup_time_sim_full:                      0.
% 6.42/1.52  sup_time_sim_immed:                     0.
% 6.42/1.52  
% 6.42/1.52  sup_num_of_clauses:                     324
% 6.42/1.52  sup_num_in_active:                      180
% 6.42/1.52  sup_num_in_passive:                     144
% 6.42/1.52  sup_num_of_loops:                       242
% 6.42/1.52  sup_fw_superposition:                   226
% 6.42/1.52  sup_bw_superposition:                   225
% 6.42/1.52  sup_immediate_simplified:               71
% 6.42/1.52  sup_given_eliminated:                   2
% 6.42/1.52  comparisons_done:                       0
% 6.42/1.52  comparisons_avoided:                    24
% 6.42/1.52  
% 6.42/1.52  ------ Simplifications
% 6.42/1.52  
% 6.42/1.52  
% 6.42/1.52  sim_fw_subset_subsumed:                 43
% 6.42/1.52  sim_bw_subset_subsumed:                 12
% 6.42/1.52  sim_fw_subsumed:                        26
% 6.42/1.52  sim_bw_subsumed:                        6
% 6.42/1.52  sim_fw_subsumption_res:                 9
% 6.42/1.52  sim_bw_subsumption_res:                 0
% 6.42/1.52  sim_tautology_del:                      16
% 6.42/1.52  sim_eq_tautology_del:                   12
% 6.42/1.52  sim_eq_res_simp:                        0
% 6.42/1.52  sim_fw_demodulated:                     19
% 6.42/1.52  sim_bw_demodulated:                     60
% 6.42/1.52  sim_light_normalised:                   22
% 6.42/1.52  sim_joinable_taut:                      0
% 6.42/1.52  sim_joinable_simp:                      0
% 6.42/1.52  sim_ac_normalised:                      0
% 6.42/1.52  sim_smt_subsumption:                    0
% 6.42/1.52  
%------------------------------------------------------------------------------
