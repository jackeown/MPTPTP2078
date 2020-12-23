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
% DateTime   : Thu Dec  3 12:09:52 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 803 expanded)
%              Number of clauses        :  118 ( 250 expanded)
%              Number of leaves         :   27 ( 255 expanded)
%              Depth                    :   22
%              Number of atoms          :  754 (5395 expanded)
%              Number of equality atoms :  334 (1483 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK11) != k7_partfun1(X0,X4,k1_funct_1(X3,sK11))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK11,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK10),X5) != k7_partfun1(X0,sK10,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK10))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK9,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK9,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK9),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK9,X1,X2)
        & v1_funct_1(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
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
                  ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK7
                  & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4))
                  & m1_subset_1(X5,sK7) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
          & v1_funct_2(X3,sK7,sK8)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))
    & k1_xboole_0 != sK7
    & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    & m1_subset_1(sK11,sK7)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK9,sK7,sK8)
    & v1_funct_1(sK9)
    & ~ v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f47,f69,f68,f67,f66])).

fof(f110,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f70])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f70])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f105,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f106,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f70])).

fof(f107,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f70])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2(X0))
      & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f56])).

fof(f79,plain,(
    ! [X0] : v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f70])).

fof(f112,plain,(
    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f70])).

fof(f111,plain,(
    m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f70])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f59])).

fof(f63,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f60,f63,f62,f61])).

fof(f87,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f116,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f115])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f70])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_relat_1(X4) )
         => ( r2_hidden(X2,X0)
           => ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
          | k1_xboole_0 = X1
          | ~ r2_hidden(X2,X0)
          | ~ v1_funct_1(X4)
          | ~ v1_relat_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2534,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2547,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4883,plain,
    ( k1_relset_1(sK8,sK6,sK10) = k1_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_2534,c_2547])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2532,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2546,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4424,plain,
    ( k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_2532,c_2546])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2545,plain,
    ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
    | k1_xboole_0 = X1
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6662,plain,
    ( k1_partfun1(sK7,sK8,sK8,X0,sK9,X1) = k8_funct_2(sK7,sK8,X0,sK9,X1)
    | sK8 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK8,X0))) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_4424,c_2545])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_44,plain,
    ( v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_45,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_46,plain,
    ( v1_funct_2(sK9,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_47,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1625,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2656,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_2660,plain,
    ( sK8 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2656])).

cnf(c_2662,plain,
    ( sK8 != k1_xboole_0
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2660])).

cnf(c_7,plain,
    ( v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2560,plain,
    ( v1_xboole_0(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2562,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3337,plain,
    ( sK2(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2560,c_2562])).

cnf(c_3340,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3337,c_2560])).

cnf(c_31890,plain,
    ( v1_funct_1(X1) != iProver_top
    | r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,X0,X1)) != iProver_top
    | k1_partfun1(sK7,sK8,sK8,X0,sK9,X1) = k8_funct_2(sK7,sK8,X0,sK9,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK8,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6662,c_44,c_45,c_46,c_47,c_2662,c_3340])).

cnf(c_31891,plain,
    ( k1_partfun1(sK7,sK8,sK8,X0,sK9,X1) = k8_funct_2(sK7,sK8,X0,sK9,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK8,X0))) != iProver_top
    | r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_31890])).

cnf(c_31902,plain,
    ( k1_partfun1(sK7,sK8,sK8,sK6,sK9,sK10) = k8_funct_2(sK7,sK8,sK6,sK9,sK10)
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
    | r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4883,c_31891])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2538,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4870,plain,
    ( k1_partfun1(X0,X1,sK8,sK6,X2,sK10) = k5_relat_1(X2,sK10)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2538])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_48,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5170,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK8,sK6,X2,sK10) = k5_relat_1(X2,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4870,c_48])).

cnf(c_5171,plain,
    ( k1_partfun1(X0,X1,sK8,sK6,X2,sK10) = k5_relat_1(X2,sK10)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5170])).

cnf(c_5178,plain,
    ( k1_partfun1(sK7,sK8,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10)
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2532,c_5171])).

cnf(c_5407,plain,
    ( k1_partfun1(sK7,sK8,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5178,c_45])).

cnf(c_31904,plain,
    ( k8_funct_2(sK7,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10)
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
    | r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) != iProver_top
    | v1_funct_1(sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31902,c_5407])).

cnf(c_49,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2536,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4540,plain,
    ( r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4424,c_2536])).

cnf(c_5072,plain,
    ( r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4883,c_4540])).

cnf(c_32200,plain,
    ( k8_funct_2(sK7,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31904,c_48,c_49,c_5072])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2535,plain,
    ( m1_subset_1(sK11,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2558,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4984,plain,
    ( r2_hidden(sK11,sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_2558])).

cnf(c_50,plain,
    ( m1_subset_1(sK11,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2620,plain,
    ( ~ v1_xboole_0(sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2621,plain,
    ( k1_xboole_0 = sK7
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2620])).

cnf(c_2687,plain,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2907,plain,
    ( ~ m1_subset_1(sK11,sK7)
    | r2_hidden(sK11,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_2908,plain,
    ( m1_subset_1(sK11,sK7) != iProver_top
    | r2_hidden(sK11,sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2907])).

cnf(c_5722,plain,
    ( r2_hidden(sK11,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4984,c_50,c_35,c_2621,c_2908])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2551,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2563,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5059,plain,
    ( r2_hidden(X0,k1_relset_1(sK8,sK6,sK10)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4540,c_2563])).

cnf(c_5060,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5059,c_4883])).

cnf(c_6595,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_2551,c_5060])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2555,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2556,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3681,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2532,c_2556])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_328,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_329,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_415,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_329])).

cnf(c_2528,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_3790,plain,
    ( v1_relat_1(k2_zfmisc_1(sK7,sK8)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_3681,c_2528])).

cnf(c_4112,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_3790])).

cnf(c_29558,plain,
    ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6595,c_45,c_4112])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2539,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5594,plain,
    ( k1_relset_1(sK7,sK8,sK9) = sK7
    | sK8 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2532,c_2539])).

cnf(c_4884,plain,
    ( k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) ),
    inference(superposition,[status(thm)],[c_2532,c_2547])).

cnf(c_5597,plain,
    ( k1_relat_1(sK9) = sK7
    | sK8 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5594,c_4884])).

cnf(c_8280,plain,
    ( k1_relat_1(sK9) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5597,c_44,c_46,c_2662,c_3340])).

cnf(c_29564,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29558,c_8280])).

cnf(c_21,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_31,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_21,c_31])).

cnf(c_2527,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_3216,plain,
    ( k7_partfun1(sK6,sK10,X0) = k1_funct_1(sK10,X0)
    | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2527])).

cnf(c_3299,plain,
    ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | k7_partfun1(sK6,sK10,X0) = k1_funct_1(sK10,X0)
    | v1_relat_1(sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3216,c_48])).

cnf(c_3300,plain,
    ( k7_partfun1(sK6,sK10,X0) = k1_funct_1(sK10,X0)
    | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(renaming,[status(thm)],[c_3299])).

cnf(c_29574,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
    | r2_hidden(X0,sK7) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_29564,c_3300])).

cnf(c_3680,plain,
    ( r1_tarski(sK10,k2_zfmisc_1(sK8,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2556])).

cnf(c_3690,plain,
    ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) != iProver_top
    | v1_relat_1(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3680,c_2528])).

cnf(c_4018,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_3690])).

cnf(c_31416,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29574,c_4018])).

cnf(c_31417,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_31416])).

cnf(c_31427,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(superposition,[status(thm)],[c_5722,c_31417])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_31486,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(demodulation,[status(thm)],[c_31427,c_34])).

cnf(c_32202,plain,
    ( k1_funct_1(k5_relat_1(sK9,sK10),sK11) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(demodulation,[status(thm)],[c_32200,c_31486])).

cnf(c_2533,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2537,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | k1_xboole_0 = X3
    | v1_funct_2(X0,X4,X3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) != iProver_top
    | r2_hidden(X2,X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4116,plain,
    ( k1_funct_1(k5_relat_1(sK9,X0),X1) = k1_funct_1(X0,k1_funct_1(sK9,X1))
    | sK8 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2532,c_2537])).

cnf(c_4692,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | k1_funct_1(k5_relat_1(sK9,X0),X1) = k1_funct_1(X0,k1_funct_1(sK9,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4116,c_44,c_45,c_46,c_2662,c_3340])).

cnf(c_4693,plain,
    ( k1_funct_1(k5_relat_1(sK9,X0),X1) = k1_funct_1(X0,k1_funct_1(sK9,X1))
    | r2_hidden(X1,sK7) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4692])).

cnf(c_5727,plain,
    ( k1_funct_1(X0,k1_funct_1(sK9,sK11)) = k1_funct_1(k5_relat_1(sK9,X0),sK11)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5722,c_4693])).

cnf(c_7091,plain,
    ( k1_funct_1(k5_relat_1(sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_5727])).

cnf(c_7530,plain,
    ( k1_funct_1(k5_relat_1(sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7091,c_4018])).

cnf(c_32203,plain,
    ( k1_funct_1(sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(light_normalisation,[status(thm)],[c_32202,c_7530])).

cnf(c_32204,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_32203])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:12:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.00/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.49  
% 8.00/1.49  ------  iProver source info
% 8.00/1.49  
% 8.00/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.49  git: non_committed_changes: false
% 8.00/1.49  git: last_make_outside_of_git: false
% 8.00/1.49  
% 8.00/1.49  ------ 
% 8.00/1.49  
% 8.00/1.49  ------ Input Options
% 8.00/1.49  
% 8.00/1.49  --out_options                           all
% 8.00/1.49  --tptp_safe_out                         true
% 8.00/1.49  --problem_path                          ""
% 8.00/1.49  --include_path                          ""
% 8.00/1.49  --clausifier                            res/vclausify_rel
% 8.00/1.49  --clausifier_options                    ""
% 8.00/1.49  --stdin                                 false
% 8.00/1.49  --stats_out                             all
% 8.00/1.49  
% 8.00/1.49  ------ General Options
% 8.00/1.49  
% 8.00/1.49  --fof                                   false
% 8.00/1.49  --time_out_real                         305.
% 8.00/1.49  --time_out_virtual                      -1.
% 8.00/1.49  --symbol_type_check                     false
% 8.00/1.49  --clausify_out                          false
% 8.00/1.49  --sig_cnt_out                           false
% 8.00/1.49  --trig_cnt_out                          false
% 8.00/1.49  --trig_cnt_out_tolerance                1.
% 8.00/1.49  --trig_cnt_out_sk_spl                   false
% 8.00/1.49  --abstr_cl_out                          false
% 8.00/1.49  
% 8.00/1.49  ------ Global Options
% 8.00/1.49  
% 8.00/1.49  --schedule                              default
% 8.00/1.49  --add_important_lit                     false
% 8.00/1.49  --prop_solver_per_cl                    1000
% 8.00/1.49  --min_unsat_core                        false
% 8.00/1.49  --soft_assumptions                      false
% 8.00/1.49  --soft_lemma_size                       3
% 8.00/1.49  --prop_impl_unit_size                   0
% 8.00/1.49  --prop_impl_unit                        []
% 8.00/1.49  --share_sel_clauses                     true
% 8.00/1.49  --reset_solvers                         false
% 8.00/1.49  --bc_imp_inh                            [conj_cone]
% 8.00/1.49  --conj_cone_tolerance                   3.
% 8.00/1.49  --extra_neg_conj                        none
% 8.00/1.49  --large_theory_mode                     true
% 8.00/1.49  --prolific_symb_bound                   200
% 8.00/1.49  --lt_threshold                          2000
% 8.00/1.49  --clause_weak_htbl                      true
% 8.00/1.49  --gc_record_bc_elim                     false
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing Options
% 8.00/1.49  
% 8.00/1.49  --preprocessing_flag                    true
% 8.00/1.49  --time_out_prep_mult                    0.1
% 8.00/1.49  --splitting_mode                        input
% 8.00/1.49  --splitting_grd                         true
% 8.00/1.49  --splitting_cvd                         false
% 8.00/1.49  --splitting_cvd_svl                     false
% 8.00/1.49  --splitting_nvd                         32
% 8.00/1.49  --sub_typing                            true
% 8.00/1.49  --prep_gs_sim                           true
% 8.00/1.49  --prep_unflatten                        true
% 8.00/1.49  --prep_res_sim                          true
% 8.00/1.49  --prep_upred                            true
% 8.00/1.49  --prep_sem_filter                       exhaustive
% 8.00/1.49  --prep_sem_filter_out                   false
% 8.00/1.49  --pred_elim                             true
% 8.00/1.49  --res_sim_input                         true
% 8.00/1.49  --eq_ax_congr_red                       true
% 8.00/1.49  --pure_diseq_elim                       true
% 8.00/1.49  --brand_transform                       false
% 8.00/1.49  --non_eq_to_eq                          false
% 8.00/1.49  --prep_def_merge                        true
% 8.00/1.49  --prep_def_merge_prop_impl              false
% 8.00/1.49  --prep_def_merge_mbd                    true
% 8.00/1.49  --prep_def_merge_tr_red                 false
% 8.00/1.49  --prep_def_merge_tr_cl                  false
% 8.00/1.49  --smt_preprocessing                     true
% 8.00/1.49  --smt_ac_axioms                         fast
% 8.00/1.49  --preprocessed_out                      false
% 8.00/1.49  --preprocessed_stats                    false
% 8.00/1.49  
% 8.00/1.49  ------ Abstraction refinement Options
% 8.00/1.49  
% 8.00/1.49  --abstr_ref                             []
% 8.00/1.49  --abstr_ref_prep                        false
% 8.00/1.49  --abstr_ref_until_sat                   false
% 8.00/1.49  --abstr_ref_sig_restrict                funpre
% 8.00/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.49  --abstr_ref_under                       []
% 8.00/1.49  
% 8.00/1.49  ------ SAT Options
% 8.00/1.49  
% 8.00/1.49  --sat_mode                              false
% 8.00/1.49  --sat_fm_restart_options                ""
% 8.00/1.49  --sat_gr_def                            false
% 8.00/1.49  --sat_epr_types                         true
% 8.00/1.49  --sat_non_cyclic_types                  false
% 8.00/1.49  --sat_finite_models                     false
% 8.00/1.49  --sat_fm_lemmas                         false
% 8.00/1.49  --sat_fm_prep                           false
% 8.00/1.49  --sat_fm_uc_incr                        true
% 8.00/1.49  --sat_out_model                         small
% 8.00/1.49  --sat_out_clauses                       false
% 8.00/1.49  
% 8.00/1.49  ------ QBF Options
% 8.00/1.49  
% 8.00/1.49  --qbf_mode                              false
% 8.00/1.49  --qbf_elim_univ                         false
% 8.00/1.49  --qbf_dom_inst                          none
% 8.00/1.49  --qbf_dom_pre_inst                      false
% 8.00/1.49  --qbf_sk_in                             false
% 8.00/1.49  --qbf_pred_elim                         true
% 8.00/1.49  --qbf_split                             512
% 8.00/1.49  
% 8.00/1.49  ------ BMC1 Options
% 8.00/1.49  
% 8.00/1.49  --bmc1_incremental                      false
% 8.00/1.49  --bmc1_axioms                           reachable_all
% 8.00/1.49  --bmc1_min_bound                        0
% 8.00/1.49  --bmc1_max_bound                        -1
% 8.00/1.49  --bmc1_max_bound_default                -1
% 8.00/1.49  --bmc1_symbol_reachability              true
% 8.00/1.49  --bmc1_property_lemmas                  false
% 8.00/1.49  --bmc1_k_induction                      false
% 8.00/1.49  --bmc1_non_equiv_states                 false
% 8.00/1.49  --bmc1_deadlock                         false
% 8.00/1.49  --bmc1_ucm                              false
% 8.00/1.49  --bmc1_add_unsat_core                   none
% 8.00/1.49  --bmc1_unsat_core_children              false
% 8.00/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.49  --bmc1_out_stat                         full
% 8.00/1.49  --bmc1_ground_init                      false
% 8.00/1.49  --bmc1_pre_inst_next_state              false
% 8.00/1.49  --bmc1_pre_inst_state                   false
% 8.00/1.49  --bmc1_pre_inst_reach_state             false
% 8.00/1.49  --bmc1_out_unsat_core                   false
% 8.00/1.49  --bmc1_aig_witness_out                  false
% 8.00/1.49  --bmc1_verbose                          false
% 8.00/1.49  --bmc1_dump_clauses_tptp                false
% 8.00/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.49  --bmc1_dump_file                        -
% 8.00/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.49  --bmc1_ucm_extend_mode                  1
% 8.00/1.49  --bmc1_ucm_init_mode                    2
% 8.00/1.49  --bmc1_ucm_cone_mode                    none
% 8.00/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.49  --bmc1_ucm_relax_model                  4
% 8.00/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.49  --bmc1_ucm_layered_model                none
% 8.00/1.49  --bmc1_ucm_max_lemma_size               10
% 8.00/1.49  
% 8.00/1.49  ------ AIG Options
% 8.00/1.49  
% 8.00/1.49  --aig_mode                              false
% 8.00/1.49  
% 8.00/1.49  ------ Instantiation Options
% 8.00/1.49  
% 8.00/1.49  --instantiation_flag                    true
% 8.00/1.49  --inst_sos_flag                         true
% 8.00/1.49  --inst_sos_phase                        true
% 8.00/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.49  --inst_lit_sel_side                     num_symb
% 8.00/1.49  --inst_solver_per_active                1400
% 8.00/1.49  --inst_solver_calls_frac                1.
% 8.00/1.49  --inst_passive_queue_type               priority_queues
% 8.00/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.49  --inst_passive_queues_freq              [25;2]
% 8.00/1.49  --inst_dismatching                      true
% 8.00/1.49  --inst_eager_unprocessed_to_passive     true
% 8.00/1.49  --inst_prop_sim_given                   true
% 8.00/1.49  --inst_prop_sim_new                     false
% 8.00/1.49  --inst_subs_new                         false
% 8.00/1.49  --inst_eq_res_simp                      false
% 8.00/1.49  --inst_subs_given                       false
% 8.00/1.49  --inst_orphan_elimination               true
% 8.00/1.49  --inst_learning_loop_flag               true
% 8.00/1.49  --inst_learning_start                   3000
% 8.00/1.49  --inst_learning_factor                  2
% 8.00/1.49  --inst_start_prop_sim_after_learn       3
% 8.00/1.49  --inst_sel_renew                        solver
% 8.00/1.49  --inst_lit_activity_flag                true
% 8.00/1.49  --inst_restr_to_given                   false
% 8.00/1.49  --inst_activity_threshold               500
% 8.00/1.49  --inst_out_proof                        true
% 8.00/1.49  
% 8.00/1.49  ------ Resolution Options
% 8.00/1.49  
% 8.00/1.49  --resolution_flag                       true
% 8.00/1.49  --res_lit_sel                           adaptive
% 8.00/1.49  --res_lit_sel_side                      none
% 8.00/1.49  --res_ordering                          kbo
% 8.00/1.49  --res_to_prop_solver                    active
% 8.00/1.49  --res_prop_simpl_new                    false
% 8.00/1.49  --res_prop_simpl_given                  true
% 8.00/1.49  --res_passive_queue_type                priority_queues
% 8.00/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.49  --res_passive_queues_freq               [15;5]
% 8.00/1.49  --res_forward_subs                      full
% 8.00/1.49  --res_backward_subs                     full
% 8.00/1.49  --res_forward_subs_resolution           true
% 8.00/1.49  --res_backward_subs_resolution          true
% 8.00/1.49  --res_orphan_elimination                true
% 8.00/1.49  --res_time_limit                        2.
% 8.00/1.49  --res_out_proof                         true
% 8.00/1.49  
% 8.00/1.49  ------ Superposition Options
% 8.00/1.49  
% 8.00/1.49  --superposition_flag                    true
% 8.00/1.49  --sup_passive_queue_type                priority_queues
% 8.00/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.49  --demod_completeness_check              fast
% 8.00/1.49  --demod_use_ground                      true
% 8.00/1.49  --sup_to_prop_solver                    passive
% 8.00/1.49  --sup_prop_simpl_new                    true
% 8.00/1.49  --sup_prop_simpl_given                  true
% 8.00/1.49  --sup_fun_splitting                     true
% 8.00/1.49  --sup_smt_interval                      50000
% 8.00/1.49  
% 8.00/1.49  ------ Superposition Simplification Setup
% 8.00/1.49  
% 8.00/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.49  --sup_immed_triv                        [TrivRules]
% 8.00/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.49  --sup_immed_bw_main                     []
% 8.00/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.49  --sup_input_bw                          []
% 8.00/1.49  
% 8.00/1.49  ------ Combination Options
% 8.00/1.49  
% 8.00/1.49  --comb_res_mult                         3
% 8.00/1.49  --comb_sup_mult                         2
% 8.00/1.49  --comb_inst_mult                        10
% 8.00/1.49  
% 8.00/1.49  ------ Debug Options
% 8.00/1.49  
% 8.00/1.49  --dbg_backtrace                         false
% 8.00/1.49  --dbg_dump_prop_clauses                 false
% 8.00/1.49  --dbg_dump_prop_clauses_file            -
% 8.00/1.49  --dbg_out_stat                          false
% 8.00/1.49  ------ Parsing...
% 8.00/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.49  ------ Proving...
% 8.00/1.49  ------ Problem Properties 
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  clauses                                 43
% 8.00/1.49  conjectures                             10
% 8.00/1.49  EPR                                     13
% 8.00/1.49  Horn                                    32
% 8.00/1.49  unary                                   13
% 8.00/1.49  binary                                  10
% 8.00/1.49  lits                                    120
% 8.00/1.49  lits eq                                 26
% 8.00/1.49  fd_pure                                 0
% 8.00/1.49  fd_pseudo                               0
% 8.00/1.49  fd_cond                                 6
% 8.00/1.49  fd_pseudo_cond                          3
% 8.00/1.49  AC symbols                              0
% 8.00/1.49  
% 8.00/1.49  ------ Schedule dynamic 5 is on 
% 8.00/1.49  
% 8.00/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  ------ 
% 8.00/1.49  Current options:
% 8.00/1.49  ------ 
% 8.00/1.49  
% 8.00/1.49  ------ Input Options
% 8.00/1.49  
% 8.00/1.49  --out_options                           all
% 8.00/1.49  --tptp_safe_out                         true
% 8.00/1.49  --problem_path                          ""
% 8.00/1.49  --include_path                          ""
% 8.00/1.49  --clausifier                            res/vclausify_rel
% 8.00/1.49  --clausifier_options                    ""
% 8.00/1.49  --stdin                                 false
% 8.00/1.49  --stats_out                             all
% 8.00/1.49  
% 8.00/1.49  ------ General Options
% 8.00/1.49  
% 8.00/1.49  --fof                                   false
% 8.00/1.49  --time_out_real                         305.
% 8.00/1.49  --time_out_virtual                      -1.
% 8.00/1.49  --symbol_type_check                     false
% 8.00/1.49  --clausify_out                          false
% 8.00/1.49  --sig_cnt_out                           false
% 8.00/1.49  --trig_cnt_out                          false
% 8.00/1.49  --trig_cnt_out_tolerance                1.
% 8.00/1.49  --trig_cnt_out_sk_spl                   false
% 8.00/1.49  --abstr_cl_out                          false
% 8.00/1.49  
% 8.00/1.49  ------ Global Options
% 8.00/1.49  
% 8.00/1.49  --schedule                              default
% 8.00/1.49  --add_important_lit                     false
% 8.00/1.49  --prop_solver_per_cl                    1000
% 8.00/1.49  --min_unsat_core                        false
% 8.00/1.49  --soft_assumptions                      false
% 8.00/1.49  --soft_lemma_size                       3
% 8.00/1.49  --prop_impl_unit_size                   0
% 8.00/1.49  --prop_impl_unit                        []
% 8.00/1.49  --share_sel_clauses                     true
% 8.00/1.49  --reset_solvers                         false
% 8.00/1.49  --bc_imp_inh                            [conj_cone]
% 8.00/1.49  --conj_cone_tolerance                   3.
% 8.00/1.49  --extra_neg_conj                        none
% 8.00/1.49  --large_theory_mode                     true
% 8.00/1.49  --prolific_symb_bound                   200
% 8.00/1.49  --lt_threshold                          2000
% 8.00/1.49  --clause_weak_htbl                      true
% 8.00/1.49  --gc_record_bc_elim                     false
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing Options
% 8.00/1.49  
% 8.00/1.49  --preprocessing_flag                    true
% 8.00/1.49  --time_out_prep_mult                    0.1
% 8.00/1.49  --splitting_mode                        input
% 8.00/1.49  --splitting_grd                         true
% 8.00/1.49  --splitting_cvd                         false
% 8.00/1.49  --splitting_cvd_svl                     false
% 8.00/1.49  --splitting_nvd                         32
% 8.00/1.49  --sub_typing                            true
% 8.00/1.49  --prep_gs_sim                           true
% 8.00/1.49  --prep_unflatten                        true
% 8.00/1.49  --prep_res_sim                          true
% 8.00/1.49  --prep_upred                            true
% 8.00/1.49  --prep_sem_filter                       exhaustive
% 8.00/1.49  --prep_sem_filter_out                   false
% 8.00/1.49  --pred_elim                             true
% 8.00/1.49  --res_sim_input                         true
% 8.00/1.49  --eq_ax_congr_red                       true
% 8.00/1.49  --pure_diseq_elim                       true
% 8.00/1.49  --brand_transform                       false
% 8.00/1.49  --non_eq_to_eq                          false
% 8.00/1.49  --prep_def_merge                        true
% 8.00/1.49  --prep_def_merge_prop_impl              false
% 8.00/1.49  --prep_def_merge_mbd                    true
% 8.00/1.49  --prep_def_merge_tr_red                 false
% 8.00/1.49  --prep_def_merge_tr_cl                  false
% 8.00/1.49  --smt_preprocessing                     true
% 8.00/1.49  --smt_ac_axioms                         fast
% 8.00/1.49  --preprocessed_out                      false
% 8.00/1.49  --preprocessed_stats                    false
% 8.00/1.49  
% 8.00/1.49  ------ Abstraction refinement Options
% 8.00/1.49  
% 8.00/1.49  --abstr_ref                             []
% 8.00/1.49  --abstr_ref_prep                        false
% 8.00/1.49  --abstr_ref_until_sat                   false
% 8.00/1.49  --abstr_ref_sig_restrict                funpre
% 8.00/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.49  --abstr_ref_under                       []
% 8.00/1.49  
% 8.00/1.49  ------ SAT Options
% 8.00/1.49  
% 8.00/1.49  --sat_mode                              false
% 8.00/1.49  --sat_fm_restart_options                ""
% 8.00/1.49  --sat_gr_def                            false
% 8.00/1.49  --sat_epr_types                         true
% 8.00/1.49  --sat_non_cyclic_types                  false
% 8.00/1.49  --sat_finite_models                     false
% 8.00/1.49  --sat_fm_lemmas                         false
% 8.00/1.49  --sat_fm_prep                           false
% 8.00/1.49  --sat_fm_uc_incr                        true
% 8.00/1.49  --sat_out_model                         small
% 8.00/1.49  --sat_out_clauses                       false
% 8.00/1.49  
% 8.00/1.49  ------ QBF Options
% 8.00/1.49  
% 8.00/1.49  --qbf_mode                              false
% 8.00/1.49  --qbf_elim_univ                         false
% 8.00/1.49  --qbf_dom_inst                          none
% 8.00/1.49  --qbf_dom_pre_inst                      false
% 8.00/1.49  --qbf_sk_in                             false
% 8.00/1.49  --qbf_pred_elim                         true
% 8.00/1.49  --qbf_split                             512
% 8.00/1.49  
% 8.00/1.49  ------ BMC1 Options
% 8.00/1.49  
% 8.00/1.49  --bmc1_incremental                      false
% 8.00/1.49  --bmc1_axioms                           reachable_all
% 8.00/1.49  --bmc1_min_bound                        0
% 8.00/1.49  --bmc1_max_bound                        -1
% 8.00/1.49  --bmc1_max_bound_default                -1
% 8.00/1.49  --bmc1_symbol_reachability              true
% 8.00/1.49  --bmc1_property_lemmas                  false
% 8.00/1.49  --bmc1_k_induction                      false
% 8.00/1.49  --bmc1_non_equiv_states                 false
% 8.00/1.49  --bmc1_deadlock                         false
% 8.00/1.49  --bmc1_ucm                              false
% 8.00/1.49  --bmc1_add_unsat_core                   none
% 8.00/1.49  --bmc1_unsat_core_children              false
% 8.00/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.49  --bmc1_out_stat                         full
% 8.00/1.49  --bmc1_ground_init                      false
% 8.00/1.49  --bmc1_pre_inst_next_state              false
% 8.00/1.49  --bmc1_pre_inst_state                   false
% 8.00/1.49  --bmc1_pre_inst_reach_state             false
% 8.00/1.49  --bmc1_out_unsat_core                   false
% 8.00/1.49  --bmc1_aig_witness_out                  false
% 8.00/1.49  --bmc1_verbose                          false
% 8.00/1.49  --bmc1_dump_clauses_tptp                false
% 8.00/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.49  --bmc1_dump_file                        -
% 8.00/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.49  --bmc1_ucm_extend_mode                  1
% 8.00/1.49  --bmc1_ucm_init_mode                    2
% 8.00/1.49  --bmc1_ucm_cone_mode                    none
% 8.00/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.49  --bmc1_ucm_relax_model                  4
% 8.00/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.49  --bmc1_ucm_layered_model                none
% 8.00/1.49  --bmc1_ucm_max_lemma_size               10
% 8.00/1.49  
% 8.00/1.49  ------ AIG Options
% 8.00/1.49  
% 8.00/1.49  --aig_mode                              false
% 8.00/1.49  
% 8.00/1.49  ------ Instantiation Options
% 8.00/1.49  
% 8.00/1.49  --instantiation_flag                    true
% 8.00/1.49  --inst_sos_flag                         true
% 8.00/1.49  --inst_sos_phase                        true
% 8.00/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.49  --inst_lit_sel_side                     none
% 8.00/1.49  --inst_solver_per_active                1400
% 8.00/1.49  --inst_solver_calls_frac                1.
% 8.00/1.49  --inst_passive_queue_type               priority_queues
% 8.00/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.49  --inst_passive_queues_freq              [25;2]
% 8.00/1.49  --inst_dismatching                      true
% 8.00/1.49  --inst_eager_unprocessed_to_passive     true
% 8.00/1.49  --inst_prop_sim_given                   true
% 8.00/1.49  --inst_prop_sim_new                     false
% 8.00/1.49  --inst_subs_new                         false
% 8.00/1.49  --inst_eq_res_simp                      false
% 8.00/1.49  --inst_subs_given                       false
% 8.00/1.49  --inst_orphan_elimination               true
% 8.00/1.49  --inst_learning_loop_flag               true
% 8.00/1.49  --inst_learning_start                   3000
% 8.00/1.49  --inst_learning_factor                  2
% 8.00/1.49  --inst_start_prop_sim_after_learn       3
% 8.00/1.49  --inst_sel_renew                        solver
% 8.00/1.49  --inst_lit_activity_flag                true
% 8.00/1.49  --inst_restr_to_given                   false
% 8.00/1.49  --inst_activity_threshold               500
% 8.00/1.49  --inst_out_proof                        true
% 8.00/1.49  
% 8.00/1.49  ------ Resolution Options
% 8.00/1.49  
% 8.00/1.49  --resolution_flag                       false
% 8.00/1.49  --res_lit_sel                           adaptive
% 8.00/1.49  --res_lit_sel_side                      none
% 8.00/1.49  --res_ordering                          kbo
% 8.00/1.49  --res_to_prop_solver                    active
% 8.00/1.49  --res_prop_simpl_new                    false
% 8.00/1.49  --res_prop_simpl_given                  true
% 8.00/1.49  --res_passive_queue_type                priority_queues
% 8.00/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.49  --res_passive_queues_freq               [15;5]
% 8.00/1.49  --res_forward_subs                      full
% 8.00/1.49  --res_backward_subs                     full
% 8.00/1.49  --res_forward_subs_resolution           true
% 8.00/1.49  --res_backward_subs_resolution          true
% 8.00/1.49  --res_orphan_elimination                true
% 8.00/1.49  --res_time_limit                        2.
% 8.00/1.49  --res_out_proof                         true
% 8.00/1.49  
% 8.00/1.49  ------ Superposition Options
% 8.00/1.49  
% 8.00/1.49  --superposition_flag                    true
% 8.00/1.49  --sup_passive_queue_type                priority_queues
% 8.00/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.49  --demod_completeness_check              fast
% 8.00/1.49  --demod_use_ground                      true
% 8.00/1.49  --sup_to_prop_solver                    passive
% 8.00/1.49  --sup_prop_simpl_new                    true
% 8.00/1.49  --sup_prop_simpl_given                  true
% 8.00/1.49  --sup_fun_splitting                     true
% 8.00/1.49  --sup_smt_interval                      50000
% 8.00/1.49  
% 8.00/1.49  ------ Superposition Simplification Setup
% 8.00/1.49  
% 8.00/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.49  --sup_immed_triv                        [TrivRules]
% 8.00/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.49  --sup_immed_bw_main                     []
% 8.00/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.49  --sup_input_bw                          []
% 8.00/1.49  
% 8.00/1.49  ------ Combination Options
% 8.00/1.49  
% 8.00/1.49  --comb_res_mult                         3
% 8.00/1.49  --comb_sup_mult                         2
% 8.00/1.49  --comb_inst_mult                        10
% 8.00/1.49  
% 8.00/1.49  ------ Debug Options
% 8.00/1.49  
% 8.00/1.49  --dbg_backtrace                         false
% 8.00/1.49  --dbg_dump_prop_clauses                 false
% 8.00/1.49  --dbg_dump_prop_clauses_file            -
% 8.00/1.49  --dbg_out_stat                          false
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  ------ Proving...
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  % SZS status Theorem for theBenchmark.p
% 8.00/1.49  
% 8.00/1.49   Resolution empty clause
% 8.00/1.49  
% 8.00/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  fof(f20,conjecture,(
% 8.00/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f21,negated_conjecture,(
% 8.00/1.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 8.00/1.49    inference(negated_conjecture,[],[f20])).
% 8.00/1.49  
% 8.00/1.49  fof(f46,plain,(
% 8.00/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 8.00/1.49    inference(ennf_transformation,[],[f21])).
% 8.00/1.49  
% 8.00/1.49  fof(f47,plain,(
% 8.00/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 8.00/1.49    inference(flattening,[],[f46])).
% 8.00/1.49  
% 8.00/1.49  fof(f69,plain,(
% 8.00/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK11) != k7_partfun1(X0,X4,k1_funct_1(X3,sK11)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK11,X1))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f68,plain,(
% 8.00/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK10),X5) != k7_partfun1(X0,sK10,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK10)) & m1_subset_1(X5,X1)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK10))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f67,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK9,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK9,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK9),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK9,X1,X2) & v1_funct_1(sK9))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f66,plain,(
% 8.00/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(X3,sK7,sK8) & v1_funct_1(X3)) & ~v1_xboole_0(sK8))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f70,plain,(
% 8.00/1.49    (((k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(sK11,sK7)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)) & ~v1_xboole_0(sK8)),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f47,f69,f68,f67,f66])).
% 8.00/1.49  
% 8.00/1.49  fof(f110,plain,(
% 8.00/1.49    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f13,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f34,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f13])).
% 8.00/1.49  
% 8.00/1.49  fof(f93,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f34])).
% 8.00/1.49  
% 8.00/1.49  fof(f108,plain,(
% 8.00/1.49    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f14,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f35,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f14])).
% 8.00/1.49  
% 8.00/1.49  fof(f94,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f35])).
% 8.00/1.49  
% 8.00/1.49  fof(f15,axiom,(
% 8.00/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f36,plain,(
% 8.00/1.49    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 8.00/1.49    inference(ennf_transformation,[],[f15])).
% 8.00/1.49  
% 8.00/1.49  fof(f37,plain,(
% 8.00/1.49    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 8.00/1.49    inference(flattening,[],[f36])).
% 8.00/1.49  
% 8.00/1.49  fof(f95,plain,(
% 8.00/1.49    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f37])).
% 8.00/1.49  
% 8.00/1.49  fof(f105,plain,(
% 8.00/1.49    ~v1_xboole_0(sK8)),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f106,plain,(
% 8.00/1.49    v1_funct_1(sK9)),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f107,plain,(
% 8.00/1.49    v1_funct_2(sK9,sK7,sK8)),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f5,axiom,(
% 8.00/1.49    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f56,plain,(
% 8.00/1.49    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0))))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f57,plain,(
% 8.00/1.49    ! [X0] : (v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)))),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f56])).
% 8.00/1.49  
% 8.00/1.49  fof(f79,plain,(
% 8.00/1.49    ( ! [X0] : (v1_xboole_0(sK2(X0))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f57])).
% 8.00/1.49  
% 8.00/1.49  fof(f3,axiom,(
% 8.00/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f24,plain,(
% 8.00/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 8.00/1.49    inference(ennf_transformation,[],[f3])).
% 8.00/1.49  
% 8.00/1.49  fof(f76,plain,(
% 8.00/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f24])).
% 8.00/1.49  
% 8.00/1.49  fof(f18,axiom,(
% 8.00/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f42,plain,(
% 8.00/1.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.00/1.49    inference(ennf_transformation,[],[f18])).
% 8.00/1.49  
% 8.00/1.49  fof(f43,plain,(
% 8.00/1.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.00/1.49    inference(flattening,[],[f42])).
% 8.00/1.49  
% 8.00/1.49  fof(f103,plain,(
% 8.00/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f43])).
% 8.00/1.49  
% 8.00/1.49  fof(f109,plain,(
% 8.00/1.49    v1_funct_1(sK10)),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f112,plain,(
% 8.00/1.49    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f111,plain,(
% 8.00/1.49    m1_subset_1(sK11,sK7)),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f6,axiom,(
% 8.00/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f27,plain,(
% 8.00/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 8.00/1.49    inference(ennf_transformation,[],[f6])).
% 8.00/1.49  
% 8.00/1.49  fof(f28,plain,(
% 8.00/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 8.00/1.49    inference(flattening,[],[f27])).
% 8.00/1.49  
% 8.00/1.49  fof(f80,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f28])).
% 8.00/1.49  
% 8.00/1.49  fof(f113,plain,(
% 8.00/1.49    k1_xboole_0 != sK7),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f10,axiom,(
% 8.00/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f30,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.00/1.49    inference(ennf_transformation,[],[f10])).
% 8.00/1.49  
% 8.00/1.49  fof(f31,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(flattening,[],[f30])).
% 8.00/1.49  
% 8.00/1.49  fof(f59,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(nnf_transformation,[],[f31])).
% 8.00/1.49  
% 8.00/1.49  fof(f60,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(rectify,[],[f59])).
% 8.00/1.49  
% 8.00/1.49  fof(f63,plain,(
% 8.00/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f62,plain,(
% 8.00/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f61,plain,(
% 8.00/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f64,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f60,f63,f62,f61])).
% 8.00/1.49  
% 8.00/1.49  fof(f87,plain,(
% 8.00/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f64])).
% 8.00/1.49  
% 8.00/1.49  fof(f115,plain,(
% 8.00/1.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(equality_resolution,[],[f87])).
% 8.00/1.49  
% 8.00/1.49  fof(f116,plain,(
% 8.00/1.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(equality_resolution,[],[f115])).
% 8.00/1.49  
% 8.00/1.49  fof(f2,axiom,(
% 8.00/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f23,plain,(
% 8.00/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 8.00/1.49    inference(ennf_transformation,[],[f2])).
% 8.00/1.49  
% 8.00/1.49  fof(f52,plain,(
% 8.00/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 8.00/1.49    inference(nnf_transformation,[],[f23])).
% 8.00/1.49  
% 8.00/1.49  fof(f53,plain,(
% 8.00/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.00/1.49    inference(rectify,[],[f52])).
% 8.00/1.49  
% 8.00/1.49  fof(f54,plain,(
% 8.00/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f55,plain,(
% 8.00/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 8.00/1.49  
% 8.00/1.49  fof(f73,plain,(
% 8.00/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f55])).
% 8.00/1.49  
% 8.00/1.49  fof(f9,axiom,(
% 8.00/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f84,plain,(
% 8.00/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f9])).
% 8.00/1.49  
% 8.00/1.49  fof(f7,axiom,(
% 8.00/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f58,plain,(
% 8.00/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.00/1.49    inference(nnf_transformation,[],[f7])).
% 8.00/1.49  
% 8.00/1.49  fof(f81,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f58])).
% 8.00/1.49  
% 8.00/1.49  fof(f8,axiom,(
% 8.00/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f29,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.00/1.49    inference(ennf_transformation,[],[f8])).
% 8.00/1.49  
% 8.00/1.49  fof(f83,plain,(
% 8.00/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f29])).
% 8.00/1.49  
% 8.00/1.49  fof(f82,plain,(
% 8.00/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f58])).
% 8.00/1.49  
% 8.00/1.49  fof(f16,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f38,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f16])).
% 8.00/1.49  
% 8.00/1.49  fof(f39,plain,(
% 8.00/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(flattening,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f65,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(nnf_transformation,[],[f39])).
% 8.00/1.49  
% 8.00/1.49  fof(f96,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f65])).
% 8.00/1.49  
% 8.00/1.49  fof(f12,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f22,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 8.00/1.49    inference(pure_predicate_removal,[],[f12])).
% 8.00/1.49  
% 8.00/1.49  fof(f33,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.49    inference(ennf_transformation,[],[f22])).
% 8.00/1.49  
% 8.00/1.49  fof(f92,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f33])).
% 8.00/1.49  
% 8.00/1.49  fof(f17,axiom,(
% 8.00/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f40,plain,(
% 8.00/1.49    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 8.00/1.49    inference(ennf_transformation,[],[f17])).
% 8.00/1.49  
% 8.00/1.49  fof(f41,plain,(
% 8.00/1.49    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.00/1.49    inference(flattening,[],[f40])).
% 8.00/1.49  
% 8.00/1.49  fof(f102,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f41])).
% 8.00/1.49  
% 8.00/1.49  fof(f114,plain,(
% 8.00/1.49    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))),
% 8.00/1.49    inference(cnf_transformation,[],[f70])).
% 8.00/1.49  
% 8.00/1.49  fof(f19,axiom,(
% 8.00/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1))))),
% 8.00/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f44,plain,(
% 8.00/1.49    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 8.00/1.49    inference(ennf_transformation,[],[f19])).
% 8.00/1.49  
% 8.00/1.49  fof(f45,plain,(
% 8.00/1.49    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 8.00/1.49    inference(flattening,[],[f44])).
% 8.00/1.49  
% 8.00/1.49  fof(f104,plain,(
% 8.00/1.49    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f45])).
% 8.00/1.49  
% 8.00/1.49  cnf(c_38,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
% 8.00/1.49      inference(cnf_transformation,[],[f110]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2534,plain,
% 8.00/1.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_22,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f93]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2547,plain,
% 8.00/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4883,plain,
% 8.00/1.49      ( k1_relset_1(sK8,sK6,sK10) = k1_relat_1(sK10) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2534,c_2547]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_40,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 8.00/1.49      inference(cnf_transformation,[],[f108]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2532,plain,
% 8.00/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_23,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f94]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2546,plain,
% 8.00/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4424,plain,
% 8.00/1.49      ( k2_relset_1(sK7,sK8,sK9) = k2_relat_1(sK9) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2532,c_2546]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_24,plain,
% 8.00/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.00/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 8.00/1.49      | ~ v1_funct_1(X3)
% 8.00/1.49      | ~ v1_funct_1(X0)
% 8.00/1.49      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 8.00/1.49      | k1_xboole_0 = X2 ),
% 8.00/1.49      inference(cnf_transformation,[],[f95]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2545,plain,
% 8.00/1.49      ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
% 8.00/1.49      | k1_xboole_0 = X1
% 8.00/1.49      | v1_funct_2(X3,X0,X1) != iProver_top
% 8.00/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 8.00/1.49      | v1_funct_1(X3) != iProver_top
% 8.00/1.49      | v1_funct_1(X4) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6662,plain,
% 8.00/1.49      ( k1_partfun1(sK7,sK8,sK8,X0,sK9,X1) = k8_funct_2(sK7,sK8,X0,sK9,X1)
% 8.00/1.49      | sK8 = k1_xboole_0
% 8.00/1.49      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 8.00/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK8,X0))) != iProver_top
% 8.00/1.49      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,X0,X1)) != iProver_top
% 8.00/1.49      | v1_funct_1(X1) != iProver_top
% 8.00/1.49      | v1_funct_1(sK9) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_4424,c_2545]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_43,negated_conjecture,
% 8.00/1.49      ( ~ v1_xboole_0(sK8) ),
% 8.00/1.49      inference(cnf_transformation,[],[f105]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_44,plain,
% 8.00/1.49      ( v1_xboole_0(sK8) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_42,negated_conjecture,
% 8.00/1.49      ( v1_funct_1(sK9) ),
% 8.00/1.49      inference(cnf_transformation,[],[f106]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_45,plain,
% 8.00/1.49      ( v1_funct_1(sK9) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_41,negated_conjecture,
% 8.00/1.49      ( v1_funct_2(sK9,sK7,sK8) ),
% 8.00/1.49      inference(cnf_transformation,[],[f107]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_46,plain,
% 8.00/1.49      ( v1_funct_2(sK9,sK7,sK8) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_47,plain,
% 8.00/1.49      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1625,plain,
% 8.00/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 8.00/1.49      theory(equality) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2656,plain,
% 8.00/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1625]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2660,plain,
% 8.00/1.49      ( sK8 != X0
% 8.00/1.49      | v1_xboole_0(X0) != iProver_top
% 8.00/1.49      | v1_xboole_0(sK8) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2656]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2662,plain,
% 8.00/1.49      ( sK8 != k1_xboole_0
% 8.00/1.49      | v1_xboole_0(sK8) = iProver_top
% 8.00/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_2660]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_7,plain,
% 8.00/1.49      ( v1_xboole_0(sK2(X0)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f79]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2560,plain,
% 8.00/1.49      ( v1_xboole_0(sK2(X0)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5,plain,
% 8.00/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 8.00/1.49      inference(cnf_transformation,[],[f76]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2562,plain,
% 8.00/1.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3337,plain,
% 8.00/1.49      ( sK2(X0) = k1_xboole_0 ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2560,c_2562]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3340,plain,
% 8.00/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_3337,c_2560]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31890,plain,
% 8.00/1.49      ( v1_funct_1(X1) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,X0,X1)) != iProver_top
% 8.00/1.49      | k1_partfun1(sK7,sK8,sK8,X0,sK9,X1) = k8_funct_2(sK7,sK8,X0,sK9,X1)
% 8.00/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK8,X0))) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_6662,c_44,c_45,c_46,c_47,c_2662,c_3340]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31891,plain,
% 8.00/1.49      ( k1_partfun1(sK7,sK8,sK8,X0,sK9,X1) = k8_funct_2(sK7,sK8,X0,sK9,X1)
% 8.00/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK8,X0))) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,X0,X1)) != iProver_top
% 8.00/1.49      | v1_funct_1(X1) != iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_31890]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31902,plain,
% 8.00/1.49      ( k1_partfun1(sK7,sK8,sK8,sK6,sK9,sK10) = k8_funct_2(sK7,sK8,sK6,sK9,sK10)
% 8.00/1.49      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) != iProver_top
% 8.00/1.49      | v1_funct_1(sK10) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_4883,c_31891]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.00/1.49      | ~ v1_funct_1(X3)
% 8.00/1.49      | ~ v1_funct_1(X0)
% 8.00/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f103]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2538,plain,
% 8.00/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 8.00/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 8.00/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.49      | v1_funct_1(X5) != iProver_top
% 8.00/1.49      | v1_funct_1(X4) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4870,plain,
% 8.00/1.49      ( k1_partfun1(X0,X1,sK8,sK6,X2,sK10) = k5_relat_1(X2,sK10)
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.49      | v1_funct_1(X2) != iProver_top
% 8.00/1.49      | v1_funct_1(sK10) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2534,c_2538]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_39,negated_conjecture,
% 8.00/1.49      ( v1_funct_1(sK10) ),
% 8.00/1.49      inference(cnf_transformation,[],[f109]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_48,plain,
% 8.00/1.49      ( v1_funct_1(sK10) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5170,plain,
% 8.00/1.49      ( v1_funct_1(X2) != iProver_top
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.49      | k1_partfun1(X0,X1,sK8,sK6,X2,sK10) = k5_relat_1(X2,sK10) ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4870,c_48]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5171,plain,
% 8.00/1.49      ( k1_partfun1(X0,X1,sK8,sK6,X2,sK10) = k5_relat_1(X2,sK10)
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.49      | v1_funct_1(X2) != iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_5170]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5178,plain,
% 8.00/1.49      ( k1_partfun1(sK7,sK8,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10)
% 8.00/1.49      | v1_funct_1(sK9) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2532,c_5171]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5407,plain,
% 8.00/1.49      ( k1_partfun1(sK7,sK8,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10) ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5178,c_45]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31904,plain,
% 8.00/1.49      ( k8_funct_2(sK7,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10)
% 8.00/1.49      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
% 8.00/1.49      | r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) != iProver_top
% 8.00/1.49      | v1_funct_1(sK10) != iProver_top ),
% 8.00/1.49      inference(light_normalisation,[status(thm)],[c_31902,c_5407]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_49,plain,
% 8.00/1.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_36,negated_conjecture,
% 8.00/1.49      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f112]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2536,plain,
% 8.00/1.49      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4540,plain,
% 8.00/1.49      ( r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_4424,c_2536]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5072,plain,
% 8.00/1.49      ( r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) = iProver_top ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_4883,c_4540]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32200,plain,
% 8.00/1.49      ( k8_funct_2(sK7,sK8,sK6,sK9,sK10) = k5_relat_1(sK9,sK10) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_31904,c_48,c_49,c_5072]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_37,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK11,sK7) ),
% 8.00/1.49      inference(cnf_transformation,[],[f111]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2535,plain,
% 8.00/1.49      ( m1_subset_1(sK11,sK7) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_9,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f80]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2558,plain,
% 8.00/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 8.00/1.49      | r2_hidden(X0,X1) = iProver_top
% 8.00/1.49      | v1_xboole_0(X1) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4984,plain,
% 8.00/1.49      ( r2_hidden(sK11,sK7) = iProver_top | v1_xboole_0(sK7) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2535,c_2558]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_50,plain,
% 8.00/1.49      ( m1_subset_1(sK11,sK7) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_35,negated_conjecture,
% 8.00/1.49      ( k1_xboole_0 != sK7 ),
% 8.00/1.49      inference(cnf_transformation,[],[f113]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2620,plain,
% 8.00/1.49      ( ~ v1_xboole_0(sK7) | k1_xboole_0 = sK7 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2621,plain,
% 8.00/1.49      ( k1_xboole_0 = sK7 | v1_xboole_0(sK7) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2620]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2687,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK7) | v1_xboole_0(sK7) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2907,plain,
% 8.00/1.49      ( ~ m1_subset_1(sK11,sK7) | r2_hidden(sK11,sK7) | v1_xboole_0(sK7) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_2687]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2908,plain,
% 8.00/1.49      ( m1_subset_1(sK11,sK7) != iProver_top
% 8.00/1.49      | r2_hidden(sK11,sK7) = iProver_top
% 8.00/1.49      | v1_xboole_0(sK7) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2907]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5722,plain,
% 8.00/1.49      ( r2_hidden(sK11,sK7) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_4984,c_50,c_35,c_2621,c_2908]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_17,plain,
% 8.00/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 8.00/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 8.00/1.49      | ~ v1_funct_1(X1)
% 8.00/1.49      | ~ v1_relat_1(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f116]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2551,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 8.00/1.49      | v1_funct_1(X1) != iProver_top
% 8.00/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4,plain,
% 8.00/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2563,plain,
% 8.00/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.00/1.49      | r2_hidden(X2,X0) != iProver_top
% 8.00/1.49      | r2_hidden(X2,X1) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5059,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relset_1(sK8,sK6,sK10)) = iProver_top
% 8.00/1.49      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_4540,c_2563]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5060,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relat_1(sK10)) = iProver_top
% 8.00/1.49      | r2_hidden(X0,k2_relat_1(sK9)) != iProver_top ),
% 8.00/1.49      inference(light_normalisation,[status(thm)],[c_5059,c_4883]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6595,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top
% 8.00/1.49      | v1_funct_1(sK9) != iProver_top
% 8.00/1.49      | v1_relat_1(sK9) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2551,c_5060]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13,plain,
% 8.00/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f84]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2555,plain,
% 8.00/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_11,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f81]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2556,plain,
% 8.00/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.00/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3681,plain,
% 8.00/1.49      ( r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2532,c_2556]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f83]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10,plain,
% 8.00/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f82]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_328,plain,
% 8.00/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.00/1.49      inference(prop_impl,[status(thm)],[c_10]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_329,plain,
% 8.00/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_328]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_415,plain,
% 8.00/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 8.00/1.49      inference(bin_hyper_res,[status(thm)],[c_12,c_329]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2528,plain,
% 8.00/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.00/1.49      | v1_relat_1(X1) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3790,plain,
% 8.00/1.49      ( v1_relat_1(k2_zfmisc_1(sK7,sK8)) != iProver_top
% 8.00/1.49      | v1_relat_1(sK9) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_3681,c_2528]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4112,plain,
% 8.00/1.49      ( v1_relat_1(sK9) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2555,c_3790]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_29558,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relat_1(sK9)) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_6595,c_45,c_4112]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_30,plain,
% 8.00/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | k1_relset_1(X1,X2,X0) = X1
% 8.00/1.49      | k1_xboole_0 = X2 ),
% 8.00/1.49      inference(cnf_transformation,[],[f96]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2539,plain,
% 8.00/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 8.00/1.49      | k1_xboole_0 = X1
% 8.00/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.00/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5594,plain,
% 8.00/1.49      ( k1_relset_1(sK7,sK8,sK9) = sK7
% 8.00/1.49      | sK8 = k1_xboole_0
% 8.00/1.49      | v1_funct_2(sK9,sK7,sK8) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2532,c_2539]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4884,plain,
% 8.00/1.49      ( k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2532,c_2547]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5597,plain,
% 8.00/1.49      ( k1_relat_1(sK9) = sK7
% 8.00/1.49      | sK8 = k1_xboole_0
% 8.00/1.49      | v1_funct_2(sK9,sK7,sK8) != iProver_top ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_5594,c_4884]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8280,plain,
% 8.00/1.49      ( k1_relat_1(sK9) = sK7 ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_5597,c_44,c_46,c_2662,c_3340]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_29564,plain,
% 8.00/1.49      ( r2_hidden(X0,sK7) != iProver_top
% 8.00/1.49      | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
% 8.00/1.49      inference(light_normalisation,[status(thm)],[c_29558,c_8280]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_21,plain,
% 8.00/1.49      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 8.00/1.49      inference(cnf_transformation,[],[f92]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31,plain,
% 8.00/1.49      ( ~ v5_relat_1(X0,X1)
% 8.00/1.49      | ~ r2_hidden(X2,k1_relat_1(X0))
% 8.00/1.49      | ~ v1_funct_1(X0)
% 8.00/1.49      | ~ v1_relat_1(X0)
% 8.00/1.49      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 8.00/1.49      inference(cnf_transformation,[],[f102]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_559,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | ~ r2_hidden(X3,k1_relat_1(X0))
% 8.00/1.49      | ~ v1_funct_1(X0)
% 8.00/1.49      | ~ v1_relat_1(X0)
% 8.00/1.49      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 8.00/1.49      inference(resolution,[status(thm)],[c_21,c_31]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2527,plain,
% 8.00/1.49      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 8.00/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 8.00/1.49      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 8.00/1.49      | v1_funct_1(X1) != iProver_top
% 8.00/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3216,plain,
% 8.00/1.49      ( k7_partfun1(sK6,sK10,X0) = k1_funct_1(sK10,X0)
% 8.00/1.49      | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 8.00/1.49      | v1_funct_1(sK10) != iProver_top
% 8.00/1.49      | v1_relat_1(sK10) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2534,c_2527]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3299,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 8.00/1.49      | k7_partfun1(sK6,sK10,X0) = k1_funct_1(sK10,X0)
% 8.00/1.49      | v1_relat_1(sK10) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3216,c_48]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3300,plain,
% 8.00/1.49      ( k7_partfun1(sK6,sK10,X0) = k1_funct_1(sK10,X0)
% 8.00/1.49      | r2_hidden(X0,k1_relat_1(sK10)) != iProver_top
% 8.00/1.49      | v1_relat_1(sK10) != iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_3299]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_29574,plain,
% 8.00/1.49      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
% 8.00/1.49      | r2_hidden(X0,sK7) != iProver_top
% 8.00/1.49      | v1_relat_1(sK10) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_29564,c_3300]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3680,plain,
% 8.00/1.49      ( r1_tarski(sK10,k2_zfmisc_1(sK8,sK6)) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2534,c_2556]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3690,plain,
% 8.00/1.49      ( v1_relat_1(k2_zfmisc_1(sK8,sK6)) != iProver_top
% 8.00/1.49      | v1_relat_1(sK10) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_3680,c_2528]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4018,plain,
% 8.00/1.49      ( v1_relat_1(sK10) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2555,c_3690]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31416,plain,
% 8.00/1.49      ( r2_hidden(X0,sK7) != iProver_top
% 8.00/1.49      | k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0)) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_29574,c_4018]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31417,plain,
% 8.00/1.49      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
% 8.00/1.49      | r2_hidden(X0,sK7) != iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_31416]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31427,plain,
% 8.00/1.49      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_5722,c_31417]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_34,negated_conjecture,
% 8.00/1.49      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f114]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_31486,plain,
% 8.00/1.49      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_31427,c_34]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32202,plain,
% 8.00/1.49      ( k1_funct_1(k5_relat_1(sK9,sK10),sK11) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_32200,c_31486]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2533,plain,
% 8.00/1.49      ( v1_funct_1(sK10) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_33,plain,
% 8.00/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.49      | ~ r2_hidden(X3,X1)
% 8.00/1.49      | ~ v1_funct_1(X4)
% 8.00/1.49      | ~ v1_funct_1(X0)
% 8.00/1.49      | ~ v1_relat_1(X4)
% 8.00/1.49      | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 8.00/1.49      | k1_xboole_0 = X2 ),
% 8.00/1.49      inference(cnf_transformation,[],[f104]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2537,plain,
% 8.00/1.49      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 8.00/1.49      | k1_xboole_0 = X3
% 8.00/1.49      | v1_funct_2(X0,X4,X3) != iProver_top
% 8.00/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) != iProver_top
% 8.00/1.49      | r2_hidden(X2,X4) != iProver_top
% 8.00/1.49      | v1_funct_1(X1) != iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4116,plain,
% 8.00/1.49      ( k1_funct_1(k5_relat_1(sK9,X0),X1) = k1_funct_1(X0,k1_funct_1(sK9,X1))
% 8.00/1.49      | sK8 = k1_xboole_0
% 8.00/1.49      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 8.00/1.49      | r2_hidden(X1,sK7) != iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_funct_1(sK9) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2532,c_2537]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4692,plain,
% 8.00/1.49      ( v1_funct_1(X0) != iProver_top
% 8.00/1.49      | r2_hidden(X1,sK7) != iProver_top
% 8.00/1.49      | k1_funct_1(k5_relat_1(sK9,X0),X1) = k1_funct_1(X0,k1_funct_1(sK9,X1))
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_4116,c_44,c_45,c_46,c_2662,c_3340]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4693,plain,
% 8.00/1.49      ( k1_funct_1(k5_relat_1(sK9,X0),X1) = k1_funct_1(X0,k1_funct_1(sK9,X1))
% 8.00/1.49      | r2_hidden(X1,sK7) != iProver_top
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_4692]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5727,plain,
% 8.00/1.49      ( k1_funct_1(X0,k1_funct_1(sK9,sK11)) = k1_funct_1(k5_relat_1(sK9,X0),sK11)
% 8.00/1.49      | v1_funct_1(X0) != iProver_top
% 8.00/1.49      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_5722,c_4693]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_7091,plain,
% 8.00/1.49      ( k1_funct_1(k5_relat_1(sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
% 8.00/1.49      | v1_relat_1(sK10) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2533,c_5727]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_7530,plain,
% 8.00/1.49      ( k1_funct_1(k5_relat_1(sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_7091,c_4018]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32203,plain,
% 8.00/1.49      ( k1_funct_1(sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 8.00/1.49      inference(light_normalisation,[status(thm)],[c_32202,c_7530]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_32204,plain,
% 8.00/1.49      ( $false ),
% 8.00/1.49      inference(equality_resolution_simp,[status(thm)],[c_32203]) ).
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  ------                               Statistics
% 8.00/1.49  
% 8.00/1.49  ------ General
% 8.00/1.49  
% 8.00/1.49  abstr_ref_over_cycles:                  0
% 8.00/1.49  abstr_ref_under_cycles:                 0
% 8.00/1.49  gc_basic_clause_elim:                   0
% 8.00/1.49  forced_gc_time:                         0
% 8.00/1.49  parsing_time:                           0.007
% 8.00/1.49  unif_index_cands_time:                  0.
% 8.00/1.49  unif_index_add_time:                    0.
% 8.00/1.49  orderings_time:                         0.
% 8.00/1.49  out_proof_time:                         0.015
% 8.00/1.49  total_time:                             0.866
% 8.00/1.49  num_of_symbols:                         63
% 8.00/1.49  num_of_terms:                           29805
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing
% 8.00/1.49  
% 8.00/1.49  num_of_splits:                          0
% 8.00/1.49  num_of_split_atoms:                     0
% 8.00/1.49  num_of_reused_defs:                     0
% 8.00/1.49  num_eq_ax_congr_red:                    62
% 8.00/1.49  num_of_sem_filtered_clauses:            1
% 8.00/1.49  num_of_subtypes:                        0
% 8.00/1.49  monotx_restored_types:                  0
% 8.00/1.49  sat_num_of_epr_types:                   0
% 8.00/1.49  sat_num_of_non_cyclic_types:            0
% 8.00/1.49  sat_guarded_non_collapsed_types:        0
% 8.00/1.49  num_pure_diseq_elim:                    0
% 8.00/1.49  simp_replaced_by:                       0
% 8.00/1.49  res_preprocessed:                       206
% 8.00/1.49  prep_upred:                             0
% 8.00/1.49  prep_unflattend:                        102
% 8.00/1.49  smt_new_axioms:                         0
% 8.00/1.49  pred_elim_cands:                        7
% 8.00/1.49  pred_elim:                              1
% 8.00/1.49  pred_elim_cl:                           1
% 8.00/1.49  pred_elim_cycles:                       5
% 8.00/1.49  merged_defs:                            8
% 8.00/1.49  merged_defs_ncl:                        0
% 8.00/1.49  bin_hyper_res:                          9
% 8.00/1.49  prep_cycles:                            4
% 8.00/1.49  pred_elim_time:                         0.022
% 8.00/1.49  splitting_time:                         0.
% 8.00/1.49  sem_filter_time:                        0.
% 8.00/1.49  monotx_time:                            0.
% 8.00/1.49  subtype_inf_time:                       0.
% 8.00/1.49  
% 8.00/1.49  ------ Problem properties
% 8.00/1.49  
% 8.00/1.49  clauses:                                43
% 8.00/1.49  conjectures:                            10
% 8.00/1.49  epr:                                    13
% 8.00/1.49  horn:                                   32
% 8.00/1.49  ground:                                 10
% 8.00/1.49  unary:                                  13
% 8.00/1.49  binary:                                 10
% 8.00/1.49  lits:                                   120
% 8.00/1.49  lits_eq:                                26
% 8.00/1.49  fd_pure:                                0
% 8.00/1.49  fd_pseudo:                              0
% 8.00/1.49  fd_cond:                                6
% 8.00/1.49  fd_pseudo_cond:                         3
% 8.00/1.49  ac_symbols:                             0
% 8.00/1.49  
% 8.00/1.49  ------ Propositional Solver
% 8.00/1.49  
% 8.00/1.49  prop_solver_calls:                      32
% 8.00/1.49  prop_fast_solver_calls:                 2756
% 8.00/1.49  smt_solver_calls:                       0
% 8.00/1.49  smt_fast_solver_calls:                  0
% 8.00/1.49  prop_num_of_clauses:                    13595
% 8.00/1.49  prop_preprocess_simplified:             26951
% 8.00/1.49  prop_fo_subsumed:                       123
% 8.00/1.49  prop_solver_time:                       0.
% 8.00/1.49  smt_solver_time:                        0.
% 8.00/1.49  smt_fast_solver_time:                   0.
% 8.00/1.49  prop_fast_solver_time:                  0.
% 8.00/1.49  prop_unsat_core_time:                   0.
% 8.00/1.49  
% 8.00/1.49  ------ QBF
% 8.00/1.49  
% 8.00/1.49  qbf_q_res:                              0
% 8.00/1.49  qbf_num_tautologies:                    0
% 8.00/1.49  qbf_prep_cycles:                        0
% 8.00/1.49  
% 8.00/1.49  ------ BMC1
% 8.00/1.49  
% 8.00/1.49  bmc1_current_bound:                     -1
% 8.00/1.49  bmc1_last_solved_bound:                 -1
% 8.00/1.49  bmc1_unsat_core_size:                   -1
% 8.00/1.49  bmc1_unsat_core_parents_size:           -1
% 8.00/1.49  bmc1_merge_next_fun:                    0
% 8.00/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.00/1.49  
% 8.00/1.49  ------ Instantiation
% 8.00/1.49  
% 8.00/1.49  inst_num_of_clauses:                    3342
% 8.00/1.49  inst_num_in_passive:                    1720
% 8.00/1.49  inst_num_in_active:                     1538
% 8.00/1.49  inst_num_in_unprocessed:                84
% 8.00/1.49  inst_num_of_loops:                      1910
% 8.00/1.49  inst_num_of_learning_restarts:          0
% 8.00/1.49  inst_num_moves_active_passive:          369
% 8.00/1.49  inst_lit_activity:                      0
% 8.00/1.49  inst_lit_activity_moves:                0
% 8.00/1.49  inst_num_tautologies:                   0
% 8.00/1.49  inst_num_prop_implied:                  0
% 8.00/1.49  inst_num_existing_simplified:           0
% 8.00/1.49  inst_num_eq_res_simplified:             0
% 8.00/1.49  inst_num_child_elim:                    0
% 8.00/1.49  inst_num_of_dismatching_blockings:      1528
% 8.00/1.49  inst_num_of_non_proper_insts:           4046
% 8.00/1.49  inst_num_of_duplicates:                 0
% 8.00/1.49  inst_inst_num_from_inst_to_res:         0
% 8.00/1.49  inst_dismatching_checking_time:         0.
% 8.00/1.49  
% 8.00/1.49  ------ Resolution
% 8.00/1.49  
% 8.00/1.49  res_num_of_clauses:                     0
% 8.00/1.49  res_num_in_passive:                     0
% 8.00/1.49  res_num_in_active:                      0
% 8.00/1.49  res_num_of_loops:                       210
% 8.00/1.49  res_forward_subset_subsumed:            185
% 8.00/1.49  res_backward_subset_subsumed:           2
% 8.00/1.49  res_forward_subsumed:                   2
% 8.00/1.49  res_backward_subsumed:                  0
% 8.00/1.49  res_forward_subsumption_resolution:     0
% 8.00/1.49  res_backward_subsumption_resolution:    0
% 8.00/1.49  res_clause_to_clause_subsumption:       3133
% 8.00/1.49  res_orphan_elimination:                 0
% 8.00/1.49  res_tautology_del:                      331
% 8.00/1.49  res_num_eq_res_simplified:              0
% 8.00/1.49  res_num_sel_changes:                    0
% 8.00/1.49  res_moves_from_active_to_pass:          0
% 8.00/1.49  
% 8.00/1.49  ------ Superposition
% 8.00/1.49  
% 8.00/1.49  sup_time_total:                         0.
% 8.00/1.49  sup_time_generating:                    0.
% 8.00/1.49  sup_time_sim_full:                      0.
% 8.00/1.49  sup_time_sim_immed:                     0.
% 8.00/1.49  
% 8.00/1.49  sup_num_of_clauses:                     1179
% 8.00/1.49  sup_num_in_active:                      360
% 8.00/1.49  sup_num_in_passive:                     819
% 8.00/1.49  sup_num_of_loops:                       381
% 8.00/1.49  sup_fw_superposition:                   596
% 8.00/1.49  sup_bw_superposition:                   861
% 8.00/1.49  sup_immediate_simplified:               197
% 8.00/1.49  sup_given_eliminated:                   0
% 8.00/1.49  comparisons_done:                       0
% 8.00/1.49  comparisons_avoided:                    441
% 8.00/1.49  
% 8.00/1.49  ------ Simplifications
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  sim_fw_subset_subsumed:                 77
% 8.00/1.49  sim_bw_subset_subsumed:                 46
% 8.00/1.49  sim_fw_subsumed:                        75
% 8.00/1.49  sim_bw_subsumed:                        9
% 8.00/1.49  sim_fw_subsumption_res:                 0
% 8.00/1.49  sim_bw_subsumption_res:                 0
% 8.00/1.49  sim_tautology_del:                      9
% 8.00/1.49  sim_eq_tautology_del:                   15
% 8.00/1.49  sim_eq_res_simp:                        0
% 8.00/1.49  sim_fw_demodulated:                     8
% 8.00/1.49  sim_bw_demodulated:                     13
% 8.00/1.49  sim_light_normalised:                   24
% 8.00/1.49  sim_joinable_taut:                      0
% 8.00/1.49  sim_joinable_simp:                      0
% 8.00/1.49  sim_ac_normalised:                      0
% 8.00/1.49  sim_smt_subsumption:                    0
% 8.00/1.49  
%------------------------------------------------------------------------------
