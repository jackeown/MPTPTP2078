%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:43 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 710 expanded)
%              Number of clauses        :  113 ( 199 expanded)
%              Number of leaves         :   23 ( 240 expanded)
%              Depth                    :   22
%              Number of atoms          :  676 (5302 expanded)
%              Number of equality atoms :  295 (1462 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,negated_conjecture,(
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
    inference(negated_conjecture,[],[f32])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f68,plain,(
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
    inference(flattening,[],[f67])).

fof(f90,plain,(
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

fof(f89,plain,(
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

fof(f88,plain,(
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

fof(f87,plain,
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

fof(f91,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f68,f90,f89,f88,f87])).

fof(f154,plain,(
    m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f91])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f156,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f91])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f153,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f91])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f155,plain,(
    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f91])).

fof(f151,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f91])).

fof(f31,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f66,plain,(
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
    inference(flattening,[],[f65])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f148,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f91])).

fof(f149,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f91])).

fof(f150,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f91])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f63])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f57])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f152,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f91])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f28,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f134,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f71])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f161,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f157,plain,(
    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f91])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f99])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f96,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f116,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_59,negated_conjecture,
    ( m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_3386,plain,
    ( m1_subset_1(sK11,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3420,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7833,plain,
    ( r2_hidden(sK11,sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3386,c_3420])).

cnf(c_72,plain,
    ( m1_subset_1(sK11,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_57,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3872,plain,
    ( ~ v1_xboole_0(sK7)
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3873,plain,
    ( k1_xboole_0 = sK7
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3872])).

cnf(c_4091,plain,
    ( ~ m1_subset_1(X0,sK7)
    | r2_hidden(X0,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4455,plain,
    ( ~ m1_subset_1(sK11,sK7)
    | r2_hidden(sK11,sK7)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_4091])).

cnf(c_4456,plain,
    ( m1_subset_1(sK11,sK7) != iProver_top
    | r2_hidden(sK11,sK7) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4455])).

cnf(c_7871,plain,
    ( r2_hidden(sK11,sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7833,c_72,c_57,c_3873,c_4456])).

cnf(c_60,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_3385,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_33,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_3403,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6344,plain,
    ( v5_relat_1(sK10,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3385,c_3403])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_3401,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6503,plain,
    ( k1_relset_1(sK8,sK6,sK10) = k1_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_3385,c_3401])).

cnf(c_58,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_3387,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_6793,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6503,c_3387])).

cnf(c_62,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_3383,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_51,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_3390,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_6181,plain,
    ( sK8 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3383,c_3390])).

cnf(c_65,negated_conjecture,
    ( ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_64,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_67,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_63,negated_conjecture,
    ( v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_68,plain,
    ( v1_funct_2(sK9,sK7,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_63])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2240,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3916,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_2240])).

cnf(c_3918,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3916])).

cnf(c_7053,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6181,c_65,c_67,c_68,c_0,c_3918])).

cnf(c_7054,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7053])).

cnf(c_7062,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_relat_1(sK10)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6793,c_7054])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_3392,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_8383,plain,
    ( k1_relat_1(sK10) = k1_xboole_0
    | v1_funct_2(sK9,sK7,k1_relat_1(sK10)) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_7062,c_3392])).

cnf(c_53,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_3388,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_5326,plain,
    ( sK8 = k1_xboole_0
    | v1_funct_2(sK9,sK7,X0) = iProver_top
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_3383,c_3388])).

cnf(c_6082,plain,
    ( r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
    | v1_funct_2(sK9,sK7,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5326,c_65,c_67,c_68,c_0,c_3918])).

cnf(c_6083,plain,
    ( v1_funct_2(sK9,sK7,X0) = iProver_top
    | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6082])).

cnf(c_6091,plain,
    ( v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_6083])).

cnf(c_6792,plain,
    ( v1_funct_2(sK9,sK7,k1_relat_1(sK10)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6503,c_6091])).

cnf(c_20070,plain,
    ( r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top
    | k1_relat_1(sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8383,c_67,c_6792])).

cnf(c_20071,plain,
    ( k1_relat_1(sK10) = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
    inference(renaming,[status(thm)],[c_20070])).

cnf(c_41,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_3398,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_20082,plain,
    ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
    | k1_relat_1(sK10) = k1_xboole_0
    | v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_20071,c_3398])).

cnf(c_61,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_70,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_71,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_3901,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_3902,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
    | v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3901])).

cnf(c_32595,plain,
    ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
    | k1_relat_1(sK10) = k1_xboole_0
    | v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(X1,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20082,c_70,c_71,c_3902])).

cnf(c_32605,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
    | k1_relat_1(sK10) = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6344,c_32595])).

cnf(c_32722,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | k1_relat_1(sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7871,c_32605])).

cnf(c_42,plain,
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
    inference(cnf_transformation,[],[f134])).

cnf(c_3397,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_14563,plain,
    ( k1_funct_1(k8_funct_2(X0,sK8,sK6,X1,sK10),X2) = k1_funct_1(sK10,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK8) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top
    | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK8,X1),k1_relat_1(sK10)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_6503,c_3397])).

cnf(c_66,plain,
    ( v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_15497,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | v1_funct_2(X1,X0,sK8) != iProver_top
    | k1_xboole_0 = X0
    | k1_funct_1(k8_funct_2(X0,sK8,sK6,X1,sK10),X2) = k1_funct_1(sK10,k1_funct_1(X1,X2))
    | r1_tarski(k2_relset_1(X0,sK8,X1),k1_relat_1(sK10)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14563,c_66,c_70,c_71])).

cnf(c_15498,plain,
    ( k1_funct_1(k8_funct_2(X0,sK8,sK6,X1,sK10),X2) = k1_funct_1(sK10,k1_funct_1(X1,X2))
    | k1_xboole_0 = X0
    | v1_funct_2(X1,X0,sK8) != iProver_top
    | m1_subset_1(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK8,X1),k1_relat_1(sK10)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_15497])).

cnf(c_15508,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
    | sK7 = k1_xboole_0
    | v1_funct_2(sK9,sK7,sK8) != iProver_top
    | m1_subset_1(X0,sK7) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6793,c_15498])).

cnf(c_69,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_186,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_187,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2239,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3970,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_3971,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3970])).

cnf(c_15772,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
    | m1_subset_1(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15508,c_67,c_68,c_69,c_57,c_186,c_187,c_3971])).

cnf(c_15781,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(superposition,[status(thm)],[c_3386,c_15772])).

cnf(c_56,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_15787,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(demodulation,[status(thm)],[c_15781,c_56])).

cnf(c_32772,plain,
    ( k1_relat_1(sK10) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32722,c_15787])).

cnf(c_32794,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32772,c_7062])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f160])).

cnf(c_32805,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32794,c_5])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_17319,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(X0))
    | r1_tarski(sK9,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_17320,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK9,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17319])).

cnf(c_17322,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17320])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_9508,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_9511,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9508])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_5797,plain,
    ( ~ r1_tarski(X0,sK9)
    | ~ r1_tarski(sK9,X0)
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5798,plain,
    ( sK9 = X0
    | r1_tarski(X0,sK9) != iProver_top
    | r1_tarski(sK9,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5797])).

cnf(c_5800,plain,
    ( sK9 = k1_xboole_0
    | r1_tarski(sK9,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5798])).

cnf(c_5578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9))
    | r1_tarski(X0,sK9) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5579,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(X0,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5578])).

cnf(c_5581,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK9)) != iProver_top
    | r1_tarski(k1_xboole_0,sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5579])).

cnf(c_5448,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK9)
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_2240])).

cnf(c_5450,plain,
    ( v1_xboole_0(sK9)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK9 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5448])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_24,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39,c_24])).

cnf(c_338,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_3379,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_4346,plain,
    ( v1_funct_2(sK9,sK7,sK8) != iProver_top
    | v1_xboole_0(sK9) != iProver_top
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3383,c_3379])).

cnf(c_4375,plain,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_xboole_0(sK9)
    | v1_xboole_0(sK8)
    | v1_xboole_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4346])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32805,c_17322,c_9511,c_5800,c_5581,c_5450,c_4375,c_3872,c_0,c_57,c_63,c_65])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:54:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.65/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.49  
% 7.65/1.49  ------  iProver source info
% 7.65/1.49  
% 7.65/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.49  git: non_committed_changes: false
% 7.65/1.49  git: last_make_outside_of_git: false
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  
% 7.65/1.49  ------ Input Options
% 7.65/1.49  
% 7.65/1.49  --out_options                           all
% 7.65/1.49  --tptp_safe_out                         true
% 7.65/1.49  --problem_path                          ""
% 7.65/1.49  --include_path                          ""
% 7.65/1.49  --clausifier                            res/vclausify_rel
% 7.65/1.49  --clausifier_options                    --mode clausify
% 7.65/1.49  --stdin                                 false
% 7.65/1.49  --stats_out                             all
% 7.65/1.49  
% 7.65/1.49  ------ General Options
% 7.65/1.49  
% 7.65/1.49  --fof                                   false
% 7.65/1.49  --time_out_real                         305.
% 7.65/1.49  --time_out_virtual                      -1.
% 7.65/1.49  --symbol_type_check                     false
% 7.65/1.49  --clausify_out                          false
% 7.65/1.49  --sig_cnt_out                           false
% 7.65/1.49  --trig_cnt_out                          false
% 7.65/1.49  --trig_cnt_out_tolerance                1.
% 7.65/1.49  --trig_cnt_out_sk_spl                   false
% 7.65/1.49  --abstr_cl_out                          false
% 7.65/1.49  
% 7.65/1.49  ------ Global Options
% 7.65/1.49  
% 7.65/1.49  --schedule                              default
% 7.65/1.49  --add_important_lit                     false
% 7.65/1.49  --prop_solver_per_cl                    1000
% 7.65/1.49  --min_unsat_core                        false
% 7.65/1.49  --soft_assumptions                      false
% 7.65/1.49  --soft_lemma_size                       3
% 7.65/1.49  --prop_impl_unit_size                   0
% 7.65/1.49  --prop_impl_unit                        []
% 7.65/1.49  --share_sel_clauses                     true
% 7.65/1.49  --reset_solvers                         false
% 7.65/1.49  --bc_imp_inh                            [conj_cone]
% 7.65/1.49  --conj_cone_tolerance                   3.
% 7.65/1.49  --extra_neg_conj                        none
% 7.65/1.49  --large_theory_mode                     true
% 7.65/1.49  --prolific_symb_bound                   200
% 7.65/1.49  --lt_threshold                          2000
% 7.65/1.49  --clause_weak_htbl                      true
% 7.65/1.49  --gc_record_bc_elim                     false
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing Options
% 7.65/1.49  
% 7.65/1.49  --preprocessing_flag                    true
% 7.65/1.49  --time_out_prep_mult                    0.1
% 7.65/1.49  --splitting_mode                        input
% 7.65/1.49  --splitting_grd                         true
% 7.65/1.49  --splitting_cvd                         false
% 7.65/1.49  --splitting_cvd_svl                     false
% 7.65/1.49  --splitting_nvd                         32
% 7.65/1.49  --sub_typing                            true
% 7.65/1.49  --prep_gs_sim                           true
% 7.65/1.49  --prep_unflatten                        true
% 7.65/1.49  --prep_res_sim                          true
% 7.65/1.49  --prep_upred                            true
% 7.65/1.49  --prep_sem_filter                       exhaustive
% 7.65/1.49  --prep_sem_filter_out                   false
% 7.65/1.49  --pred_elim                             true
% 7.65/1.49  --res_sim_input                         true
% 7.65/1.49  --eq_ax_congr_red                       true
% 7.65/1.49  --pure_diseq_elim                       true
% 7.65/1.49  --brand_transform                       false
% 7.65/1.49  --non_eq_to_eq                          false
% 7.65/1.49  --prep_def_merge                        true
% 7.65/1.49  --prep_def_merge_prop_impl              false
% 7.65/1.49  --prep_def_merge_mbd                    true
% 7.65/1.49  --prep_def_merge_tr_red                 false
% 7.65/1.49  --prep_def_merge_tr_cl                  false
% 7.65/1.49  --smt_preprocessing                     true
% 7.65/1.49  --smt_ac_axioms                         fast
% 7.65/1.49  --preprocessed_out                      false
% 7.65/1.49  --preprocessed_stats                    false
% 7.65/1.49  
% 7.65/1.49  ------ Abstraction refinement Options
% 7.65/1.49  
% 7.65/1.49  --abstr_ref                             []
% 7.65/1.49  --abstr_ref_prep                        false
% 7.65/1.49  --abstr_ref_until_sat                   false
% 7.65/1.49  --abstr_ref_sig_restrict                funpre
% 7.65/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.49  --abstr_ref_under                       []
% 7.65/1.49  
% 7.65/1.49  ------ SAT Options
% 7.65/1.49  
% 7.65/1.49  --sat_mode                              false
% 7.65/1.49  --sat_fm_restart_options                ""
% 7.65/1.49  --sat_gr_def                            false
% 7.65/1.49  --sat_epr_types                         true
% 7.65/1.49  --sat_non_cyclic_types                  false
% 7.65/1.49  --sat_finite_models                     false
% 7.65/1.49  --sat_fm_lemmas                         false
% 7.65/1.49  --sat_fm_prep                           false
% 7.65/1.49  --sat_fm_uc_incr                        true
% 7.65/1.49  --sat_out_model                         small
% 7.65/1.49  --sat_out_clauses                       false
% 7.65/1.49  
% 7.65/1.49  ------ QBF Options
% 7.65/1.49  
% 7.65/1.49  --qbf_mode                              false
% 7.65/1.49  --qbf_elim_univ                         false
% 7.65/1.49  --qbf_dom_inst                          none
% 7.65/1.49  --qbf_dom_pre_inst                      false
% 7.65/1.49  --qbf_sk_in                             false
% 7.65/1.49  --qbf_pred_elim                         true
% 7.65/1.49  --qbf_split                             512
% 7.65/1.49  
% 7.65/1.49  ------ BMC1 Options
% 7.65/1.49  
% 7.65/1.49  --bmc1_incremental                      false
% 7.65/1.49  --bmc1_axioms                           reachable_all
% 7.65/1.49  --bmc1_min_bound                        0
% 7.65/1.49  --bmc1_max_bound                        -1
% 7.65/1.49  --bmc1_max_bound_default                -1
% 7.65/1.49  --bmc1_symbol_reachability              true
% 7.65/1.49  --bmc1_property_lemmas                  false
% 7.65/1.49  --bmc1_k_induction                      false
% 7.65/1.49  --bmc1_non_equiv_states                 false
% 7.65/1.49  --bmc1_deadlock                         false
% 7.65/1.49  --bmc1_ucm                              false
% 7.65/1.49  --bmc1_add_unsat_core                   none
% 7.65/1.49  --bmc1_unsat_core_children              false
% 7.65/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.49  --bmc1_out_stat                         full
% 7.65/1.49  --bmc1_ground_init                      false
% 7.65/1.49  --bmc1_pre_inst_next_state              false
% 7.65/1.49  --bmc1_pre_inst_state                   false
% 7.65/1.49  --bmc1_pre_inst_reach_state             false
% 7.65/1.49  --bmc1_out_unsat_core                   false
% 7.65/1.49  --bmc1_aig_witness_out                  false
% 7.65/1.49  --bmc1_verbose                          false
% 7.65/1.49  --bmc1_dump_clauses_tptp                false
% 7.65/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.49  --bmc1_dump_file                        -
% 7.65/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.49  --bmc1_ucm_extend_mode                  1
% 7.65/1.49  --bmc1_ucm_init_mode                    2
% 7.65/1.49  --bmc1_ucm_cone_mode                    none
% 7.65/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.49  --bmc1_ucm_relax_model                  4
% 7.65/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.49  --bmc1_ucm_layered_model                none
% 7.65/1.49  --bmc1_ucm_max_lemma_size               10
% 7.65/1.49  
% 7.65/1.49  ------ AIG Options
% 7.65/1.49  
% 7.65/1.49  --aig_mode                              false
% 7.65/1.49  
% 7.65/1.49  ------ Instantiation Options
% 7.65/1.49  
% 7.65/1.49  --instantiation_flag                    true
% 7.65/1.49  --inst_sos_flag                         false
% 7.65/1.49  --inst_sos_phase                        true
% 7.65/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.49  --inst_lit_sel_side                     num_symb
% 7.65/1.49  --inst_solver_per_active                1400
% 7.65/1.49  --inst_solver_calls_frac                1.
% 7.65/1.49  --inst_passive_queue_type               priority_queues
% 7.65/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.49  --inst_passive_queues_freq              [25;2]
% 7.65/1.49  --inst_dismatching                      true
% 7.65/1.49  --inst_eager_unprocessed_to_passive     true
% 7.65/1.49  --inst_prop_sim_given                   true
% 7.65/1.49  --inst_prop_sim_new                     false
% 7.65/1.49  --inst_subs_new                         false
% 7.65/1.49  --inst_eq_res_simp                      false
% 7.65/1.49  --inst_subs_given                       false
% 7.65/1.49  --inst_orphan_elimination               true
% 7.65/1.49  --inst_learning_loop_flag               true
% 7.65/1.49  --inst_learning_start                   3000
% 7.65/1.49  --inst_learning_factor                  2
% 7.65/1.49  --inst_start_prop_sim_after_learn       3
% 7.65/1.49  --inst_sel_renew                        solver
% 7.65/1.49  --inst_lit_activity_flag                true
% 7.65/1.49  --inst_restr_to_given                   false
% 7.65/1.49  --inst_activity_threshold               500
% 7.65/1.49  --inst_out_proof                        true
% 7.65/1.49  
% 7.65/1.49  ------ Resolution Options
% 7.65/1.49  
% 7.65/1.49  --resolution_flag                       true
% 7.65/1.49  --res_lit_sel                           adaptive
% 7.65/1.49  --res_lit_sel_side                      none
% 7.65/1.49  --res_ordering                          kbo
% 7.65/1.49  --res_to_prop_solver                    active
% 7.65/1.49  --res_prop_simpl_new                    false
% 7.65/1.49  --res_prop_simpl_given                  true
% 7.65/1.49  --res_passive_queue_type                priority_queues
% 7.65/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.49  --res_passive_queues_freq               [15;5]
% 7.65/1.49  --res_forward_subs                      full
% 7.65/1.49  --res_backward_subs                     full
% 7.65/1.49  --res_forward_subs_resolution           true
% 7.65/1.49  --res_backward_subs_resolution          true
% 7.65/1.49  --res_orphan_elimination                true
% 7.65/1.49  --res_time_limit                        2.
% 7.65/1.49  --res_out_proof                         true
% 7.65/1.49  
% 7.65/1.49  ------ Superposition Options
% 7.65/1.49  
% 7.65/1.49  --superposition_flag                    true
% 7.65/1.49  --sup_passive_queue_type                priority_queues
% 7.65/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.49  --demod_completeness_check              fast
% 7.65/1.49  --demod_use_ground                      true
% 7.65/1.49  --sup_to_prop_solver                    passive
% 7.65/1.49  --sup_prop_simpl_new                    true
% 7.65/1.49  --sup_prop_simpl_given                  true
% 7.65/1.49  --sup_fun_splitting                     false
% 7.65/1.49  --sup_smt_interval                      50000
% 7.65/1.49  
% 7.65/1.49  ------ Superposition Simplification Setup
% 7.65/1.49  
% 7.65/1.49  --sup_indices_passive                   []
% 7.65/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.49  --sup_full_bw                           [BwDemod]
% 7.65/1.49  --sup_immed_triv                        [TrivRules]
% 7.65/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.49  --sup_immed_bw_main                     []
% 7.65/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.49  
% 7.65/1.49  ------ Combination Options
% 7.65/1.49  
% 7.65/1.49  --comb_res_mult                         3
% 7.65/1.49  --comb_sup_mult                         2
% 7.65/1.49  --comb_inst_mult                        10
% 7.65/1.49  
% 7.65/1.49  ------ Debug Options
% 7.65/1.49  
% 7.65/1.49  --dbg_backtrace                         false
% 7.65/1.49  --dbg_dump_prop_clauses                 false
% 7.65/1.49  --dbg_dump_prop_clauses_file            -
% 7.65/1.49  --dbg_out_stat                          false
% 7.65/1.49  ------ Parsing...
% 7.65/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.49  ------ Proving...
% 7.65/1.49  ------ Problem Properties 
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  clauses                                 59
% 7.65/1.49  conjectures                             10
% 7.65/1.49  EPR                                     15
% 7.65/1.49  Horn                                    46
% 7.65/1.49  unary                                   21
% 7.65/1.49  binary                                  9
% 7.65/1.49  lits                                    169
% 7.65/1.49  lits eq                                 26
% 7.65/1.49  fd_pure                                 0
% 7.65/1.49  fd_pseudo                               0
% 7.65/1.49  fd_cond                                 6
% 7.65/1.49  fd_pseudo_cond                          4
% 7.65/1.49  AC symbols                              0
% 7.65/1.49  
% 7.65/1.49  ------ Schedule dynamic 5 is on 
% 7.65/1.49  
% 7.65/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ 
% 7.65/1.49  Current options:
% 7.65/1.49  ------ 
% 7.65/1.49  
% 7.65/1.49  ------ Input Options
% 7.65/1.49  
% 7.65/1.49  --out_options                           all
% 7.65/1.49  --tptp_safe_out                         true
% 7.65/1.49  --problem_path                          ""
% 7.65/1.49  --include_path                          ""
% 7.65/1.49  --clausifier                            res/vclausify_rel
% 7.65/1.49  --clausifier_options                    --mode clausify
% 7.65/1.49  --stdin                                 false
% 7.65/1.49  --stats_out                             all
% 7.65/1.49  
% 7.65/1.49  ------ General Options
% 7.65/1.49  
% 7.65/1.49  --fof                                   false
% 7.65/1.49  --time_out_real                         305.
% 7.65/1.49  --time_out_virtual                      -1.
% 7.65/1.49  --symbol_type_check                     false
% 7.65/1.49  --clausify_out                          false
% 7.65/1.49  --sig_cnt_out                           false
% 7.65/1.49  --trig_cnt_out                          false
% 7.65/1.49  --trig_cnt_out_tolerance                1.
% 7.65/1.49  --trig_cnt_out_sk_spl                   false
% 7.65/1.49  --abstr_cl_out                          false
% 7.65/1.49  
% 7.65/1.49  ------ Global Options
% 7.65/1.49  
% 7.65/1.49  --schedule                              default
% 7.65/1.49  --add_important_lit                     false
% 7.65/1.49  --prop_solver_per_cl                    1000
% 7.65/1.49  --min_unsat_core                        false
% 7.65/1.49  --soft_assumptions                      false
% 7.65/1.49  --soft_lemma_size                       3
% 7.65/1.49  --prop_impl_unit_size                   0
% 7.65/1.49  --prop_impl_unit                        []
% 7.65/1.49  --share_sel_clauses                     true
% 7.65/1.49  --reset_solvers                         false
% 7.65/1.49  --bc_imp_inh                            [conj_cone]
% 7.65/1.49  --conj_cone_tolerance                   3.
% 7.65/1.49  --extra_neg_conj                        none
% 7.65/1.49  --large_theory_mode                     true
% 7.65/1.49  --prolific_symb_bound                   200
% 7.65/1.49  --lt_threshold                          2000
% 7.65/1.49  --clause_weak_htbl                      true
% 7.65/1.49  --gc_record_bc_elim                     false
% 7.65/1.49  
% 7.65/1.49  ------ Preprocessing Options
% 7.65/1.49  
% 7.65/1.49  --preprocessing_flag                    true
% 7.65/1.49  --time_out_prep_mult                    0.1
% 7.65/1.49  --splitting_mode                        input
% 7.65/1.49  --splitting_grd                         true
% 7.65/1.49  --splitting_cvd                         false
% 7.65/1.49  --splitting_cvd_svl                     false
% 7.65/1.49  --splitting_nvd                         32
% 7.65/1.49  --sub_typing                            true
% 7.65/1.49  --prep_gs_sim                           true
% 7.65/1.49  --prep_unflatten                        true
% 7.65/1.49  --prep_res_sim                          true
% 7.65/1.49  --prep_upred                            true
% 7.65/1.49  --prep_sem_filter                       exhaustive
% 7.65/1.49  --prep_sem_filter_out                   false
% 7.65/1.49  --pred_elim                             true
% 7.65/1.49  --res_sim_input                         true
% 7.65/1.49  --eq_ax_congr_red                       true
% 7.65/1.49  --pure_diseq_elim                       true
% 7.65/1.49  --brand_transform                       false
% 7.65/1.49  --non_eq_to_eq                          false
% 7.65/1.49  --prep_def_merge                        true
% 7.65/1.49  --prep_def_merge_prop_impl              false
% 7.65/1.49  --prep_def_merge_mbd                    true
% 7.65/1.49  --prep_def_merge_tr_red                 false
% 7.65/1.49  --prep_def_merge_tr_cl                  false
% 7.65/1.49  --smt_preprocessing                     true
% 7.65/1.49  --smt_ac_axioms                         fast
% 7.65/1.49  --preprocessed_out                      false
% 7.65/1.49  --preprocessed_stats                    false
% 7.65/1.49  
% 7.65/1.49  ------ Abstraction refinement Options
% 7.65/1.49  
% 7.65/1.49  --abstr_ref                             []
% 7.65/1.49  --abstr_ref_prep                        false
% 7.65/1.49  --abstr_ref_until_sat                   false
% 7.65/1.49  --abstr_ref_sig_restrict                funpre
% 7.65/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.49  --abstr_ref_under                       []
% 7.65/1.49  
% 7.65/1.49  ------ SAT Options
% 7.65/1.49  
% 7.65/1.49  --sat_mode                              false
% 7.65/1.49  --sat_fm_restart_options                ""
% 7.65/1.49  --sat_gr_def                            false
% 7.65/1.49  --sat_epr_types                         true
% 7.65/1.49  --sat_non_cyclic_types                  false
% 7.65/1.49  --sat_finite_models                     false
% 7.65/1.49  --sat_fm_lemmas                         false
% 7.65/1.49  --sat_fm_prep                           false
% 7.65/1.49  --sat_fm_uc_incr                        true
% 7.65/1.49  --sat_out_model                         small
% 7.65/1.49  --sat_out_clauses                       false
% 7.65/1.49  
% 7.65/1.49  ------ QBF Options
% 7.65/1.49  
% 7.65/1.49  --qbf_mode                              false
% 7.65/1.49  --qbf_elim_univ                         false
% 7.65/1.49  --qbf_dom_inst                          none
% 7.65/1.49  --qbf_dom_pre_inst                      false
% 7.65/1.49  --qbf_sk_in                             false
% 7.65/1.49  --qbf_pred_elim                         true
% 7.65/1.49  --qbf_split                             512
% 7.65/1.49  
% 7.65/1.49  ------ BMC1 Options
% 7.65/1.49  
% 7.65/1.49  --bmc1_incremental                      false
% 7.65/1.49  --bmc1_axioms                           reachable_all
% 7.65/1.49  --bmc1_min_bound                        0
% 7.65/1.49  --bmc1_max_bound                        -1
% 7.65/1.49  --bmc1_max_bound_default                -1
% 7.65/1.49  --bmc1_symbol_reachability              true
% 7.65/1.49  --bmc1_property_lemmas                  false
% 7.65/1.49  --bmc1_k_induction                      false
% 7.65/1.49  --bmc1_non_equiv_states                 false
% 7.65/1.49  --bmc1_deadlock                         false
% 7.65/1.49  --bmc1_ucm                              false
% 7.65/1.49  --bmc1_add_unsat_core                   none
% 7.65/1.49  --bmc1_unsat_core_children              false
% 7.65/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.49  --bmc1_out_stat                         full
% 7.65/1.49  --bmc1_ground_init                      false
% 7.65/1.49  --bmc1_pre_inst_next_state              false
% 7.65/1.49  --bmc1_pre_inst_state                   false
% 7.65/1.49  --bmc1_pre_inst_reach_state             false
% 7.65/1.49  --bmc1_out_unsat_core                   false
% 7.65/1.49  --bmc1_aig_witness_out                  false
% 7.65/1.49  --bmc1_verbose                          false
% 7.65/1.49  --bmc1_dump_clauses_tptp                false
% 7.65/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.49  --bmc1_dump_file                        -
% 7.65/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.49  --bmc1_ucm_extend_mode                  1
% 7.65/1.49  --bmc1_ucm_init_mode                    2
% 7.65/1.49  --bmc1_ucm_cone_mode                    none
% 7.65/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.49  --bmc1_ucm_relax_model                  4
% 7.65/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.49  --bmc1_ucm_layered_model                none
% 7.65/1.49  --bmc1_ucm_max_lemma_size               10
% 7.65/1.49  
% 7.65/1.49  ------ AIG Options
% 7.65/1.49  
% 7.65/1.49  --aig_mode                              false
% 7.65/1.49  
% 7.65/1.49  ------ Instantiation Options
% 7.65/1.49  
% 7.65/1.49  --instantiation_flag                    true
% 7.65/1.49  --inst_sos_flag                         false
% 7.65/1.49  --inst_sos_phase                        true
% 7.65/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.49  --inst_lit_sel_side                     none
% 7.65/1.49  --inst_solver_per_active                1400
% 7.65/1.49  --inst_solver_calls_frac                1.
% 7.65/1.49  --inst_passive_queue_type               priority_queues
% 7.65/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.49  --inst_passive_queues_freq              [25;2]
% 7.65/1.49  --inst_dismatching                      true
% 7.65/1.49  --inst_eager_unprocessed_to_passive     true
% 7.65/1.49  --inst_prop_sim_given                   true
% 7.65/1.49  --inst_prop_sim_new                     false
% 7.65/1.49  --inst_subs_new                         false
% 7.65/1.49  --inst_eq_res_simp                      false
% 7.65/1.49  --inst_subs_given                       false
% 7.65/1.49  --inst_orphan_elimination               true
% 7.65/1.49  --inst_learning_loop_flag               true
% 7.65/1.49  --inst_learning_start                   3000
% 7.65/1.49  --inst_learning_factor                  2
% 7.65/1.49  --inst_start_prop_sim_after_learn       3
% 7.65/1.49  --inst_sel_renew                        solver
% 7.65/1.49  --inst_lit_activity_flag                true
% 7.65/1.49  --inst_restr_to_given                   false
% 7.65/1.49  --inst_activity_threshold               500
% 7.65/1.49  --inst_out_proof                        true
% 7.65/1.49  
% 7.65/1.49  ------ Resolution Options
% 7.65/1.49  
% 7.65/1.49  --resolution_flag                       false
% 7.65/1.49  --res_lit_sel                           adaptive
% 7.65/1.49  --res_lit_sel_side                      none
% 7.65/1.49  --res_ordering                          kbo
% 7.65/1.49  --res_to_prop_solver                    active
% 7.65/1.49  --res_prop_simpl_new                    false
% 7.65/1.49  --res_prop_simpl_given                  true
% 7.65/1.49  --res_passive_queue_type                priority_queues
% 7.65/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.49  --res_passive_queues_freq               [15;5]
% 7.65/1.49  --res_forward_subs                      full
% 7.65/1.49  --res_backward_subs                     full
% 7.65/1.49  --res_forward_subs_resolution           true
% 7.65/1.49  --res_backward_subs_resolution          true
% 7.65/1.49  --res_orphan_elimination                true
% 7.65/1.49  --res_time_limit                        2.
% 7.65/1.49  --res_out_proof                         true
% 7.65/1.49  
% 7.65/1.49  ------ Superposition Options
% 7.65/1.49  
% 7.65/1.49  --superposition_flag                    true
% 7.65/1.49  --sup_passive_queue_type                priority_queues
% 7.65/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.49  --demod_completeness_check              fast
% 7.65/1.49  --demod_use_ground                      true
% 7.65/1.49  --sup_to_prop_solver                    passive
% 7.65/1.49  --sup_prop_simpl_new                    true
% 7.65/1.49  --sup_prop_simpl_given                  true
% 7.65/1.49  --sup_fun_splitting                     false
% 7.65/1.49  --sup_smt_interval                      50000
% 7.65/1.49  
% 7.65/1.49  ------ Superposition Simplification Setup
% 7.65/1.49  
% 7.65/1.49  --sup_indices_passive                   []
% 7.65/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.49  --sup_full_bw                           [BwDemod]
% 7.65/1.49  --sup_immed_triv                        [TrivRules]
% 7.65/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.49  --sup_immed_bw_main                     []
% 7.65/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.49  
% 7.65/1.49  ------ Combination Options
% 7.65/1.49  
% 7.65/1.49  --comb_res_mult                         3
% 7.65/1.49  --comb_sup_mult                         2
% 7.65/1.49  --comb_inst_mult                        10
% 7.65/1.49  
% 7.65/1.49  ------ Debug Options
% 7.65/1.49  
% 7.65/1.49  --dbg_backtrace                         false
% 7.65/1.49  --dbg_dump_prop_clauses                 false
% 7.65/1.49  --dbg_dump_prop_clauses_file            -
% 7.65/1.49  --dbg_out_stat                          false
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  ------ Proving...
% 7.65/1.49  
% 7.65/1.49  
% 7.65/1.49  % SZS status Theorem for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.49  
% 7.65/1.49  fof(f32,conjecture,(
% 7.65/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f33,negated_conjecture,(
% 7.65/1.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.65/1.49    inference(negated_conjecture,[],[f32])).
% 7.65/1.49  
% 7.65/1.49  fof(f67,plain,(
% 7.65/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.65/1.49    inference(ennf_transformation,[],[f33])).
% 7.65/1.49  
% 7.65/1.49  fof(f68,plain,(
% 7.65/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.65/1.49    inference(flattening,[],[f67])).
% 7.65/1.49  
% 7.65/1.49  fof(f90,plain,(
% 7.65/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK11) != k7_partfun1(X0,X4,k1_funct_1(X3,sK11)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK11,X1))) )),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f89,plain,(
% 7.65/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK10),X5) != k7_partfun1(X0,sK10,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK10)) & m1_subset_1(X5,X1)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK10))) )),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f88,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK9,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK9,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK9),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK9,X1,X2) & v1_funct_1(sK9))) )),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f87,plain,(
% 7.65/1.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(X3,sK7,sK8) & v1_funct_1(X3)) & ~v1_xboole_0(sK8))),
% 7.65/1.49    introduced(choice_axiom,[])).
% 7.65/1.49  
% 7.65/1.49  fof(f91,plain,(
% 7.65/1.49    (((k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(sK11,sK7)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)) & ~v1_xboole_0(sK8)),
% 7.65/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f68,f90,f89,f88,f87])).
% 7.65/1.49  
% 7.65/1.49  fof(f154,plain,(
% 7.65/1.49    m1_subset_1(sK11,sK7)),
% 7.65/1.49    inference(cnf_transformation,[],[f91])).
% 7.65/1.49  
% 7.65/1.49  fof(f10,axiom,(
% 7.65/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f37,plain,(
% 7.65/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.65/1.49    inference(ennf_transformation,[],[f10])).
% 7.65/1.49  
% 7.65/1.49  fof(f38,plain,(
% 7.65/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.65/1.49    inference(flattening,[],[f37])).
% 7.65/1.49  
% 7.65/1.49  fof(f105,plain,(
% 7.65/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f38])).
% 7.65/1.49  
% 7.65/1.49  fof(f156,plain,(
% 7.65/1.49    k1_xboole_0 != sK7),
% 7.65/1.49    inference(cnf_transformation,[],[f91])).
% 7.65/1.49  
% 7.65/1.49  fof(f2,axiom,(
% 7.65/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f35,plain,(
% 7.65/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.65/1.49    inference(ennf_transformation,[],[f2])).
% 7.65/1.49  
% 7.65/1.49  fof(f93,plain,(
% 7.65/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.65/1.49    inference(cnf_transformation,[],[f35])).
% 7.65/1.49  
% 7.65/1.49  fof(f153,plain,(
% 7.65/1.49    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 7.65/1.49    inference(cnf_transformation,[],[f91])).
% 7.65/1.49  
% 7.65/1.49  fof(f22,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f34,plain,(
% 7.65/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.65/1.49    inference(pure_predicate_removal,[],[f22])).
% 7.65/1.49  
% 7.65/1.49  fof(f50,plain,(
% 7.65/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.49    inference(ennf_transformation,[],[f34])).
% 7.65/1.49  
% 7.65/1.49  fof(f125,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.49    inference(cnf_transformation,[],[f50])).
% 7.65/1.49  
% 7.65/1.49  fof(f24,axiom,(
% 7.65/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.49  
% 7.65/1.49  fof(f52,plain,(
% 7.65/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.49    inference(ennf_transformation,[],[f24])).
% 7.65/1.49  
% 7.65/1.49  fof(f127,plain,(
% 7.65/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.49    inference(cnf_transformation,[],[f52])).
% 7.65/1.49  
% 7.65/1.49  fof(f155,plain,(
% 7.65/1.49    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))),
% 7.65/1.49    inference(cnf_transformation,[],[f91])).
% 7.65/1.49  
% 7.65/1.49  fof(f151,plain,(
% 7.65/1.49    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 7.65/1.49    inference(cnf_transformation,[],[f91])).
% 7.65/1.49  
% 7.65/1.49  fof(f31,axiom,(
% 7.65/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.65/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f65,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.65/1.50    inference(ennf_transformation,[],[f31])).
% 7.65/1.50  
% 7.65/1.50  fof(f66,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.65/1.50    inference(flattening,[],[f65])).
% 7.65/1.50  
% 7.65/1.50  fof(f146,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f66])).
% 7.65/1.50  
% 7.65/1.50  fof(f148,plain,(
% 7.65/1.50    ~v1_xboole_0(sK8)),
% 7.65/1.50    inference(cnf_transformation,[],[f91])).
% 7.65/1.50  
% 7.65/1.50  fof(f149,plain,(
% 7.65/1.50    v1_funct_1(sK9)),
% 7.65/1.50    inference(cnf_transformation,[],[f91])).
% 7.65/1.50  
% 7.65/1.50  fof(f150,plain,(
% 7.65/1.50    v1_funct_2(sK9,sK7,sK8)),
% 7.65/1.50    inference(cnf_transformation,[],[f91])).
% 7.65/1.50  
% 7.65/1.50  fof(f1,axiom,(
% 7.65/1.50    v1_xboole_0(k1_xboole_0)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f92,plain,(
% 7.65/1.50    v1_xboole_0(k1_xboole_0)),
% 7.65/1.50    inference(cnf_transformation,[],[f1])).
% 7.65/1.50  
% 7.65/1.50  fof(f30,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f63,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.65/1.50    inference(ennf_transformation,[],[f30])).
% 7.65/1.50  
% 7.65/1.50  fof(f64,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.65/1.50    inference(flattening,[],[f63])).
% 7.65/1.50  
% 7.65/1.50  fof(f141,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f64])).
% 7.65/1.50  
% 7.65/1.50  fof(f144,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f66])).
% 7.65/1.50  
% 7.65/1.50  fof(f27,axiom,(
% 7.65/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f57,plain,(
% 7.65/1.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.65/1.50    inference(ennf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f58,plain,(
% 7.65/1.50    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.65/1.50    inference(flattening,[],[f57])).
% 7.65/1.50  
% 7.65/1.50  fof(f133,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f58])).
% 7.65/1.50  
% 7.65/1.50  fof(f152,plain,(
% 7.65/1.50    v1_funct_1(sK10)),
% 7.65/1.50    inference(cnf_transformation,[],[f91])).
% 7.65/1.50  
% 7.65/1.50  fof(f21,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f49,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.50    inference(ennf_transformation,[],[f21])).
% 7.65/1.50  
% 7.65/1.50  fof(f124,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f49])).
% 7.65/1.50  
% 7.65/1.50  fof(f28,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f59,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.65/1.50    inference(ennf_transformation,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f60,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.65/1.50    inference(flattening,[],[f59])).
% 7.65/1.50  
% 7.65/1.50  fof(f134,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f60])).
% 7.65/1.50  
% 7.65/1.50  fof(f4,axiom,(
% 7.65/1.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f71,plain,(
% 7.65/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.65/1.50    inference(nnf_transformation,[],[f4])).
% 7.65/1.50  
% 7.65/1.50  fof(f72,plain,(
% 7.65/1.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.65/1.50    inference(flattening,[],[f71])).
% 7.65/1.50  
% 7.65/1.50  fof(f97,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f72])).
% 7.65/1.50  
% 7.65/1.50  fof(f98,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f72])).
% 7.65/1.50  
% 7.65/1.50  fof(f161,plain,(
% 7.65/1.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.65/1.50    inference(equality_resolution,[],[f98])).
% 7.65/1.50  
% 7.65/1.50  fof(f157,plain,(
% 7.65/1.50    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))),
% 7.65/1.50    inference(cnf_transformation,[],[f91])).
% 7.65/1.50  
% 7.65/1.50  fof(f99,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.65/1.50    inference(cnf_transformation,[],[f72])).
% 7.65/1.50  
% 7.65/1.50  fof(f160,plain,(
% 7.65/1.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.65/1.50    inference(equality_resolution,[],[f99])).
% 7.65/1.50  
% 7.65/1.50  fof(f11,axiom,(
% 7.65/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f75,plain,(
% 7.65/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.65/1.50    inference(nnf_transformation,[],[f11])).
% 7.65/1.50  
% 7.65/1.50  fof(f106,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f75])).
% 7.65/1.50  
% 7.65/1.50  fof(f8,axiom,(
% 7.65/1.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f103,plain,(
% 7.65/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f8])).
% 7.65/1.50  
% 7.65/1.50  fof(f3,axiom,(
% 7.65/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f69,plain,(
% 7.65/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.65/1.50    inference(nnf_transformation,[],[f3])).
% 7.65/1.50  
% 7.65/1.50  fof(f70,plain,(
% 7.65/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.65/1.50    inference(flattening,[],[f69])).
% 7.65/1.50  
% 7.65/1.50  fof(f96,plain,(
% 7.65/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f70])).
% 7.65/1.50  
% 7.65/1.50  fof(f26,axiom,(
% 7.65/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f55,plain,(
% 7.65/1.50    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f56,plain,(
% 7.65/1.50    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.65/1.50    inference(flattening,[],[f55])).
% 7.65/1.50  
% 7.65/1.50  fof(f131,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f56])).
% 7.65/1.50  
% 7.65/1.50  fof(f18,axiom,(
% 7.65/1.50    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f45,plain,(
% 7.65/1.50    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 7.65/1.50    inference(ennf_transformation,[],[f18])).
% 7.65/1.50  
% 7.65/1.50  fof(f116,plain,(
% 7.65/1.50    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f45])).
% 7.65/1.50  
% 7.65/1.50  cnf(c_59,negated_conjecture,
% 7.65/1.50      ( m1_subset_1(sK11,sK7) ),
% 7.65/1.50      inference(cnf_transformation,[],[f154]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3386,plain,
% 7.65/1.50      ( m1_subset_1(sK11,sK7) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3420,plain,
% 7.65/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.65/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.65/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7833,plain,
% 7.65/1.50      ( r2_hidden(sK11,sK7) = iProver_top
% 7.65/1.50      | v1_xboole_0(sK7) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3386,c_3420]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_72,plain,
% 7.65/1.50      ( m1_subset_1(sK11,sK7) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_57,negated_conjecture,
% 7.65/1.50      ( k1_xboole_0 != sK7 ),
% 7.65/1.50      inference(cnf_transformation,[],[f156]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1,plain,
% 7.65/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3872,plain,
% 7.65/1.50      ( ~ v1_xboole_0(sK7) | k1_xboole_0 = sK7 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3873,plain,
% 7.65/1.50      ( k1_xboole_0 = sK7 | v1_xboole_0(sK7) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_3872]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4091,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,sK7) | r2_hidden(X0,sK7) | v1_xboole_0(sK7) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4455,plain,
% 7.65/1.50      ( ~ m1_subset_1(sK11,sK7)
% 7.65/1.50      | r2_hidden(sK11,sK7)
% 7.65/1.50      | v1_xboole_0(sK7) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4091]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4456,plain,
% 7.65/1.50      ( m1_subset_1(sK11,sK7) != iProver_top
% 7.65/1.50      | r2_hidden(sK11,sK7) = iProver_top
% 7.65/1.50      | v1_xboole_0(sK7) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_4455]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7871,plain,
% 7.65/1.50      ( r2_hidden(sK11,sK7) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_7833,c_72,c_57,c_3873,c_4456]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_60,negated_conjecture,
% 7.65/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f153]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3385,plain,
% 7.65/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_33,plain,
% 7.65/1.50      ( v5_relat_1(X0,X1)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f125]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3403,plain,
% 7.65/1.50      ( v5_relat_1(X0,X1) = iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6344,plain,
% 7.65/1.50      ( v5_relat_1(sK10,sK6) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3385,c_3403]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_35,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f127]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3401,plain,
% 7.65/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6503,plain,
% 7.65/1.50      ( k1_relset_1(sK8,sK6,sK10) = k1_relat_1(sK10) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3385,c_3401]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_58,negated_conjecture,
% 7.65/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f155]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3387,plain,
% 7.65/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6793,plain,
% 7.65/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relat_1(sK10)) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_6503,c_3387]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_62,negated_conjecture,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 7.65/1.50      inference(cnf_transformation,[],[f151]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3383,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_51,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.65/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | k1_xboole_0 = X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f146]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3390,plain,
% 7.65/1.50      ( k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6181,plain,
% 7.65/1.50      ( sK8 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.65/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
% 7.65/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3383,c_3390]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_65,negated_conjecture,
% 7.65/1.50      ( ~ v1_xboole_0(sK8) ),
% 7.65/1.50      inference(cnf_transformation,[],[f148]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_64,negated_conjecture,
% 7.65/1.50      ( v1_funct_1(sK9) ),
% 7.65/1.50      inference(cnf_transformation,[],[f149]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_67,plain,
% 7.65/1.50      ( v1_funct_1(sK9) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_63,negated_conjecture,
% 7.65/1.50      ( v1_funct_2(sK9,sK7,sK8) ),
% 7.65/1.50      inference(cnf_transformation,[],[f150]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_68,plain,
% 7.65/1.50      ( v1_funct_2(sK9,sK7,sK8) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_63]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_0,plain,
% 7.65/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2240,plain,
% 7.65/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3916,plain,
% 7.65/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2240]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3918,plain,
% 7.65/1.50      ( v1_xboole_0(sK8)
% 7.65/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.65/1.50      | sK8 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3916]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7053,plain,
% 7.65/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
% 7.65/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_6181,c_65,c_67,c_68,c_0,c_3918]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7054,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_7053]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7062,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_relat_1(sK10)))) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_6793,c_7054]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_49,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ r2_hidden(X3,X1)
% 7.65/1.50      | r2_hidden(k1_funct_1(X0,X3),X2)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | k1_xboole_0 = X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f141]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3392,plain,
% 7.65/1.50      ( k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.65/1.50      | r2_hidden(X3,X2) != iProver_top
% 7.65/1.50      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8383,plain,
% 7.65/1.50      ( k1_relat_1(sK10) = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK9,sK7,k1_relat_1(sK10)) != iProver_top
% 7.65/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.65/1.50      | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top
% 7.65/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_7062,c_3392]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_53,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | v1_funct_2(X0,X1,X3)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | k1_xboole_0 = X2 ),
% 7.65/1.50      inference(cnf_transformation,[],[f144]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3388,plain,
% 7.65/1.50      ( k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,X2,X0) != iProver_top
% 7.65/1.50      | v1_funct_2(X1,X2,X3) = iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5326,plain,
% 7.65/1.50      ( sK8 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK9,sK7,X0) = iProver_top
% 7.65/1.50      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
% 7.65/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3383,c_3388]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6082,plain,
% 7.65/1.50      ( r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top
% 7.65/1.50      | v1_funct_2(sK9,sK7,X0) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_5326,c_65,c_67,c_68,c_0,c_3918]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6083,plain,
% 7.65/1.50      ( v1_funct_2(sK9,sK7,X0) = iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(sK7,sK8,sK9),X0) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_6082]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6091,plain,
% 7.65/1.50      ( v1_funct_2(sK9,sK7,k1_relset_1(sK8,sK6,sK10)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3387,c_6083]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6792,plain,
% 7.65/1.50      ( v1_funct_2(sK9,sK7,k1_relat_1(sK10)) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_6503,c_6091]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20070,plain,
% 7.65/1.50      ( r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top
% 7.65/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.65/1.50      | k1_relat_1(sK10) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_8383,c_67,c_6792]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20071,plain,
% 7.65/1.50      ( k1_relat_1(sK10) = k1_xboole_0
% 7.65/1.50      | r2_hidden(X0,sK7) != iProver_top
% 7.65/1.50      | r2_hidden(k1_funct_1(sK9,X0),k1_relat_1(sK10)) = iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_20070]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_41,plain,
% 7.65/1.50      ( ~ v5_relat_1(X0,X1)
% 7.65/1.50      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_relat_1(X0)
% 7.65/1.50      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f133]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3398,plain,
% 7.65/1.50      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.65/1.50      | v5_relat_1(X1,X0) != iProver_top
% 7.65/1.50      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20082,plain,
% 7.65/1.50      ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
% 7.65/1.50      | k1_relat_1(sK10) = k1_xboole_0
% 7.65/1.50      | v5_relat_1(sK10,X0) != iProver_top
% 7.65/1.50      | r2_hidden(X1,sK7) != iProver_top
% 7.65/1.50      | v1_funct_1(sK10) != iProver_top
% 7.65/1.50      | v1_relat_1(sK10) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_20071,c_3398]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_61,negated_conjecture,
% 7.65/1.50      ( v1_funct_1(sK10) ),
% 7.65/1.50      inference(cnf_transformation,[],[f152]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_70,plain,
% 7.65/1.50      ( v1_funct_1(sK10) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_71,plain,
% 7.65/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | v1_relat_1(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f124]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3901,plain,
% 7.65/1.50      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
% 7.65/1.50      | v1_relat_1(sK10) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3902,plain,
% 7.65/1.50      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
% 7.65/1.50      | v1_relat_1(sK10) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_3901]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32595,plain,
% 7.65/1.50      ( k7_partfun1(X0,sK10,k1_funct_1(sK9,X1)) = k1_funct_1(sK10,k1_funct_1(sK9,X1))
% 7.65/1.50      | k1_relat_1(sK10) = k1_xboole_0
% 7.65/1.50      | v5_relat_1(sK10,X0) != iProver_top
% 7.65/1.50      | r2_hidden(X1,sK7) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_20082,c_70,c_71,c_3902]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32605,plain,
% 7.65/1.50      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,X0)) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
% 7.65/1.50      | k1_relat_1(sK10) = k1_xboole_0
% 7.65/1.50      | r2_hidden(X0,sK7) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_6344,c_32595]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32722,plain,
% 7.65/1.50      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) = k1_funct_1(sK10,k1_funct_1(sK9,sK11))
% 7.65/1.50      | k1_relat_1(sK10) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_7871,c_32605]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_42,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X3,X1)
% 7.65/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 7.65/1.50      | ~ v1_funct_1(X4)
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | v1_xboole_0(X2)
% 7.65/1.50      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.65/1.50      | k1_xboole_0 = X1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f134]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3397,plain,
% 7.65/1.50      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.65/1.50      | m1_subset_1(X5,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.65/1.50      | v1_funct_1(X3) != iProver_top
% 7.65/1.50      | v1_funct_1(X4) != iProver_top
% 7.65/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14563,plain,
% 7.65/1.50      ( k1_funct_1(k8_funct_2(X0,sK8,sK6,X1,sK10),X2) = k1_funct_1(sK10,k1_funct_1(X1,X2))
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,X0,sK8) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top
% 7.65/1.50      | m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) != iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(X0,sK8,X1),k1_relat_1(sK10)) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top
% 7.65/1.50      | v1_funct_1(sK10) != iProver_top
% 7.65/1.50      | v1_xboole_0(sK8) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_6503,c_3397]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_66,plain,
% 7.65/1.50      ( v1_xboole_0(sK8) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15497,plain,
% 7.65/1.50      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.65/1.50      | v1_funct_2(X1,X0,sK8) != iProver_top
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | k1_funct_1(k8_funct_2(X0,sK8,sK6,X1,sK10),X2) = k1_funct_1(sK10,k1_funct_1(X1,X2))
% 7.65/1.50      | r1_tarski(k2_relset_1(X0,sK8,X1),k1_relat_1(sK10)) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_14563,c_66,c_70,c_71]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15498,plain,
% 7.65/1.50      ( k1_funct_1(k8_funct_2(X0,sK8,sK6,X1,sK10),X2) = k1_funct_1(sK10,k1_funct_1(X1,X2))
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | v1_funct_2(X1,X0,sK8) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,X0) != iProver_top
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top
% 7.65/1.50      | r1_tarski(k2_relset_1(X0,sK8,X1),k1_relat_1(sK10)) != iProver_top
% 7.65/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_15497]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15508,plain,
% 7.65/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
% 7.65/1.50      | sK7 = k1_xboole_0
% 7.65/1.50      | v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.65/1.50      | m1_subset_1(X0,sK7) != iProver_top
% 7.65/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.65/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_6793,c_15498]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_69,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7,plain,
% 7.65/1.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = X0
% 7.65/1.50      | k1_xboole_0 = X1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_186,plain,
% 7.65/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6,plain,
% 7.65/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f161]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_187,plain,
% 7.65/1.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2239,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3970,plain,
% 7.65/1.50      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2239]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3971,plain,
% 7.65/1.50      ( sK7 != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = sK7
% 7.65/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3970]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15772,plain,
% 7.65/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X0) = k1_funct_1(sK10,k1_funct_1(sK9,X0))
% 7.65/1.50      | m1_subset_1(X0,sK7) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_15508,c_67,c_68,c_69,c_57,c_186,c_187,c_3971]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15781,plain,
% 7.65/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) = k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3386,c_15772]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_56,negated_conjecture,
% 7.65/1.50      ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f157]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15787,plain,
% 7.65/1.50      ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_15781,c_56]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32772,plain,
% 7.65/1.50      ( k1_relat_1(sK10) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_32722,c_15787]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32794,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k1_xboole_0))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_32772,c_7062]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5,plain,
% 7.65/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f160]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_32805,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_32794,c_5]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17319,plain,
% 7.65/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(X0)) | r1_tarski(sK9,X0) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17320,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(X0)) != iProver_top
% 7.65/1.50      | r1_tarski(sK9,X0) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_17319]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17322,plain,
% 7.65/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.65/1.50      | r1_tarski(sK9,k1_xboole_0) = iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_17320]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11,plain,
% 7.65/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9508,plain,
% 7.65/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK9)) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9511,plain,
% 7.65/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK9)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_9508]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5797,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,sK9) | ~ r1_tarski(sK9,X0) | sK9 = X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5798,plain,
% 7.65/1.50      ( sK9 = X0
% 7.65/1.50      | r1_tarski(X0,sK9) != iProver_top
% 7.65/1.50      | r1_tarski(sK9,X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_5797]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5800,plain,
% 7.65/1.50      ( sK9 = k1_xboole_0
% 7.65/1.50      | r1_tarski(sK9,k1_xboole_0) != iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,sK9) != iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5798]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5578,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9)) | r1_tarski(X0,sK9) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5579,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK9)) != iProver_top
% 7.65/1.50      | r1_tarski(X0,sK9) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_5578]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5581,plain,
% 7.65/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK9)) != iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,sK9) = iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5579]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5448,plain,
% 7.65/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK9) | sK9 != X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2240]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5450,plain,
% 7.65/1.50      ( v1_xboole_0(sK9)
% 7.65/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.65/1.50      | sK9 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5448]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_39,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_1(X0)
% 7.65/1.50      | ~ v1_xboole_0(X0)
% 7.65/1.50      | v1_xboole_0(X1)
% 7.65/1.50      | v1_xboole_0(X2) ),
% 7.65/1.50      inference(cnf_transformation,[],[f131]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_24,plain,
% 7.65/1.50      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_337,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ v1_xboole_0(X0)
% 7.65/1.50      | v1_xboole_0(X1)
% 7.65/1.50      | v1_xboole_0(X2) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_39,c_24]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_338,plain,
% 7.65/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.65/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.50      | ~ v1_xboole_0(X0)
% 7.65/1.50      | v1_xboole_0(X1)
% 7.65/1.50      | v1_xboole_0(X2) ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_337]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3379,plain,
% 7.65/1.50      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.65/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.50      | v1_xboole_0(X0) != iProver_top
% 7.65/1.50      | v1_xboole_0(X2) = iProver_top
% 7.65/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4346,plain,
% 7.65/1.50      ( v1_funct_2(sK9,sK7,sK8) != iProver_top
% 7.65/1.50      | v1_xboole_0(sK9) != iProver_top
% 7.65/1.50      | v1_xboole_0(sK8) = iProver_top
% 7.65/1.50      | v1_xboole_0(sK7) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_3383,c_3379]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4375,plain,
% 7.65/1.50      ( ~ v1_funct_2(sK9,sK7,sK8)
% 7.65/1.50      | ~ v1_xboole_0(sK9)
% 7.65/1.50      | v1_xboole_0(sK8)
% 7.65/1.50      | v1_xboole_0(sK7) ),
% 7.65/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4346]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(contradiction,plain,
% 7.65/1.50      ( $false ),
% 7.65/1.50      inference(minisat,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_32805,c_17322,c_9511,c_5800,c_5581,c_5450,c_4375,
% 7.65/1.50                 c_3872,c_0,c_57,c_63,c_65]) ).
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  ------                               Statistics
% 7.65/1.50  
% 7.65/1.50  ------ General
% 7.65/1.50  
% 7.65/1.50  abstr_ref_over_cycles:                  0
% 7.65/1.50  abstr_ref_under_cycles:                 0
% 7.65/1.50  gc_basic_clause_elim:                   0
% 7.65/1.50  forced_gc_time:                         0
% 7.65/1.50  parsing_time:                           0.012
% 7.65/1.50  unif_index_cands_time:                  0.
% 7.65/1.50  unif_index_add_time:                    0.
% 7.65/1.50  orderings_time:                         0.
% 7.65/1.50  out_proof_time:                         0.018
% 7.65/1.50  total_time:                             0.911
% 7.65/1.50  num_of_symbols:                         61
% 7.65/1.50  num_of_terms:                           39260
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing
% 7.65/1.50  
% 7.65/1.50  num_of_splits:                          0
% 7.65/1.50  num_of_split_atoms:                     0
% 7.65/1.50  num_of_reused_defs:                     0
% 7.65/1.50  num_eq_ax_congr_red:                    42
% 7.65/1.50  num_of_sem_filtered_clauses:            1
% 7.65/1.50  num_of_subtypes:                        0
% 7.65/1.50  monotx_restored_types:                  0
% 7.65/1.50  sat_num_of_epr_types:                   0
% 7.65/1.50  sat_num_of_non_cyclic_types:            0
% 7.65/1.50  sat_guarded_non_collapsed_types:        0
% 7.65/1.50  num_pure_diseq_elim:                    0
% 7.65/1.50  simp_replaced_by:                       0
% 7.65/1.50  res_preprocessed:                       275
% 7.65/1.50  prep_upred:                             0
% 7.65/1.50  prep_unflattend:                        36
% 7.65/1.50  smt_new_axioms:                         0
% 7.65/1.50  pred_elim_cands:                        8
% 7.65/1.50  pred_elim:                              0
% 7.65/1.50  pred_elim_cl:                           0
% 7.65/1.50  pred_elim_cycles:                       2
% 7.65/1.50  merged_defs:                            8
% 7.65/1.50  merged_defs_ncl:                        0
% 7.65/1.50  bin_hyper_res:                          9
% 7.65/1.50  prep_cycles:                            4
% 7.65/1.50  pred_elim_time:                         0.02
% 7.65/1.50  splitting_time:                         0.
% 7.65/1.50  sem_filter_time:                        0.
% 7.65/1.50  monotx_time:                            0.001
% 7.65/1.50  subtype_inf_time:                       0.
% 7.65/1.50  
% 7.65/1.50  ------ Problem properties
% 7.65/1.50  
% 7.65/1.50  clauses:                                59
% 7.65/1.50  conjectures:                            10
% 7.65/1.50  epr:                                    15
% 7.65/1.50  horn:                                   46
% 7.65/1.50  ground:                                 13
% 7.65/1.50  unary:                                  21
% 7.65/1.50  binary:                                 9
% 7.65/1.50  lits:                                   169
% 7.65/1.50  lits_eq:                                26
% 7.65/1.50  fd_pure:                                0
% 7.65/1.50  fd_pseudo:                              0
% 7.65/1.50  fd_cond:                                6
% 7.65/1.50  fd_pseudo_cond:                         4
% 7.65/1.50  ac_symbols:                             0
% 7.65/1.50  
% 7.65/1.50  ------ Propositional Solver
% 7.65/1.50  
% 7.65/1.50  prop_solver_calls:                      28
% 7.65/1.50  prop_fast_solver_calls:                 2832
% 7.65/1.50  smt_solver_calls:                       0
% 7.65/1.50  smt_fast_solver_calls:                  0
% 7.65/1.50  prop_num_of_clauses:                    11938
% 7.65/1.50  prop_preprocess_simplified:             29529
% 7.65/1.50  prop_fo_subsumed:                       83
% 7.65/1.50  prop_solver_time:                       0.
% 7.65/1.50  smt_solver_time:                        0.
% 7.65/1.50  smt_fast_solver_time:                   0.
% 7.65/1.50  prop_fast_solver_time:                  0.
% 7.65/1.50  prop_unsat_core_time:                   0.001
% 7.65/1.50  
% 7.65/1.50  ------ QBF
% 7.65/1.50  
% 7.65/1.50  qbf_q_res:                              0
% 7.65/1.50  qbf_num_tautologies:                    0
% 7.65/1.50  qbf_prep_cycles:                        0
% 7.65/1.50  
% 7.65/1.50  ------ BMC1
% 7.65/1.50  
% 7.65/1.50  bmc1_current_bound:                     -1
% 7.65/1.50  bmc1_last_solved_bound:                 -1
% 7.65/1.50  bmc1_unsat_core_size:                   -1
% 7.65/1.50  bmc1_unsat_core_parents_size:           -1
% 7.65/1.50  bmc1_merge_next_fun:                    0
% 7.65/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation
% 7.65/1.50  
% 7.65/1.50  inst_num_of_clauses:                    3399
% 7.65/1.50  inst_num_in_passive:                    1428
% 7.65/1.50  inst_num_in_active:                     1233
% 7.65/1.50  inst_num_in_unprocessed:                738
% 7.65/1.50  inst_num_of_loops:                      1420
% 7.65/1.50  inst_num_of_learning_restarts:          0
% 7.65/1.50  inst_num_moves_active_passive:          186
% 7.65/1.50  inst_lit_activity:                      0
% 7.65/1.50  inst_lit_activity_moves:                0
% 7.65/1.50  inst_num_tautologies:                   0
% 7.65/1.50  inst_num_prop_implied:                  0
% 7.65/1.50  inst_num_existing_simplified:           0
% 7.65/1.50  inst_num_eq_res_simplified:             0
% 7.65/1.50  inst_num_child_elim:                    0
% 7.65/1.50  inst_num_of_dismatching_blockings:      1677
% 7.65/1.50  inst_num_of_non_proper_insts:           3146
% 7.65/1.50  inst_num_of_duplicates:                 0
% 7.65/1.50  inst_inst_num_from_inst_to_res:         0
% 7.65/1.50  inst_dismatching_checking_time:         0.
% 7.65/1.50  
% 7.65/1.50  ------ Resolution
% 7.65/1.50  
% 7.65/1.50  res_num_of_clauses:                     0
% 7.65/1.50  res_num_in_passive:                     0
% 7.65/1.50  res_num_in_active:                      0
% 7.65/1.50  res_num_of_loops:                       279
% 7.65/1.50  res_forward_subset_subsumed:            434
% 7.65/1.50  res_backward_subset_subsumed:           0
% 7.65/1.50  res_forward_subsumed:                   0
% 7.65/1.50  res_backward_subsumed:                  0
% 7.65/1.50  res_forward_subsumption_resolution:     0
% 7.65/1.50  res_backward_subsumption_resolution:    0
% 7.65/1.50  res_clause_to_clause_subsumption:       1674
% 7.65/1.50  res_orphan_elimination:                 0
% 7.65/1.50  res_tautology_del:                      186
% 7.65/1.50  res_num_eq_res_simplified:              0
% 7.65/1.50  res_num_sel_changes:                    0
% 7.65/1.50  res_moves_from_active_to_pass:          0
% 7.65/1.50  
% 7.65/1.50  ------ Superposition
% 7.65/1.50  
% 7.65/1.50  sup_time_total:                         0.
% 7.65/1.50  sup_time_generating:                    0.
% 7.65/1.50  sup_time_sim_full:                      0.
% 7.65/1.50  sup_time_sim_immed:                     0.
% 7.65/1.50  
% 7.65/1.50  sup_num_of_clauses:                     428
% 7.65/1.50  sup_num_in_active:                      238
% 7.65/1.50  sup_num_in_passive:                     190
% 7.65/1.50  sup_num_of_loops:                       283
% 7.65/1.50  sup_fw_superposition:                   328
% 7.65/1.50  sup_bw_superposition:                   291
% 7.65/1.50  sup_immediate_simplified:               117
% 7.65/1.50  sup_given_eliminated:                   1
% 7.65/1.50  comparisons_done:                       0
% 7.65/1.50  comparisons_avoided:                    18
% 7.65/1.50  
% 7.65/1.50  ------ Simplifications
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  sim_fw_subset_subsumed:                 58
% 7.65/1.50  sim_bw_subset_subsumed:                 27
% 7.65/1.50  sim_fw_subsumed:                        33
% 7.65/1.50  sim_bw_subsumed:                        4
% 7.65/1.50  sim_fw_subsumption_res:                 15
% 7.65/1.50  sim_bw_subsumption_res:                 0
% 7.65/1.50  sim_tautology_del:                      7
% 7.65/1.50  sim_eq_tautology_del:                   15
% 7.65/1.50  sim_eq_res_simp:                        0
% 7.65/1.50  sim_fw_demodulated:                     21
% 7.65/1.50  sim_bw_demodulated:                     26
% 7.65/1.50  sim_light_normalised:                   25
% 7.65/1.50  sim_joinable_taut:                      0
% 7.65/1.50  sim_joinable_simp:                      0
% 7.65/1.50  sim_ac_normalised:                      0
% 7.65/1.50  sim_smt_subsumption:                    0
% 7.65/1.50  
%------------------------------------------------------------------------------
