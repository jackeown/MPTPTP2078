%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:52 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :  265 (18906 expanded)
%              Number of clauses        :  168 (5418 expanded)
%              Number of leaves         :   27 (6273 expanded)
%              Depth                    :   27
%              Number of atoms          :  907 (139046 expanded)
%              Number of equality atoms :  426 (38281 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
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
    inference(flattening,[],[f45])).

fof(f63,plain,(
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

fof(f62,plain,(
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

fof(f61,plain,(
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

fof(f60,plain,
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

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f46,f63,f62,f61,f60])).

fof(f105,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f64])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f64])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f64])).

fof(f104,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f64])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f100,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f64])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f64])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f19,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f108,plain,(
    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f64])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f116,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f93])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f118,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f117,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f92])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2980,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2999,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4121,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2980,c_2999])).

cnf(c_50,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3306,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3307,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3306])).

cnf(c_3483,plain,
    ( ~ m1_subset_1(X0,sK3)
    | r2_hidden(X0,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3894,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3483])).

cnf(c_3895,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3894])).

cnf(c_4346,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4121,c_50,c_35,c_3307,c_3895])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2977,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2985,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6676,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_2985])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2992,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4112,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2977,c_2992])).

cnf(c_6680,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6676,c_4112])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7032,plain,
    ( sK4 = k1_xboole_0
    | k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6680,c_46])).

cnf(c_7033,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7032])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2993,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2991,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3840,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2977,c_2991])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2981,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4179,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3840,c_2981])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2979,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4111,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2979,c_2992])).

cnf(c_4185,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4179,c_4111])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3004,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4664,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4185,c_3004])).

cnf(c_9966,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_4664])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3674,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3315])).

cnf(c_3675,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3674])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4089,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4090,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4089])).

cnf(c_21424,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9966,c_45,c_47,c_3675,c_4090])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_30,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_20,c_30])).

cnf(c_2973,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_3993,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_2973])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_48,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_49,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3671,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3315])).

cnf(c_3672,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3671])).

cnf(c_4086,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4087,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4086])).

cnf(c_4256,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3993,c_48,c_49,c_3672,c_4087])).

cnf(c_21439,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21424,c_4256])).

cnf(c_21627,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | sK4 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7033,c_21439])).

cnf(c_22098,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4346,c_21627])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2996,plain,
    ( k1_funct_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5604,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | k1_funct_1(sK6,X0) = k1_xboole_0
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2996,c_4256])).

cnf(c_7407,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | k1_funct_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5604,c_48,c_49,c_3672,c_4087])).

cnf(c_33,plain,
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
    inference(cnf_transformation,[],[f98])).

cnf(c_2982,plain,
    ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
    | k1_xboole_0 = X0
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X5,X0) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4464,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3840,c_2982])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_44,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_121,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_126,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2316,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3377,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_3378,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3377])).

cnf(c_7886,plain,
    ( m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4464,c_44,c_45,c_46,c_47,c_35,c_121,c_126,c_3378])).

cnf(c_7887,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_7886])).

cnf(c_7898,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4111,c_7887])).

cnf(c_8091,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7898,c_48,c_49,c_4185])).

cnf(c_8092,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8091])).

cnf(c_8100,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_2980,c_8092])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_8119,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_8100,c_34])).

cnf(c_8178,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7407,c_8119])).

cnf(c_22209,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22098,c_8178])).

cnf(c_8328,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8178,c_8119])).

cnf(c_22321,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22209,c_8328])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2983,plain,
    ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X3,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5389,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_2983])).

cnf(c_1184,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
    | sK5 != X2
    | sK4 != X3
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_41])).

cnf(c_1185,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(unflattening,[status(thm)],[c_1184])).

cnf(c_1189,plain,
    ( ~ m1_subset_1(X0,sK3)
    | v1_xboole_0(sK3)
    | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_42,c_40])).

cnf(c_1191,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1189])).

cnf(c_5866,plain,
    ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5389,c_35,c_1191,c_3307])).

cnf(c_5874,plain,
    ( k3_funct_2(sK3,sK4,sK5,sK7) = k1_funct_1(sK5,sK7) ),
    inference(superposition,[status(thm)],[c_2980,c_5866])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2984,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6471,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top
    | m1_subset_1(sK7,sK3) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5874,c_2984])).

cnf(c_7814,plain,
    ( m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6471,c_45,c_46,c_47,c_50,c_35,c_3307])).

cnf(c_7819,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7814,c_2999])).

cnf(c_9541,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7819,c_44])).

cnf(c_22385,plain,
    ( r2_hidden(k1_funct_1(sK5,sK7),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22321,c_9541])).

cnf(c_22415,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22321,c_2977])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2989,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22946,plain,
    ( sK5 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22415,c_2989])).

cnf(c_3363,plain,
    ( ~ v1_funct_2(X0,sK3,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3727,plain,
    ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3363])).

cnf(c_3732,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK3
    | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3727])).

cnf(c_2315,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3739,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_3971,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_3972,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3971])).

cnf(c_3627,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5065,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_3627])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_5066,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2329,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_3466,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK5,sK3,sK4)
    | X0 != sK5
    | X2 != sK4
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_2329])).

cnf(c_4301,plain,
    ( v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK5,sK3,sK4)
    | X1 != sK4
    | X0 != sK3
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3466])).

cnf(c_7593,plain,
    ( v1_funct_2(sK5,sK3,X0)
    | ~ v1_funct_2(sK5,sK3,sK4)
    | X0 != sK4
    | sK5 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4301])).

cnf(c_7595,plain,
    ( X0 != sK4
    | sK5 != sK5
    | sK3 != sK3
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7593])).

cnf(c_7597,plain,
    ( sK5 != sK5
    | sK3 != sK3
    | k1_xboole_0 != sK4
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_funct_2(sK5,sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7595])).

cnf(c_5196,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_2316])).

cnf(c_9625,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_5196])).

cnf(c_9626,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_9625])).

cnf(c_23285,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22946,c_46,c_35,c_121,c_126,c_3732,c_3739,c_3972,c_5065,c_5066,c_7597,c_8328,c_9626,c_22209,c_22415])).

cnf(c_25693,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22385,c_23285])).

cnf(c_22414,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_22321,c_2979])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2986,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22934,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK6) = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22414,c_2986])).

cnf(c_12674,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_12677,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12674])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_13])).

cnf(c_2972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_3611,plain,
    ( r1_tarski(k1_relat_1(sK6),sK4) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_2972])).

cnf(c_3002,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4563,plain,
    ( k1_relat_1(sK6) = sK4
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3611,c_3002])).

cnf(c_5375,plain,
    ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
    | k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4563,c_49,c_3672,c_4087])).

cnf(c_5376,plain,
    ( k1_relat_1(sK6) = sK4
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5375])).

cnf(c_22406,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22321,c_5376])).

cnf(c_22411,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_22321,c_4111])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2988,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23026,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22411,c_2988])).

cnf(c_23230,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22934,c_12677,c_22406,c_22414,c_23026])).

cnf(c_23233,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23230,c_22411])).

cnf(c_24791,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23233,c_4256])).

cnf(c_25697,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) ),
    inference(superposition,[status(thm)],[c_25693,c_24791])).

cnf(c_23333,plain,
    ( k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23285,c_8178])).

cnf(c_25718,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_25697,c_23333])).

cnf(c_23332,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_23285,c_8328])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25718,c_23332])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.19/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/1.51  
% 7.19/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.19/1.51  
% 7.19/1.51  ------  iProver source info
% 7.19/1.51  
% 7.19/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.19/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.19/1.51  git: non_committed_changes: false
% 7.19/1.51  git: last_make_outside_of_git: false
% 7.19/1.51  
% 7.19/1.51  ------ 
% 7.19/1.51  
% 7.19/1.51  ------ Input Options
% 7.19/1.51  
% 7.19/1.51  --out_options                           all
% 7.19/1.51  --tptp_safe_out                         true
% 7.19/1.51  --problem_path                          ""
% 7.19/1.51  --include_path                          ""
% 7.19/1.51  --clausifier                            res/vclausify_rel
% 7.19/1.51  --clausifier_options                    --mode clausify
% 7.19/1.51  --stdin                                 false
% 7.19/1.51  --stats_out                             all
% 7.19/1.51  
% 7.19/1.51  ------ General Options
% 7.19/1.51  
% 7.19/1.51  --fof                                   false
% 7.19/1.51  --time_out_real                         305.
% 7.19/1.51  --time_out_virtual                      -1.
% 7.19/1.51  --symbol_type_check                     false
% 7.19/1.51  --clausify_out                          false
% 7.19/1.51  --sig_cnt_out                           false
% 7.19/1.51  --trig_cnt_out                          false
% 7.19/1.51  --trig_cnt_out_tolerance                1.
% 7.19/1.51  --trig_cnt_out_sk_spl                   false
% 7.19/1.51  --abstr_cl_out                          false
% 7.19/1.51  
% 7.19/1.51  ------ Global Options
% 7.19/1.51  
% 7.19/1.51  --schedule                              default
% 7.19/1.51  --add_important_lit                     false
% 7.19/1.51  --prop_solver_per_cl                    1000
% 7.19/1.51  --min_unsat_core                        false
% 7.19/1.51  --soft_assumptions                      false
% 7.19/1.51  --soft_lemma_size                       3
% 7.19/1.51  --prop_impl_unit_size                   0
% 7.19/1.51  --prop_impl_unit                        []
% 7.19/1.51  --share_sel_clauses                     true
% 7.19/1.51  --reset_solvers                         false
% 7.19/1.51  --bc_imp_inh                            [conj_cone]
% 7.19/1.51  --conj_cone_tolerance                   3.
% 7.19/1.51  --extra_neg_conj                        none
% 7.19/1.51  --large_theory_mode                     true
% 7.19/1.51  --prolific_symb_bound                   200
% 7.19/1.51  --lt_threshold                          2000
% 7.19/1.51  --clause_weak_htbl                      true
% 7.19/1.51  --gc_record_bc_elim                     false
% 7.19/1.51  
% 7.19/1.51  ------ Preprocessing Options
% 7.19/1.51  
% 7.19/1.51  --preprocessing_flag                    true
% 7.19/1.51  --time_out_prep_mult                    0.1
% 7.19/1.51  --splitting_mode                        input
% 7.19/1.51  --splitting_grd                         true
% 7.19/1.51  --splitting_cvd                         false
% 7.19/1.51  --splitting_cvd_svl                     false
% 7.19/1.51  --splitting_nvd                         32
% 7.19/1.51  --sub_typing                            true
% 7.19/1.51  --prep_gs_sim                           true
% 7.19/1.51  --prep_unflatten                        true
% 7.19/1.51  --prep_res_sim                          true
% 7.19/1.51  --prep_upred                            true
% 7.19/1.51  --prep_sem_filter                       exhaustive
% 7.19/1.51  --prep_sem_filter_out                   false
% 7.19/1.51  --pred_elim                             true
% 7.19/1.51  --res_sim_input                         true
% 7.19/1.51  --eq_ax_congr_red                       true
% 7.19/1.51  --pure_diseq_elim                       true
% 7.19/1.51  --brand_transform                       false
% 7.19/1.51  --non_eq_to_eq                          false
% 7.19/1.51  --prep_def_merge                        true
% 7.19/1.51  --prep_def_merge_prop_impl              false
% 7.19/1.51  --prep_def_merge_mbd                    true
% 7.19/1.51  --prep_def_merge_tr_red                 false
% 7.19/1.51  --prep_def_merge_tr_cl                  false
% 7.19/1.51  --smt_preprocessing                     true
% 7.19/1.51  --smt_ac_axioms                         fast
% 7.19/1.51  --preprocessed_out                      false
% 7.19/1.51  --preprocessed_stats                    false
% 7.19/1.51  
% 7.19/1.51  ------ Abstraction refinement Options
% 7.19/1.51  
% 7.19/1.51  --abstr_ref                             []
% 7.19/1.51  --abstr_ref_prep                        false
% 7.19/1.51  --abstr_ref_until_sat                   false
% 7.19/1.51  --abstr_ref_sig_restrict                funpre
% 7.19/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.19/1.51  --abstr_ref_under                       []
% 7.19/1.51  
% 7.19/1.51  ------ SAT Options
% 7.19/1.51  
% 7.19/1.51  --sat_mode                              false
% 7.19/1.51  --sat_fm_restart_options                ""
% 7.19/1.51  --sat_gr_def                            false
% 7.19/1.51  --sat_epr_types                         true
% 7.19/1.51  --sat_non_cyclic_types                  false
% 7.19/1.51  --sat_finite_models                     false
% 7.19/1.51  --sat_fm_lemmas                         false
% 7.19/1.51  --sat_fm_prep                           false
% 7.19/1.51  --sat_fm_uc_incr                        true
% 7.19/1.51  --sat_out_model                         small
% 7.19/1.51  --sat_out_clauses                       false
% 7.19/1.51  
% 7.19/1.51  ------ QBF Options
% 7.19/1.51  
% 7.19/1.51  --qbf_mode                              false
% 7.19/1.51  --qbf_elim_univ                         false
% 7.19/1.51  --qbf_dom_inst                          none
% 7.19/1.51  --qbf_dom_pre_inst                      false
% 7.19/1.51  --qbf_sk_in                             false
% 7.19/1.51  --qbf_pred_elim                         true
% 7.19/1.51  --qbf_split                             512
% 7.19/1.51  
% 7.19/1.51  ------ BMC1 Options
% 7.19/1.51  
% 7.19/1.51  --bmc1_incremental                      false
% 7.19/1.51  --bmc1_axioms                           reachable_all
% 7.19/1.51  --bmc1_min_bound                        0
% 7.19/1.51  --bmc1_max_bound                        -1
% 7.19/1.51  --bmc1_max_bound_default                -1
% 7.19/1.51  --bmc1_symbol_reachability              true
% 7.19/1.51  --bmc1_property_lemmas                  false
% 7.19/1.51  --bmc1_k_induction                      false
% 7.19/1.51  --bmc1_non_equiv_states                 false
% 7.19/1.51  --bmc1_deadlock                         false
% 7.19/1.51  --bmc1_ucm                              false
% 7.19/1.51  --bmc1_add_unsat_core                   none
% 7.19/1.51  --bmc1_unsat_core_children              false
% 7.19/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.19/1.51  --bmc1_out_stat                         full
% 7.19/1.51  --bmc1_ground_init                      false
% 7.19/1.51  --bmc1_pre_inst_next_state              false
% 7.19/1.51  --bmc1_pre_inst_state                   false
% 7.19/1.51  --bmc1_pre_inst_reach_state             false
% 7.19/1.51  --bmc1_out_unsat_core                   false
% 7.19/1.51  --bmc1_aig_witness_out                  false
% 7.19/1.51  --bmc1_verbose                          false
% 7.19/1.51  --bmc1_dump_clauses_tptp                false
% 7.19/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.19/1.51  --bmc1_dump_file                        -
% 7.19/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.19/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.19/1.51  --bmc1_ucm_extend_mode                  1
% 7.19/1.51  --bmc1_ucm_init_mode                    2
% 7.19/1.51  --bmc1_ucm_cone_mode                    none
% 7.19/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.19/1.51  --bmc1_ucm_relax_model                  4
% 7.19/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.19/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.19/1.51  --bmc1_ucm_layered_model                none
% 7.19/1.51  --bmc1_ucm_max_lemma_size               10
% 7.19/1.51  
% 7.19/1.51  ------ AIG Options
% 7.19/1.51  
% 7.19/1.51  --aig_mode                              false
% 7.19/1.51  
% 7.19/1.51  ------ Instantiation Options
% 7.19/1.51  
% 7.19/1.51  --instantiation_flag                    true
% 7.19/1.51  --inst_sos_flag                         false
% 7.19/1.51  --inst_sos_phase                        true
% 7.19/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.19/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.19/1.51  --inst_lit_sel_side                     num_symb
% 7.19/1.51  --inst_solver_per_active                1400
% 7.19/1.51  --inst_solver_calls_frac                1.
% 7.19/1.51  --inst_passive_queue_type               priority_queues
% 7.19/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.19/1.51  --inst_passive_queues_freq              [25;2]
% 7.19/1.51  --inst_dismatching                      true
% 7.19/1.51  --inst_eager_unprocessed_to_passive     true
% 7.19/1.51  --inst_prop_sim_given                   true
% 7.19/1.51  --inst_prop_sim_new                     false
% 7.19/1.51  --inst_subs_new                         false
% 7.19/1.51  --inst_eq_res_simp                      false
% 7.19/1.51  --inst_subs_given                       false
% 7.19/1.51  --inst_orphan_elimination               true
% 7.19/1.51  --inst_learning_loop_flag               true
% 7.19/1.51  --inst_learning_start                   3000
% 7.19/1.51  --inst_learning_factor                  2
% 7.19/1.51  --inst_start_prop_sim_after_learn       3
% 7.19/1.51  --inst_sel_renew                        solver
% 7.19/1.51  --inst_lit_activity_flag                true
% 7.19/1.51  --inst_restr_to_given                   false
% 7.19/1.51  --inst_activity_threshold               500
% 7.19/1.51  --inst_out_proof                        true
% 7.19/1.51  
% 7.19/1.51  ------ Resolution Options
% 7.19/1.51  
% 7.19/1.51  --resolution_flag                       true
% 7.19/1.51  --res_lit_sel                           adaptive
% 7.19/1.51  --res_lit_sel_side                      none
% 7.19/1.51  --res_ordering                          kbo
% 7.19/1.51  --res_to_prop_solver                    active
% 7.19/1.51  --res_prop_simpl_new                    false
% 7.19/1.51  --res_prop_simpl_given                  true
% 7.19/1.51  --res_passive_queue_type                priority_queues
% 7.19/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.19/1.51  --res_passive_queues_freq               [15;5]
% 7.19/1.51  --res_forward_subs                      full
% 7.19/1.51  --res_backward_subs                     full
% 7.19/1.51  --res_forward_subs_resolution           true
% 7.19/1.51  --res_backward_subs_resolution          true
% 7.19/1.51  --res_orphan_elimination                true
% 7.19/1.51  --res_time_limit                        2.
% 7.19/1.51  --res_out_proof                         true
% 7.19/1.51  
% 7.19/1.51  ------ Superposition Options
% 7.19/1.51  
% 7.19/1.51  --superposition_flag                    true
% 7.19/1.51  --sup_passive_queue_type                priority_queues
% 7.19/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.19/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.19/1.51  --demod_completeness_check              fast
% 7.19/1.51  --demod_use_ground                      true
% 7.19/1.51  --sup_to_prop_solver                    passive
% 7.19/1.51  --sup_prop_simpl_new                    true
% 7.19/1.51  --sup_prop_simpl_given                  true
% 7.19/1.51  --sup_fun_splitting                     false
% 7.19/1.51  --sup_smt_interval                      50000
% 7.19/1.51  
% 7.19/1.51  ------ Superposition Simplification Setup
% 7.19/1.51  
% 7.19/1.51  --sup_indices_passive                   []
% 7.19/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.19/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.51  --sup_full_bw                           [BwDemod]
% 7.19/1.51  --sup_immed_triv                        [TrivRules]
% 7.19/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.51  --sup_immed_bw_main                     []
% 7.19/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.19/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.51  
% 7.19/1.51  ------ Combination Options
% 7.19/1.51  
% 7.19/1.51  --comb_res_mult                         3
% 7.19/1.51  --comb_sup_mult                         2
% 7.19/1.51  --comb_inst_mult                        10
% 7.19/1.51  
% 7.19/1.51  ------ Debug Options
% 7.19/1.51  
% 7.19/1.51  --dbg_backtrace                         false
% 7.19/1.51  --dbg_dump_prop_clauses                 false
% 7.19/1.51  --dbg_dump_prop_clauses_file            -
% 7.19/1.51  --dbg_out_stat                          false
% 7.19/1.51  ------ Parsing...
% 7.19/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.19/1.51  
% 7.19/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.19/1.51  
% 7.19/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.19/1.51  
% 7.19/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.19/1.51  ------ Proving...
% 7.19/1.51  ------ Problem Properties 
% 7.19/1.51  
% 7.19/1.51  
% 7.19/1.51  clauses                                 39
% 7.19/1.51  conjectures                             10
% 7.19/1.52  EPR                                     13
% 7.19/1.52  Horn                                    28
% 7.19/1.52  unary                                   13
% 7.19/1.52  binary                                  7
% 7.19/1.52  lits                                    107
% 7.19/1.52  lits eq                                 21
% 7.19/1.52  fd_pure                                 0
% 7.19/1.52  fd_pseudo                               0
% 7.19/1.52  fd_cond                                 5
% 7.19/1.52  fd_pseudo_cond                          2
% 7.19/1.52  AC symbols                              0
% 7.19/1.52  
% 7.19/1.52  ------ Schedule dynamic 5 is on 
% 7.19/1.52  
% 7.19/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.19/1.52  
% 7.19/1.52  
% 7.19/1.52  ------ 
% 7.19/1.52  Current options:
% 7.19/1.52  ------ 
% 7.19/1.52  
% 7.19/1.52  ------ Input Options
% 7.19/1.52  
% 7.19/1.52  --out_options                           all
% 7.19/1.52  --tptp_safe_out                         true
% 7.19/1.52  --problem_path                          ""
% 7.19/1.52  --include_path                          ""
% 7.19/1.52  --clausifier                            res/vclausify_rel
% 7.19/1.52  --clausifier_options                    --mode clausify
% 7.19/1.52  --stdin                                 false
% 7.19/1.52  --stats_out                             all
% 7.19/1.52  
% 7.19/1.52  ------ General Options
% 7.19/1.52  
% 7.19/1.52  --fof                                   false
% 7.19/1.52  --time_out_real                         305.
% 7.19/1.52  --time_out_virtual                      -1.
% 7.19/1.52  --symbol_type_check                     false
% 7.19/1.52  --clausify_out                          false
% 7.19/1.52  --sig_cnt_out                           false
% 7.19/1.52  --trig_cnt_out                          false
% 7.19/1.52  --trig_cnt_out_tolerance                1.
% 7.19/1.52  --trig_cnt_out_sk_spl                   false
% 7.19/1.52  --abstr_cl_out                          false
% 7.19/1.52  
% 7.19/1.52  ------ Global Options
% 7.19/1.52  
% 7.19/1.52  --schedule                              default
% 7.19/1.52  --add_important_lit                     false
% 7.19/1.52  --prop_solver_per_cl                    1000
% 7.19/1.52  --min_unsat_core                        false
% 7.19/1.52  --soft_assumptions                      false
% 7.19/1.52  --soft_lemma_size                       3
% 7.19/1.52  --prop_impl_unit_size                   0
% 7.19/1.52  --prop_impl_unit                        []
% 7.19/1.52  --share_sel_clauses                     true
% 7.19/1.52  --reset_solvers                         false
% 7.19/1.52  --bc_imp_inh                            [conj_cone]
% 7.19/1.52  --conj_cone_tolerance                   3.
% 7.19/1.52  --extra_neg_conj                        none
% 7.19/1.52  --large_theory_mode                     true
% 7.19/1.52  --prolific_symb_bound                   200
% 7.19/1.52  --lt_threshold                          2000
% 7.19/1.52  --clause_weak_htbl                      true
% 7.19/1.52  --gc_record_bc_elim                     false
% 7.19/1.52  
% 7.19/1.52  ------ Preprocessing Options
% 7.19/1.52  
% 7.19/1.52  --preprocessing_flag                    true
% 7.19/1.52  --time_out_prep_mult                    0.1
% 7.19/1.52  --splitting_mode                        input
% 7.19/1.52  --splitting_grd                         true
% 7.19/1.52  --splitting_cvd                         false
% 7.19/1.52  --splitting_cvd_svl                     false
% 7.19/1.52  --splitting_nvd                         32
% 7.19/1.52  --sub_typing                            true
% 7.19/1.52  --prep_gs_sim                           true
% 7.19/1.52  --prep_unflatten                        true
% 7.19/1.52  --prep_res_sim                          true
% 7.19/1.52  --prep_upred                            true
% 7.19/1.52  --prep_sem_filter                       exhaustive
% 7.19/1.52  --prep_sem_filter_out                   false
% 7.19/1.52  --pred_elim                             true
% 7.19/1.52  --res_sim_input                         true
% 7.19/1.52  --eq_ax_congr_red                       true
% 7.19/1.52  --pure_diseq_elim                       true
% 7.19/1.52  --brand_transform                       false
% 7.19/1.52  --non_eq_to_eq                          false
% 7.19/1.52  --prep_def_merge                        true
% 7.19/1.52  --prep_def_merge_prop_impl              false
% 7.19/1.52  --prep_def_merge_mbd                    true
% 7.19/1.52  --prep_def_merge_tr_red                 false
% 7.19/1.52  --prep_def_merge_tr_cl                  false
% 7.19/1.52  --smt_preprocessing                     true
% 7.19/1.52  --smt_ac_axioms                         fast
% 7.19/1.52  --preprocessed_out                      false
% 7.19/1.52  --preprocessed_stats                    false
% 7.19/1.52  
% 7.19/1.52  ------ Abstraction refinement Options
% 7.19/1.52  
% 7.19/1.52  --abstr_ref                             []
% 7.19/1.52  --abstr_ref_prep                        false
% 7.19/1.52  --abstr_ref_until_sat                   false
% 7.19/1.52  --abstr_ref_sig_restrict                funpre
% 7.19/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.19/1.52  --abstr_ref_under                       []
% 7.19/1.52  
% 7.19/1.52  ------ SAT Options
% 7.19/1.52  
% 7.19/1.52  --sat_mode                              false
% 7.19/1.52  --sat_fm_restart_options                ""
% 7.19/1.52  --sat_gr_def                            false
% 7.19/1.52  --sat_epr_types                         true
% 7.19/1.52  --sat_non_cyclic_types                  false
% 7.19/1.52  --sat_finite_models                     false
% 7.19/1.52  --sat_fm_lemmas                         false
% 7.19/1.52  --sat_fm_prep                           false
% 7.19/1.52  --sat_fm_uc_incr                        true
% 7.19/1.52  --sat_out_model                         small
% 7.19/1.52  --sat_out_clauses                       false
% 7.19/1.52  
% 7.19/1.52  ------ QBF Options
% 7.19/1.52  
% 7.19/1.52  --qbf_mode                              false
% 7.19/1.52  --qbf_elim_univ                         false
% 7.19/1.52  --qbf_dom_inst                          none
% 7.19/1.52  --qbf_dom_pre_inst                      false
% 7.19/1.52  --qbf_sk_in                             false
% 7.19/1.52  --qbf_pred_elim                         true
% 7.19/1.52  --qbf_split                             512
% 7.19/1.52  
% 7.19/1.52  ------ BMC1 Options
% 7.19/1.52  
% 7.19/1.52  --bmc1_incremental                      false
% 7.19/1.52  --bmc1_axioms                           reachable_all
% 7.19/1.52  --bmc1_min_bound                        0
% 7.19/1.52  --bmc1_max_bound                        -1
% 7.19/1.52  --bmc1_max_bound_default                -1
% 7.19/1.52  --bmc1_symbol_reachability              true
% 7.19/1.52  --bmc1_property_lemmas                  false
% 7.19/1.52  --bmc1_k_induction                      false
% 7.19/1.52  --bmc1_non_equiv_states                 false
% 7.19/1.52  --bmc1_deadlock                         false
% 7.19/1.52  --bmc1_ucm                              false
% 7.19/1.52  --bmc1_add_unsat_core                   none
% 7.19/1.52  --bmc1_unsat_core_children              false
% 7.19/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.19/1.52  --bmc1_out_stat                         full
% 7.19/1.52  --bmc1_ground_init                      false
% 7.19/1.52  --bmc1_pre_inst_next_state              false
% 7.19/1.52  --bmc1_pre_inst_state                   false
% 7.19/1.52  --bmc1_pre_inst_reach_state             false
% 7.19/1.52  --bmc1_out_unsat_core                   false
% 7.19/1.52  --bmc1_aig_witness_out                  false
% 7.19/1.52  --bmc1_verbose                          false
% 7.19/1.52  --bmc1_dump_clauses_tptp                false
% 7.19/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.19/1.52  --bmc1_dump_file                        -
% 7.19/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.19/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.19/1.52  --bmc1_ucm_extend_mode                  1
% 7.19/1.52  --bmc1_ucm_init_mode                    2
% 7.19/1.52  --bmc1_ucm_cone_mode                    none
% 7.19/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.19/1.52  --bmc1_ucm_relax_model                  4
% 7.19/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.19/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.19/1.52  --bmc1_ucm_layered_model                none
% 7.19/1.52  --bmc1_ucm_max_lemma_size               10
% 7.19/1.52  
% 7.19/1.52  ------ AIG Options
% 7.19/1.52  
% 7.19/1.52  --aig_mode                              false
% 7.19/1.52  
% 7.19/1.52  ------ Instantiation Options
% 7.19/1.52  
% 7.19/1.52  --instantiation_flag                    true
% 7.19/1.52  --inst_sos_flag                         false
% 7.19/1.52  --inst_sos_phase                        true
% 7.19/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.19/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.19/1.52  --inst_lit_sel_side                     none
% 7.19/1.52  --inst_solver_per_active                1400
% 7.19/1.52  --inst_solver_calls_frac                1.
% 7.19/1.52  --inst_passive_queue_type               priority_queues
% 7.19/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.19/1.52  --inst_passive_queues_freq              [25;2]
% 7.19/1.52  --inst_dismatching                      true
% 7.19/1.52  --inst_eager_unprocessed_to_passive     true
% 7.19/1.52  --inst_prop_sim_given                   true
% 7.19/1.52  --inst_prop_sim_new                     false
% 7.19/1.52  --inst_subs_new                         false
% 7.19/1.52  --inst_eq_res_simp                      false
% 7.19/1.52  --inst_subs_given                       false
% 7.19/1.52  --inst_orphan_elimination               true
% 7.19/1.52  --inst_learning_loop_flag               true
% 7.19/1.52  --inst_learning_start                   3000
% 7.19/1.52  --inst_learning_factor                  2
% 7.19/1.52  --inst_start_prop_sim_after_learn       3
% 7.19/1.52  --inst_sel_renew                        solver
% 7.19/1.52  --inst_lit_activity_flag                true
% 7.19/1.52  --inst_restr_to_given                   false
% 7.19/1.52  --inst_activity_threshold               500
% 7.19/1.52  --inst_out_proof                        true
% 7.19/1.52  
% 7.19/1.52  ------ Resolution Options
% 7.19/1.52  
% 7.19/1.52  --resolution_flag                       false
% 7.19/1.52  --res_lit_sel                           adaptive
% 7.19/1.52  --res_lit_sel_side                      none
% 7.19/1.52  --res_ordering                          kbo
% 7.19/1.52  --res_to_prop_solver                    active
% 7.19/1.52  --res_prop_simpl_new                    false
% 7.19/1.52  --res_prop_simpl_given                  true
% 7.19/1.52  --res_passive_queue_type                priority_queues
% 7.19/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.19/1.52  --res_passive_queues_freq               [15;5]
% 7.19/1.52  --res_forward_subs                      full
% 7.19/1.52  --res_backward_subs                     full
% 7.19/1.52  --res_forward_subs_resolution           true
% 7.19/1.52  --res_backward_subs_resolution          true
% 7.19/1.52  --res_orphan_elimination                true
% 7.19/1.52  --res_time_limit                        2.
% 7.19/1.52  --res_out_proof                         true
% 7.19/1.52  
% 7.19/1.52  ------ Superposition Options
% 7.19/1.52  
% 7.19/1.52  --superposition_flag                    true
% 7.19/1.52  --sup_passive_queue_type                priority_queues
% 7.19/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.19/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.19/1.52  --demod_completeness_check              fast
% 7.19/1.52  --demod_use_ground                      true
% 7.19/1.52  --sup_to_prop_solver                    passive
% 7.19/1.52  --sup_prop_simpl_new                    true
% 7.19/1.52  --sup_prop_simpl_given                  true
% 7.19/1.52  --sup_fun_splitting                     false
% 7.19/1.52  --sup_smt_interval                      50000
% 7.19/1.52  
% 7.19/1.52  ------ Superposition Simplification Setup
% 7.19/1.52  
% 7.19/1.52  --sup_indices_passive                   []
% 7.19/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.19/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.52  --sup_full_bw                           [BwDemod]
% 7.19/1.52  --sup_immed_triv                        [TrivRules]
% 7.19/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.52  --sup_immed_bw_main                     []
% 7.19/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.19/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.52  
% 7.19/1.52  ------ Combination Options
% 7.19/1.52  
% 7.19/1.52  --comb_res_mult                         3
% 7.19/1.52  --comb_sup_mult                         2
% 7.19/1.52  --comb_inst_mult                        10
% 7.19/1.52  
% 7.19/1.52  ------ Debug Options
% 7.19/1.52  
% 7.19/1.52  --dbg_backtrace                         false
% 7.19/1.52  --dbg_dump_prop_clauses                 false
% 7.19/1.52  --dbg_dump_prop_clauses_file            -
% 7.19/1.52  --dbg_out_stat                          false
% 7.19/1.52  
% 7.19/1.52  
% 7.19/1.52  
% 7.19/1.52  
% 7.19/1.52  ------ Proving...
% 7.19/1.52  
% 7.19/1.52  
% 7.19/1.52  % SZS status Theorem for theBenchmark.p
% 7.19/1.52  
% 7.19/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.19/1.52  
% 7.19/1.52  fof(f20,conjecture,(
% 7.19/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f21,negated_conjecture,(
% 7.19/1.52    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.19/1.52    inference(negated_conjecture,[],[f20])).
% 7.19/1.52  
% 7.19/1.52  fof(f45,plain,(
% 7.19/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.19/1.52    inference(ennf_transformation,[],[f21])).
% 7.19/1.52  
% 7.19/1.52  fof(f46,plain,(
% 7.19/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.19/1.52    inference(flattening,[],[f45])).
% 7.19/1.52  
% 7.19/1.52  fof(f63,plain,(
% 7.19/1.52    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) != k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 7.19/1.52    introduced(choice_axiom,[])).
% 7.19/1.52  
% 7.19/1.52  fof(f62,plain,(
% 7.19/1.52    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) != k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 7.19/1.52    introduced(choice_axiom,[])).
% 7.19/1.52  
% 7.19/1.52  fof(f61,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 7.19/1.52    introduced(choice_axiom,[])).
% 7.19/1.52  
% 7.19/1.52  fof(f60,plain,(
% 7.19/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) != k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 7.19/1.52    introduced(choice_axiom,[])).
% 7.19/1.52  
% 7.19/1.52  fof(f64,plain,(
% 7.19/1.52    (((k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 7.19/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f46,f63,f62,f61,f60])).
% 7.19/1.52  
% 7.19/1.52  fof(f105,plain,(
% 7.19/1.52    m1_subset_1(sK7,sK3)),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f6,axiom,(
% 7.19/1.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f24,plain,(
% 7.19/1.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.19/1.52    inference(ennf_transformation,[],[f6])).
% 7.19/1.52  
% 7.19/1.52  fof(f25,plain,(
% 7.19/1.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.19/1.52    inference(flattening,[],[f24])).
% 7.19/1.52  
% 7.19/1.52  fof(f75,plain,(
% 7.19/1.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f25])).
% 7.19/1.52  
% 7.19/1.52  fof(f107,plain,(
% 7.19/1.52    k1_xboole_0 != sK3),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f3,axiom,(
% 7.19/1.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f23,plain,(
% 7.19/1.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.19/1.52    inference(ennf_transformation,[],[f3])).
% 7.19/1.52  
% 7.19/1.52  fof(f70,plain,(
% 7.19/1.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f23])).
% 7.19/1.52  
% 7.19/1.52  fof(f102,plain,(
% 7.19/1.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f15,axiom,(
% 7.19/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f35,plain,(
% 7.19/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.19/1.52    inference(ennf_transformation,[],[f15])).
% 7.19/1.52  
% 7.19/1.52  fof(f36,plain,(
% 7.19/1.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.19/1.52    inference(flattening,[],[f35])).
% 7.19/1.52  
% 7.19/1.52  fof(f59,plain,(
% 7.19/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.19/1.52    inference(nnf_transformation,[],[f36])).
% 7.19/1.52  
% 7.19/1.52  fof(f89,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f59])).
% 7.19/1.52  
% 7.19/1.52  fof(f13,axiom,(
% 7.19/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f33,plain,(
% 7.19/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.19/1.52    inference(ennf_transformation,[],[f13])).
% 7.19/1.52  
% 7.19/1.52  fof(f87,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f33])).
% 7.19/1.52  
% 7.19/1.52  fof(f101,plain,(
% 7.19/1.52    v1_funct_2(sK5,sK3,sK4)),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f11,axiom,(
% 7.19/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f30,plain,(
% 7.19/1.52    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.19/1.52    inference(ennf_transformation,[],[f11])).
% 7.19/1.52  
% 7.19/1.52  fof(f31,plain,(
% 7.19/1.52    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.19/1.52    inference(flattening,[],[f30])).
% 7.19/1.52  
% 7.19/1.52  fof(f84,plain,(
% 7.19/1.52    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f31])).
% 7.19/1.52  
% 7.19/1.52  fof(f14,axiom,(
% 7.19/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f34,plain,(
% 7.19/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.19/1.52    inference(ennf_transformation,[],[f14])).
% 7.19/1.52  
% 7.19/1.52  fof(f88,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f34])).
% 7.19/1.52  
% 7.19/1.52  fof(f106,plain,(
% 7.19/1.52    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f104,plain,(
% 7.19/1.52    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f2,axiom,(
% 7.19/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f22,plain,(
% 7.19/1.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.19/1.52    inference(ennf_transformation,[],[f2])).
% 7.19/1.52  
% 7.19/1.52  fof(f51,plain,(
% 7.19/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.19/1.52    inference(nnf_transformation,[],[f22])).
% 7.19/1.52  
% 7.19/1.52  fof(f52,plain,(
% 7.19/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.19/1.52    inference(rectify,[],[f51])).
% 7.19/1.52  
% 7.19/1.52  fof(f53,plain,(
% 7.19/1.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.19/1.52    introduced(choice_axiom,[])).
% 7.19/1.52  
% 7.19/1.52  fof(f54,plain,(
% 7.19/1.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.19/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 7.19/1.52  
% 7.19/1.52  fof(f67,plain,(
% 7.19/1.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f54])).
% 7.19/1.52  
% 7.19/1.52  fof(f100,plain,(
% 7.19/1.52    v1_funct_1(sK5)),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f7,axiom,(
% 7.19/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f26,plain,(
% 7.19/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.19/1.52    inference(ennf_transformation,[],[f7])).
% 7.19/1.52  
% 7.19/1.52  fof(f76,plain,(
% 7.19/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f26])).
% 7.19/1.52  
% 7.19/1.52  fof(f9,axiom,(
% 7.19/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f79,plain,(
% 7.19/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f9])).
% 7.19/1.52  
% 7.19/1.52  fof(f12,axiom,(
% 7.19/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f32,plain,(
% 7.19/1.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.19/1.52    inference(ennf_transformation,[],[f12])).
% 7.19/1.52  
% 7.19/1.52  fof(f86,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f32])).
% 7.19/1.52  
% 7.19/1.52  fof(f16,axiom,(
% 7.19/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f37,plain,(
% 7.19/1.52    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.19/1.52    inference(ennf_transformation,[],[f16])).
% 7.19/1.52  
% 7.19/1.52  fof(f38,plain,(
% 7.19/1.52    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.19/1.52    inference(flattening,[],[f37])).
% 7.19/1.52  
% 7.19/1.52  fof(f95,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f38])).
% 7.19/1.52  
% 7.19/1.52  fof(f103,plain,(
% 7.19/1.52    v1_funct_1(sK6)),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f10,axiom,(
% 7.19/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f28,plain,(
% 7.19/1.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.19/1.52    inference(ennf_transformation,[],[f10])).
% 7.19/1.52  
% 7.19/1.52  fof(f29,plain,(
% 7.19/1.52    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.19/1.52    inference(flattening,[],[f28])).
% 7.19/1.52  
% 7.19/1.52  fof(f58,plain,(
% 7.19/1.52    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.19/1.52    inference(nnf_transformation,[],[f29])).
% 7.19/1.52  
% 7.19/1.52  fof(f83,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2 | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f58])).
% 7.19/1.52  
% 7.19/1.52  fof(f111,plain,(
% 7.19/1.52    ( ! [X0,X1] : (k1_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.19/1.52    inference(equality_resolution,[],[f83])).
% 7.19/1.52  
% 7.19/1.52  fof(f19,axiom,(
% 7.19/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f43,plain,(
% 7.19/1.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 7.19/1.52    inference(ennf_transformation,[],[f19])).
% 7.19/1.52  
% 7.19/1.52  fof(f44,plain,(
% 7.19/1.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 7.19/1.52    inference(flattening,[],[f43])).
% 7.19/1.52  
% 7.19/1.52  fof(f98,plain,(
% 7.19/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f44])).
% 7.19/1.52  
% 7.19/1.52  fof(f99,plain,(
% 7.19/1.52    ~v1_xboole_0(sK4)),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f5,axiom,(
% 7.19/1.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f74,plain,(
% 7.19/1.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f5])).
% 7.19/1.52  
% 7.19/1.52  fof(f4,axiom,(
% 7.19/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f55,plain,(
% 7.19/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.19/1.52    inference(nnf_transformation,[],[f4])).
% 7.19/1.52  
% 7.19/1.52  fof(f56,plain,(
% 7.19/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.19/1.52    inference(flattening,[],[f55])).
% 7.19/1.52  
% 7.19/1.52  fof(f73,plain,(
% 7.19/1.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f56])).
% 7.19/1.52  
% 7.19/1.52  fof(f108,plain,(
% 7.19/1.52    k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7))),
% 7.19/1.52    inference(cnf_transformation,[],[f64])).
% 7.19/1.52  
% 7.19/1.52  fof(f18,axiom,(
% 7.19/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f41,plain,(
% 7.19/1.52    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.19/1.52    inference(ennf_transformation,[],[f18])).
% 7.19/1.52  
% 7.19/1.52  fof(f42,plain,(
% 7.19/1.52    ! [X0,X1,X2,X3] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.19/1.52    inference(flattening,[],[f41])).
% 7.19/1.52  
% 7.19/1.52  fof(f97,plain,(
% 7.19/1.52    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f42])).
% 7.19/1.52  
% 7.19/1.52  fof(f17,axiom,(
% 7.19/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f39,plain,(
% 7.19/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 7.19/1.52    inference(ennf_transformation,[],[f17])).
% 7.19/1.52  
% 7.19/1.52  fof(f40,plain,(
% 7.19/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 7.19/1.52    inference(flattening,[],[f39])).
% 7.19/1.52  
% 7.19/1.52  fof(f96,plain,(
% 7.19/1.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f40])).
% 7.19/1.52  
% 7.19/1.52  fof(f93,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f59])).
% 7.19/1.52  
% 7.19/1.52  fof(f116,plain,(
% 7.19/1.52    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.19/1.52    inference(equality_resolution,[],[f93])).
% 7.19/1.52  
% 7.19/1.52  fof(f72,plain,(
% 7.19/1.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.19/1.52    inference(cnf_transformation,[],[f56])).
% 7.19/1.52  
% 7.19/1.52  fof(f109,plain,(
% 7.19/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.19/1.52    inference(equality_resolution,[],[f72])).
% 7.19/1.52  
% 7.19/1.52  fof(f90,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f59])).
% 7.19/1.52  
% 7.19/1.52  fof(f118,plain,(
% 7.19/1.52    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.19/1.52    inference(equality_resolution,[],[f90])).
% 7.19/1.52  
% 7.19/1.52  fof(f85,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f32])).
% 7.19/1.52  
% 7.19/1.52  fof(f8,axiom,(
% 7.19/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.19/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.52  
% 7.19/1.52  fof(f27,plain,(
% 7.19/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.19/1.52    inference(ennf_transformation,[],[f8])).
% 7.19/1.52  
% 7.19/1.52  fof(f57,plain,(
% 7.19/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.19/1.52    inference(nnf_transformation,[],[f27])).
% 7.19/1.52  
% 7.19/1.52  fof(f77,plain,(
% 7.19/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.19/1.52    inference(cnf_transformation,[],[f57])).
% 7.19/1.52  
% 7.19/1.52  fof(f92,plain,(
% 7.19/1.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.52    inference(cnf_transformation,[],[f59])).
% 7.19/1.52  
% 7.19/1.52  fof(f117,plain,(
% 7.19/1.52    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.19/1.52    inference(equality_resolution,[],[f92])).
% 7.19/1.52  
% 7.19/1.52  cnf(c_37,negated_conjecture,
% 7.19/1.52      ( m1_subset_1(sK7,sK3) ),
% 7.19/1.52      inference(cnf_transformation,[],[f105]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2980,plain,
% 7.19/1.52      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_10,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.19/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2999,plain,
% 7.19/1.52      ( m1_subset_1(X0,X1) != iProver_top
% 7.19/1.52      | r2_hidden(X0,X1) = iProver_top
% 7.19/1.52      | v1_xboole_0(X1) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4121,plain,
% 7.19/1.52      ( r2_hidden(sK7,sK3) = iProver_top
% 7.19/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2980,c_2999]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_50,plain,
% 7.19/1.52      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_35,negated_conjecture,
% 7.19/1.52      ( k1_xboole_0 != sK3 ),
% 7.19/1.52      inference(cnf_transformation,[],[f107]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5,plain,
% 7.19/1.52      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.19/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3306,plain,
% 7.19/1.52      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_5]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3307,plain,
% 7.19/1.52      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_3306]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3483,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,sK3) | r2_hidden(X0,sK3) | v1_xboole_0(sK3) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_10]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3894,plain,
% 7.19/1.52      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3483]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3895,plain,
% 7.19/1.52      ( m1_subset_1(sK7,sK3) != iProver_top
% 7.19/1.52      | r2_hidden(sK7,sK3) = iProver_top
% 7.19/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_3894]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4346,plain,
% 7.19/1.52      ( r2_hidden(sK7,sK3) = iProver_top ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_4121,c_50,c_35,c_3307,c_3895]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_40,negated_conjecture,
% 7.19/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.19/1.52      inference(cnf_transformation,[],[f102]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2977,plain,
% 7.19/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_29,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.19/1.52      | k1_xboole_0 = X2 ),
% 7.19/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2985,plain,
% 7.19/1.52      ( k1_relset_1(X0,X1,X2) = X0
% 7.19/1.52      | k1_xboole_0 = X1
% 7.19/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.19/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_6676,plain,
% 7.19/1.52      ( k1_relset_1(sK3,sK4,sK5) = sK3
% 7.19/1.52      | sK4 = k1_xboole_0
% 7.19/1.52      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2977,c_2985]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.19/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2992,plain,
% 7.19/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.19/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4112,plain,
% 7.19/1.52      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2977,c_2992]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_6680,plain,
% 7.19/1.52      ( k1_relat_1(sK5) = sK3
% 7.19/1.52      | sK4 = k1_xboole_0
% 7.19/1.52      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_6676,c_4112]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_41,negated_conjecture,
% 7.19/1.52      ( v1_funct_2(sK5,sK3,sK4) ),
% 7.19/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_46,plain,
% 7.19/1.52      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7032,plain,
% 7.19/1.52      ( sK4 = k1_xboole_0 | k1_relat_1(sK5) = sK3 ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_6680,c_46]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7033,plain,
% 7.19/1.52      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 7.19/1.52      inference(renaming,[status(thm)],[c_7032]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_19,plain,
% 7.19/1.52      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.19/1.52      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.19/1.52      | ~ v1_funct_1(X1)
% 7.19/1.52      | ~ v1_relat_1(X1) ),
% 7.19/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2993,plain,
% 7.19/1.52      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 7.19/1.52      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 7.19/1.52      | v1_funct_1(X1) != iProver_top
% 7.19/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_23,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.19/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2991,plain,
% 7.19/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.19/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3840,plain,
% 7.19/1.52      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2977,c_2991]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_36,negated_conjecture,
% 7.19/1.52      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 7.19/1.52      inference(cnf_transformation,[],[f106]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2981,plain,
% 7.19/1.52      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4179,plain,
% 7.19/1.52      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_3840,c_2981]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_38,negated_conjecture,
% 7.19/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.19/1.52      inference(cnf_transformation,[],[f104]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2979,plain,
% 7.19/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4111,plain,
% 7.19/1.52      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2979,c_2992]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4185,plain,
% 7.19/1.52      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 7.19/1.52      inference(light_normalisation,[status(thm)],[c_4179,c_4111]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4,plain,
% 7.19/1.52      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.19/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3004,plain,
% 7.19/1.52      ( r1_tarski(X0,X1) != iProver_top
% 7.19/1.52      | r2_hidden(X2,X0) != iProver_top
% 7.19/1.52      | r2_hidden(X2,X1) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4664,plain,
% 7.19/1.52      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 7.19/1.52      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_4185,c_3004]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_9966,plain,
% 7.19/1.52      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.19/1.52      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top
% 7.19/1.52      | v1_funct_1(sK5) != iProver_top
% 7.19/1.52      | v1_relat_1(sK5) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2993,c_4664]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_42,negated_conjecture,
% 7.19/1.52      ( v1_funct_1(sK5) ),
% 7.19/1.52      inference(cnf_transformation,[],[f100]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_45,plain,
% 7.19/1.52      ( v1_funct_1(sK5) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_47,plain,
% 7.19/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_11,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.19/1.52      | ~ v1_relat_1(X1)
% 7.19/1.52      | v1_relat_1(X0) ),
% 7.19/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3315,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | v1_relat_1(X0)
% 7.19/1.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_11]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3674,plain,
% 7.19/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.19/1.52      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 7.19/1.52      | v1_relat_1(sK5) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3315]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3675,plain,
% 7.19/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.19/1.52      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 7.19/1.52      | v1_relat_1(sK5) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_3674]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_14,plain,
% 7.19/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.19/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4089,plain,
% 7.19/1.52      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_14]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4090,plain,
% 7.19/1.52      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_4089]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_21424,plain,
% 7.19/1.52      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 7.19/1.52      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_9966,c_45,c_47,c_3675,c_4090]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_20,plain,
% 7.19/1.52      ( v5_relat_1(X0,X1)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.19/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_30,plain,
% 7.19/1.52      ( ~ v5_relat_1(X0,X1)
% 7.19/1.52      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.19/1.52      | ~ v1_funct_1(X0)
% 7.19/1.52      | ~ v1_relat_1(X0)
% 7.19/1.52      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.19/1.52      inference(cnf_transformation,[],[f95]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_453,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.19/1.52      | ~ v1_funct_1(X0)
% 7.19/1.52      | ~ v1_relat_1(X0)
% 7.19/1.52      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.19/1.52      inference(resolution,[status(thm)],[c_20,c_30]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2973,plain,
% 7.19/1.52      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.19/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 7.19/1.52      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.19/1.52      | v1_funct_1(X1) != iProver_top
% 7.19/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3993,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.19/1.52      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.19/1.52      | v1_funct_1(sK6) != iProver_top
% 7.19/1.52      | v1_relat_1(sK6) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2979,c_2973]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_39,negated_conjecture,
% 7.19/1.52      ( v1_funct_1(sK6) ),
% 7.19/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_48,plain,
% 7.19/1.52      ( v1_funct_1(sK6) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_49,plain,
% 7.19/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3671,plain,
% 7.19/1.52      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 7.19/1.52      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
% 7.19/1.52      | v1_relat_1(sK6) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3315]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3672,plain,
% 7.19/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.19/1.52      | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
% 7.19/1.52      | v1_relat_1(sK6) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_3671]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4086,plain,
% 7.19/1.52      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_14]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4087,plain,
% 7.19/1.52      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_4086]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4256,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.19/1.52      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_3993,c_48,c_49,c_3672,c_4087]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_21439,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.19/1.52      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_21424,c_4256]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_21627,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.19/1.52      | sK4 = k1_xboole_0
% 7.19/1.52      | r2_hidden(X0,sK3) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_7033,c_21439]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22098,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 7.19/1.52      | sK4 = k1_xboole_0 ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_4346,c_21627]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_15,plain,
% 7.19/1.52      ( r2_hidden(X0,k1_relat_1(X1))
% 7.19/1.52      | ~ v1_funct_1(X1)
% 7.19/1.52      | ~ v1_relat_1(X1)
% 7.19/1.52      | k1_funct_1(X1,X0) = k1_xboole_0 ),
% 7.19/1.52      inference(cnf_transformation,[],[f111]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2996,plain,
% 7.19/1.52      ( k1_funct_1(X0,X1) = k1_xboole_0
% 7.19/1.52      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 7.19/1.52      | v1_funct_1(X0) != iProver_top
% 7.19/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5604,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.19/1.52      | k1_funct_1(sK6,X0) = k1_xboole_0
% 7.19/1.52      | v1_funct_1(sK6) != iProver_top
% 7.19/1.52      | v1_relat_1(sK6) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2996,c_4256]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7407,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.19/1.52      | k1_funct_1(sK6,X0) = k1_xboole_0 ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_5604,c_48,c_49,c_3672,c_4087]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_33,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.52      | ~ m1_subset_1(X3,X1)
% 7.19/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 7.19/1.52      | ~ v1_funct_1(X4)
% 7.19/1.52      | ~ v1_funct_1(X0)
% 7.19/1.52      | v1_xboole_0(X2)
% 7.19/1.52      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.19/1.52      | k1_xboole_0 = X1 ),
% 7.19/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2982,plain,
% 7.19/1.52      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 7.19/1.52      | k1_xboole_0 = X0
% 7.19/1.52      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.19/1.52      | m1_subset_1(X5,X0) != iProver_top
% 7.19/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.19/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.19/1.52      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.19/1.52      | v1_funct_1(X4) != iProver_top
% 7.19/1.52      | v1_funct_1(X3) != iProver_top
% 7.19/1.52      | v1_xboole_0(X1) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4464,plain,
% 7.19/1.52      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.19/1.52      | sK3 = k1_xboole_0
% 7.19/1.52      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.19/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 7.19/1.52      | m1_subset_1(X2,sK3) != iProver_top
% 7.19/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.19/1.52      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 7.19/1.52      | v1_funct_1(X1) != iProver_top
% 7.19/1.52      | v1_funct_1(sK5) != iProver_top
% 7.19/1.52      | v1_xboole_0(sK4) = iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_3840,c_2982]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_43,negated_conjecture,
% 7.19/1.52      ( ~ v1_xboole_0(sK4) ),
% 7.19/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_44,plain,
% 7.19/1.52      ( v1_xboole_0(sK4) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_9,plain,
% 7.19/1.52      ( r1_tarski(k1_xboole_0,X0) ),
% 7.19/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_121,plain,
% 7.19/1.52      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_6,plain,
% 7.19/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.19/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_126,plain,
% 7.19/1.52      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.19/1.52      | k1_xboole_0 = k1_xboole_0 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2316,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3377,plain,
% 7.19/1.52      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_2316]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3378,plain,
% 7.19/1.52      ( sK3 != k1_xboole_0
% 7.19/1.52      | k1_xboole_0 = sK3
% 7.19/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3377]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7886,plain,
% 7.19/1.52      ( m1_subset_1(X2,sK3) != iProver_top
% 7.19/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 7.19/1.52      | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.19/1.52      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 7.19/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_4464,c_44,c_45,c_46,c_47,c_35,c_121,c_126,c_3378]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7887,plain,
% 7.19/1.52      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 7.19/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 7.19/1.52      | m1_subset_1(X2,sK3) != iProver_top
% 7.19/1.52      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 7.19/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.19/1.52      inference(renaming,[status(thm)],[c_7886]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7898,plain,
% 7.19/1.52      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.19/1.52      | m1_subset_1(X0,sK3) != iProver_top
% 7.19/1.52      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.19/1.52      | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
% 7.19/1.52      | v1_funct_1(sK6) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_4111,c_7887]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_8091,plain,
% 7.19/1.52      ( m1_subset_1(X0,sK3) != iProver_top
% 7.19/1.52      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_7898,c_48,c_49,c_4185]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_8092,plain,
% 7.19/1.52      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 7.19/1.52      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.19/1.52      inference(renaming,[status(thm)],[c_8091]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_8100,plain,
% 7.19/1.52      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2980,c_8092]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_34,negated_conjecture,
% 7.19/1.52      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) ),
% 7.19/1.52      inference(cnf_transformation,[],[f108]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_8119,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_8100,c_34]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_8178,plain,
% 7.19/1.52      ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_xboole_0 ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_7407,c_8119]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22209,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_xboole_0
% 7.19/1.52      | sK4 = k1_xboole_0 ),
% 7.19/1.52      inference(light_normalisation,[status(thm)],[c_22098,c_8178]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_8328,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_xboole_0 ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_8178,c_8119]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22321,plain,
% 7.19/1.52      ( sK4 = k1_xboole_0 ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_22209,c_8328]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_32,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.52      | ~ m1_subset_1(X3,X1)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | ~ v1_funct_1(X0)
% 7.19/1.52      | v1_xboole_0(X1)
% 7.19/1.52      | k3_funct_2(X1,X2,X0,X3) = k1_funct_1(X0,X3) ),
% 7.19/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2983,plain,
% 7.19/1.52      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
% 7.19/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.19/1.52      | m1_subset_1(X3,X0) != iProver_top
% 7.19/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.19/1.52      | v1_funct_1(X2) != iProver_top
% 7.19/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5389,plain,
% 7.19/1.52      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 7.19/1.52      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.19/1.52      | m1_subset_1(X0,sK3) != iProver_top
% 7.19/1.52      | v1_funct_1(sK5) != iProver_top
% 7.19/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2977,c_2983]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_1184,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,X1)
% 7.19/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.19/1.52      | ~ v1_funct_1(X2)
% 7.19/1.52      | v1_xboole_0(X1)
% 7.19/1.52      | k3_funct_2(X1,X3,X2,X0) = k1_funct_1(X2,X0)
% 7.19/1.52      | sK5 != X2
% 7.19/1.52      | sK4 != X3
% 7.19/1.52      | sK3 != X1 ),
% 7.19/1.52      inference(resolution_lifted,[status(thm)],[c_32,c_41]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_1185,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,sK3)
% 7.19/1.52      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.19/1.52      | ~ v1_funct_1(sK5)
% 7.19/1.52      | v1_xboole_0(sK3)
% 7.19/1.52      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 7.19/1.52      inference(unflattening,[status(thm)],[c_1184]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_1189,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,sK3)
% 7.19/1.52      | v1_xboole_0(sK3)
% 7.19/1.52      | k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0) ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_1185,c_42,c_40]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_1191,plain,
% 7.19/1.52      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 7.19/1.52      | m1_subset_1(X0,sK3) != iProver_top
% 7.19/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_1189]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5866,plain,
% 7.19/1.52      ( k3_funct_2(sK3,sK4,sK5,X0) = k1_funct_1(sK5,X0)
% 7.19/1.52      | m1_subset_1(X0,sK3) != iProver_top ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_5389,c_35,c_1191,c_3307]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5874,plain,
% 7.19/1.52      ( k3_funct_2(sK3,sK4,sK5,sK7) = k1_funct_1(sK5,sK7) ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2980,c_5866]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_31,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.52      | ~ m1_subset_1(X3,X1)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 7.19/1.52      | ~ v1_funct_1(X0)
% 7.19/1.52      | v1_xboole_0(X1) ),
% 7.19/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2984,plain,
% 7.19/1.52      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.19/1.52      | m1_subset_1(X3,X1) != iProver_top
% 7.19/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.19/1.52      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 7.19/1.52      | v1_funct_1(X0) != iProver_top
% 7.19/1.52      | v1_xboole_0(X1) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_6471,plain,
% 7.19/1.52      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.19/1.52      | m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top
% 7.19/1.52      | m1_subset_1(sK7,sK3) != iProver_top
% 7.19/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.19/1.52      | v1_funct_1(sK5) != iProver_top
% 7.19/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_5874,c_2984]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7814,plain,
% 7.19/1.52      ( m1_subset_1(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_6471,c_45,c_46,c_47,c_50,c_35,c_3307]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7819,plain,
% 7.19/1.52      ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top
% 7.19/1.52      | v1_xboole_0(sK4) = iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_7814,c_2999]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_9541,plain,
% 7.19/1.52      ( r2_hidden(k1_funct_1(sK5,sK7),sK4) = iProver_top ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_7819,c_44]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22385,plain,
% 7.19/1.52      ( r2_hidden(k1_funct_1(sK5,sK7),k1_xboole_0) = iProver_top ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_22321,c_9541]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22415,plain,
% 7.19/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_22321,c_2977]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_25,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.19/1.52      | k1_xboole_0 = X1
% 7.19/1.52      | k1_xboole_0 = X0 ),
% 7.19/1.52      inference(cnf_transformation,[],[f116]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2989,plain,
% 7.19/1.52      ( k1_xboole_0 = X0
% 7.19/1.52      | k1_xboole_0 = X1
% 7.19/1.52      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 7.19/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22946,plain,
% 7.19/1.52      ( sK5 = k1_xboole_0
% 7.19/1.52      | sK3 = k1_xboole_0
% 7.19/1.52      | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_22415,c_2989]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3363,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,sK3,k1_xboole_0)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 7.19/1.52      | k1_xboole_0 = X0
% 7.19/1.52      | k1_xboole_0 = sK3 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_25]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3727,plain,
% 7.19/1.52      ( ~ v1_funct_2(sK5,sK3,k1_xboole_0)
% 7.19/1.52      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
% 7.19/1.52      | k1_xboole_0 = sK5
% 7.19/1.52      | k1_xboole_0 = sK3 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3363]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3732,plain,
% 7.19/1.52      ( k1_xboole_0 = sK5
% 7.19/1.52      | k1_xboole_0 = sK3
% 7.19/1.52      | v1_funct_2(sK5,sK3,k1_xboole_0) != iProver_top
% 7.19/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_3727]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2315,plain,( X0 = X0 ),theory(equality) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3739,plain,
% 7.19/1.52      ( sK5 = sK5 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_2315]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3971,plain,
% 7.19/1.52      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_2316]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3972,plain,
% 7.19/1.52      ( sK4 != k1_xboole_0
% 7.19/1.52      | k1_xboole_0 = sK4
% 7.19/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3971]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3627,plain,
% 7.19/1.52      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5065,plain,
% 7.19/1.52      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3627]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7,plain,
% 7.19/1.52      ( r1_tarski(X0,X0) ),
% 7.19/1.52      inference(cnf_transformation,[],[f109]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5066,plain,
% 7.19/1.52      ( r1_tarski(sK3,sK3) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2329,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.52      | v1_funct_2(X3,X4,X5)
% 7.19/1.52      | X3 != X0
% 7.19/1.52      | X4 != X1
% 7.19/1.52      | X5 != X2 ),
% 7.19/1.52      theory(equality) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3466,plain,
% 7.19/1.52      ( v1_funct_2(X0,X1,X2)
% 7.19/1.52      | ~ v1_funct_2(sK5,sK3,sK4)
% 7.19/1.52      | X0 != sK5
% 7.19/1.52      | X2 != sK4
% 7.19/1.52      | X1 != sK3 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_2329]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4301,plain,
% 7.19/1.52      ( v1_funct_2(sK5,X0,X1)
% 7.19/1.52      | ~ v1_funct_2(sK5,sK3,sK4)
% 7.19/1.52      | X1 != sK4
% 7.19/1.52      | X0 != sK3
% 7.19/1.52      | sK5 != sK5 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_3466]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7593,plain,
% 7.19/1.52      ( v1_funct_2(sK5,sK3,X0)
% 7.19/1.52      | ~ v1_funct_2(sK5,sK3,sK4)
% 7.19/1.52      | X0 != sK4
% 7.19/1.52      | sK5 != sK5
% 7.19/1.52      | sK3 != sK3 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_4301]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7595,plain,
% 7.19/1.52      ( X0 != sK4
% 7.19/1.52      | sK5 != sK5
% 7.19/1.52      | sK3 != sK3
% 7.19/1.52      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 7.19/1.52      | v1_funct_2(sK5,sK3,sK4) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_7593]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_7597,plain,
% 7.19/1.52      ( sK5 != sK5
% 7.19/1.52      | sK3 != sK3
% 7.19/1.52      | k1_xboole_0 != sK4
% 7.19/1.52      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 7.19/1.52      | v1_funct_2(sK5,sK3,k1_xboole_0) = iProver_top ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_7595]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5196,plain,
% 7.19/1.52      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_2316]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_9625,plain,
% 7.19/1.52      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_5196]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_9626,plain,
% 7.19/1.52      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_9625]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_23285,plain,
% 7.19/1.52      ( sK5 = k1_xboole_0 ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_22946,c_46,c_35,c_121,c_126,c_3732,c_3739,c_3972,
% 7.19/1.52                 c_5065,c_5066,c_7597,c_8328,c_9626,c_22209,c_22415]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_25693,plain,
% 7.19/1.52      ( r2_hidden(k1_funct_1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
% 7.19/1.52      inference(light_normalisation,[status(thm)],[c_22385,c_23285]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22414,plain,
% 7.19/1.52      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) = iProver_top ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_22321,c_2979]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_28,plain,
% 7.19/1.52      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.19/1.52      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.19/1.52      inference(cnf_transformation,[],[f118]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2986,plain,
% 7.19/1.52      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.19/1.52      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.19/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22934,plain,
% 7.19/1.52      ( k1_relset_1(k1_xboole_0,sK2,sK6) = k1_xboole_0
% 7.19/1.52      | v1_funct_2(sK6,k1_xboole_0,sK2) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_22414,c_2986]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_12674,plain,
% 7.19/1.52      ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) ),
% 7.19/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_12677,plain,
% 7.19/1.52      ( r1_tarski(k1_xboole_0,k1_relat_1(sK6)) = iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_12674]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_21,plain,
% 7.19/1.52      ( v4_relat_1(X0,X1)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.19/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_13,plain,
% 7.19/1.52      ( ~ v4_relat_1(X0,X1)
% 7.19/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.19/1.52      | ~ v1_relat_1(X0) ),
% 7.19/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_479,plain,
% 7.19/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.19/1.52      | ~ v1_relat_1(X0) ),
% 7.19/1.52      inference(resolution,[status(thm)],[c_21,c_13]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2972,plain,
% 7.19/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.19/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.19/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3611,plain,
% 7.19/1.52      ( r1_tarski(k1_relat_1(sK6),sK4) = iProver_top
% 7.19/1.52      | v1_relat_1(sK6) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_2979,c_2972]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_3002,plain,
% 7.19/1.52      ( X0 = X1
% 7.19/1.52      | r1_tarski(X1,X0) != iProver_top
% 7.19/1.52      | r1_tarski(X0,X1) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_4563,plain,
% 7.19/1.52      ( k1_relat_1(sK6) = sK4
% 7.19/1.52      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
% 7.19/1.52      | v1_relat_1(sK6) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_3611,c_3002]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5375,plain,
% 7.19/1.52      ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
% 7.19/1.52      | k1_relat_1(sK6) = sK4 ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_4563,c_49,c_3672,c_4087]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_5376,plain,
% 7.19/1.52      ( k1_relat_1(sK6) = sK4
% 7.19/1.52      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 7.19/1.52      inference(renaming,[status(thm)],[c_5375]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22406,plain,
% 7.19/1.52      ( k1_relat_1(sK6) = k1_xboole_0
% 7.19/1.52      | r1_tarski(k1_xboole_0,k1_relat_1(sK6)) != iProver_top ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_22321,c_5376]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_22411,plain,
% 7.19/1.52      ( k1_relset_1(k1_xboole_0,sK2,sK6) = k1_relat_1(sK6) ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_22321,c_4111]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_26,plain,
% 7.19/1.52      ( v1_funct_2(X0,k1_xboole_0,X1)
% 7.19/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.19/1.52      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 7.19/1.52      inference(cnf_transformation,[],[f117]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_2988,plain,
% 7.19/1.52      ( k1_relset_1(k1_xboole_0,X0,X1) != k1_xboole_0
% 7.19/1.52      | v1_funct_2(X1,k1_xboole_0,X0) = iProver_top
% 7.19/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.19/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_23026,plain,
% 7.19/1.52      ( k1_relat_1(sK6) != k1_xboole_0
% 7.19/1.52      | v1_funct_2(sK6,k1_xboole_0,sK2) = iProver_top
% 7.19/1.52      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_22411,c_2988]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_23230,plain,
% 7.19/1.52      ( k1_relset_1(k1_xboole_0,sK2,sK6) = k1_xboole_0 ),
% 7.19/1.52      inference(global_propositional_subsumption,
% 7.19/1.52                [status(thm)],
% 7.19/1.52                [c_22934,c_12677,c_22406,c_22414,c_23026]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_23233,plain,
% 7.19/1.52      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_23230,c_22411]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_24791,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 7.19/1.52      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_23233,c_4256]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_25697,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) ),
% 7.19/1.52      inference(superposition,[status(thm)],[c_25693,c_24791]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_23333,plain,
% 7.19/1.52      ( k1_funct_1(sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_xboole_0 ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_23285,c_8178]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_25718,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) = k1_xboole_0 ),
% 7.19/1.52      inference(light_normalisation,[status(thm)],[c_25697,c_23333]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(c_23332,plain,
% 7.19/1.52      ( k7_partfun1(sK2,sK6,k1_funct_1(k1_xboole_0,sK7)) != k1_xboole_0 ),
% 7.19/1.52      inference(demodulation,[status(thm)],[c_23285,c_8328]) ).
% 7.19/1.52  
% 7.19/1.52  cnf(contradiction,plain,
% 7.19/1.52      ( $false ),
% 7.19/1.52      inference(minisat,[status(thm)],[c_25718,c_23332]) ).
% 7.19/1.52  
% 7.19/1.52  
% 7.19/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.19/1.52  
% 7.19/1.52  ------                               Statistics
% 7.19/1.52  
% 7.19/1.52  ------ General
% 7.19/1.52  
% 7.19/1.52  abstr_ref_over_cycles:                  0
% 7.19/1.52  abstr_ref_under_cycles:                 0
% 7.19/1.52  gc_basic_clause_elim:                   0
% 7.19/1.52  forced_gc_time:                         0
% 7.19/1.52  parsing_time:                           0.007
% 7.19/1.52  unif_index_cands_time:                  0.
% 7.19/1.52  unif_index_add_time:                    0.
% 7.19/1.52  orderings_time:                         0.
% 7.19/1.52  out_proof_time:                         0.016
% 7.19/1.52  total_time:                             0.675
% 7.19/1.52  num_of_symbols:                         60
% 7.19/1.52  num_of_terms:                           29244
% 7.19/1.52  
% 7.19/1.52  ------ Preprocessing
% 7.19/1.52  
% 7.19/1.52  num_of_splits:                          0
% 7.19/1.52  num_of_split_atoms:                     0
% 7.19/1.52  num_of_reused_defs:                     0
% 7.19/1.52  num_eq_ax_congr_red:                    34
% 7.19/1.52  num_of_sem_filtered_clauses:            1
% 7.19/1.52  num_of_subtypes:                        0
% 7.19/1.52  monotx_restored_types:                  0
% 7.19/1.52  sat_num_of_epr_types:                   0
% 7.19/1.52  sat_num_of_non_cyclic_types:            0
% 7.19/1.52  sat_guarded_non_collapsed_types:        0
% 7.19/1.52  num_pure_diseq_elim:                    0
% 7.19/1.52  simp_replaced_by:                       0
% 7.19/1.52  res_preprocessed:                       194
% 7.19/1.52  prep_upred:                             0
% 7.19/1.52  prep_unflattend:                        130
% 7.19/1.52  smt_new_axioms:                         0
% 7.19/1.52  pred_elim_cands:                        7
% 7.19/1.52  pred_elim:                              2
% 7.19/1.52  pred_elim_cl:                           3
% 7.19/1.52  pred_elim_cycles:                       6
% 7.19/1.52  merged_defs:                            0
% 7.19/1.52  merged_defs_ncl:                        0
% 7.19/1.52  bin_hyper_res:                          0
% 7.19/1.52  prep_cycles:                            4
% 7.19/1.52  pred_elim_time:                         0.021
% 7.19/1.52  splitting_time:                         0.
% 7.19/1.52  sem_filter_time:                        0.
% 7.19/1.52  monotx_time:                            0.
% 7.19/1.52  subtype_inf_time:                       0.
% 7.19/1.52  
% 7.19/1.52  ------ Problem properties
% 7.19/1.52  
% 7.19/1.52  clauses:                                39
% 7.19/1.52  conjectures:                            10
% 7.19/1.52  epr:                                    13
% 7.19/1.52  horn:                                   28
% 7.19/1.52  ground:                                 10
% 7.19/1.52  unary:                                  13
% 7.19/1.52  binary:                                 7
% 7.19/1.52  lits:                                   107
% 7.19/1.52  lits_eq:                                21
% 7.19/1.52  fd_pure:                                0
% 7.19/1.52  fd_pseudo:                              0
% 7.19/1.52  fd_cond:                                5
% 7.19/1.52  fd_pseudo_cond:                         2
% 7.19/1.52  ac_symbols:                             0
% 7.19/1.52  
% 7.19/1.52  ------ Propositional Solver
% 7.19/1.52  
% 7.19/1.52  prop_solver_calls:                      30
% 7.19/1.52  prop_fast_solver_calls:                 2456
% 7.19/1.52  smt_solver_calls:                       0
% 7.19/1.52  smt_fast_solver_calls:                  0
% 7.19/1.52  prop_num_of_clauses:                    8186
% 7.19/1.52  prop_preprocess_simplified:             15907
% 7.19/1.52  prop_fo_subsumed:                       122
% 7.19/1.52  prop_solver_time:                       0.
% 7.19/1.52  smt_solver_time:                        0.
% 7.19/1.52  smt_fast_solver_time:                   0.
% 7.19/1.52  prop_fast_solver_time:                  0.
% 7.19/1.52  prop_unsat_core_time:                   0.001
% 7.19/1.52  
% 7.19/1.52  ------ QBF
% 7.19/1.52  
% 7.19/1.52  qbf_q_res:                              0
% 7.19/1.52  qbf_num_tautologies:                    0
% 7.19/1.52  qbf_prep_cycles:                        0
% 7.19/1.52  
% 7.19/1.52  ------ BMC1
% 7.19/1.52  
% 7.19/1.52  bmc1_current_bound:                     -1
% 7.19/1.52  bmc1_last_solved_bound:                 -1
% 7.19/1.52  bmc1_unsat_core_size:                   -1
% 7.19/1.52  bmc1_unsat_core_parents_size:           -1
% 7.19/1.52  bmc1_merge_next_fun:                    0
% 7.19/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.19/1.52  
% 7.19/1.52  ------ Instantiation
% 7.19/1.52  
% 7.19/1.52  inst_num_of_clauses:                    2108
% 7.19/1.52  inst_num_in_passive:                    899
% 7.19/1.52  inst_num_in_active:                     1012
% 7.19/1.52  inst_num_in_unprocessed:                197
% 7.19/1.52  inst_num_of_loops:                      1380
% 7.19/1.52  inst_num_of_learning_restarts:          0
% 7.19/1.52  inst_num_moves_active_passive:          365
% 7.19/1.52  inst_lit_activity:                      0
% 7.19/1.52  inst_lit_activity_moves:                0
% 7.19/1.52  inst_num_tautologies:                   0
% 7.19/1.52  inst_num_prop_implied:                  0
% 7.19/1.52  inst_num_existing_simplified:           0
% 7.19/1.52  inst_num_eq_res_simplified:             0
% 7.19/1.52  inst_num_child_elim:                    0
% 7.19/1.52  inst_num_of_dismatching_blockings:      576
% 7.19/1.52  inst_num_of_non_proper_insts:           2162
% 7.19/1.52  inst_num_of_duplicates:                 0
% 7.19/1.52  inst_inst_num_from_inst_to_res:         0
% 7.19/1.52  inst_dismatching_checking_time:         0.
% 7.19/1.52  
% 7.19/1.52  ------ Resolution
% 7.19/1.52  
% 7.19/1.52  res_num_of_clauses:                     0
% 7.19/1.52  res_num_in_passive:                     0
% 7.19/1.52  res_num_in_active:                      0
% 7.19/1.52  res_num_of_loops:                       198
% 7.19/1.52  res_forward_subset_subsumed:            205
% 7.19/1.52  res_backward_subset_subsumed:           8
% 7.19/1.52  res_forward_subsumed:                   0
% 7.19/1.52  res_backward_subsumed:                  0
% 7.19/1.52  res_forward_subsumption_resolution:     1
% 7.19/1.52  res_backward_subsumption_resolution:    0
% 7.19/1.52  res_clause_to_clause_subsumption:       2103
% 7.19/1.52  res_orphan_elimination:                 0
% 7.19/1.52  res_tautology_del:                      134
% 7.19/1.52  res_num_eq_res_simplified:              0
% 7.19/1.52  res_num_sel_changes:                    0
% 7.19/1.52  res_moves_from_active_to_pass:          0
% 7.19/1.52  
% 7.19/1.52  ------ Superposition
% 7.19/1.52  
% 7.19/1.52  sup_time_total:                         0.
% 7.19/1.52  sup_time_generating:                    0.
% 7.19/1.52  sup_time_sim_full:                      0.
% 7.19/1.52  sup_time_sim_immed:                     0.
% 7.19/1.52  
% 7.19/1.52  sup_num_of_clauses:                     473
% 7.19/1.52  sup_num_in_active:                      92
% 7.19/1.52  sup_num_in_passive:                     381
% 7.19/1.52  sup_num_of_loops:                       275
% 7.19/1.52  sup_fw_superposition:                   426
% 7.19/1.52  sup_bw_superposition:                   417
% 7.19/1.52  sup_immediate_simplified:               225
% 7.19/1.52  sup_given_eliminated:                   5
% 7.19/1.52  comparisons_done:                       0
% 7.19/1.52  comparisons_avoided:                    148
% 7.19/1.52  
% 7.19/1.52  ------ Simplifications
% 7.19/1.52  
% 7.19/1.52  
% 7.19/1.52  sim_fw_subset_subsumed:                 150
% 7.19/1.52  sim_bw_subset_subsumed:                 44
% 7.19/1.52  sim_fw_subsumed:                        60
% 7.19/1.52  sim_bw_subsumed:                        14
% 7.19/1.52  sim_fw_subsumption_res:                 5
% 7.19/1.52  sim_bw_subsumption_res:                 1
% 7.19/1.52  sim_tautology_del:                      8
% 7.19/1.52  sim_eq_tautology_del:                   55
% 7.19/1.52  sim_eq_res_simp:                        0
% 7.19/1.52  sim_fw_demodulated:                     2
% 7.19/1.52  sim_bw_demodulated:                     163
% 7.19/1.52  sim_light_normalised:                   18
% 7.19/1.52  sim_joinable_taut:                      0
% 7.19/1.52  sim_joinable_simp:                      0
% 7.19/1.52  sim_ac_normalised:                      0
% 7.19/1.52  sim_smt_subsumption:                    0
% 7.19/1.52  
%------------------------------------------------------------------------------
