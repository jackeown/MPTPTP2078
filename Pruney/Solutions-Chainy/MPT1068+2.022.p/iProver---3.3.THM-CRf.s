%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:39 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 480 expanded)
%              Number of clauses        :   80 ( 134 expanded)
%              Number of leaves         :   14 ( 166 expanded)
%              Depth                    :   20
%              Number of atoms          :  476 (3827 expanded)
%              Number of equality atoms :  177 ( 989 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
                     => ( k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f20])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                ( k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5)
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

fof(f28,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f27,f26,f25,f24])).

fof(f40,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK0) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f22])).

fof(f30,plain,(
    v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_802,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1119,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_804,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1117,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_328,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,X1),X0)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_332,plain,
    ( ~ v1_funct_1(X1)
    | ~ r2_hidden(X0,sK2)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,X1),X0)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_15,c_13])).

cnf(c_333,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,X1),X0)
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | X3 != X0
    | k1_funct_1(k5_relat_1(sK4,X2),X3) = k1_funct_1(X2,k1_funct_1(sK4,X3))
    | sK3 = k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_333])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(sK2)
    | k1_funct_1(k5_relat_1(sK4,X1),X0) = k1_funct_1(X1,k1_funct_1(sK4,X0))
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0_51,sK2)
    | ~ v1_funct_1(X1_51)
    | ~ v1_relat_1(X1_51)
    | v1_xboole_0(sK2)
    | sK3 = k1_xboole_0
    | k1_funct_1(k5_relat_1(sK4,X1_51),X0_51) = k1_funct_1(X1_51,k1_funct_1(sK4,X0_51)) ),
    inference(subtyping,[status(esa)],[c_449])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0_51,sK2)
    | ~ v1_funct_1(X1_51)
    | ~ v1_relat_1(X1_51)
    | k1_funct_1(k5_relat_1(sK4,X1_51),X0_51) = k1_funct_1(X1_51,k1_funct_1(sK4,X0_51))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_797])).

cnf(c_1125,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51))
    | m1_subset_1(X1_51,sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_16,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_806,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_813,plain,
    ( v1_xboole_0(sK2)
    | sP0_iProver_split
    | sK3 = k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_797])).

cnf(c_870,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_813])).

cnf(c_871,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51))
    | m1_subset_1(X1_51,sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_811,plain,
    ( ~ v1_xboole_0(X0_52)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1227,plain,
    ( ~ v1_xboole_0(sK0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_1230,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_1231,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_822,plain,
    ( ~ v1_xboole_0(X0_52)
    | v1_xboole_0(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1243,plain,
    ( v1_xboole_0(X0_52)
    | ~ v1_xboole_0(sK0)
    | X0_52 != sK0 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1384,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_1551,plain,
    ( v1_xboole_0(X0_52)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_52 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_822])).

cnf(c_1556,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1846,plain,
    ( v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X1_51,sK2) != iProver_top
    | k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1125,c_16,c_1,c_806,c_870,c_871,c_1227,c_1231,c_1384,c_1556])).

cnf(c_1847,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51))
    | m1_subset_1(X1_51,sK2) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_1846])).

cnf(c_1856,plain,
    ( k1_funct_1(X0_51,k1_funct_1(sK4,sK6)) = k1_funct_1(k5_relat_1(sK4,X0_51),sK6)
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_1847])).

cnf(c_1864,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1856])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_805,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1116,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_354,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | k1_partfun1(X0,X1,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,X4)
    | sK3 != X1
    | sK2 != X0
    | sK4 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_355,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_359,plain,
    ( ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_15,c_13])).

cnf(c_360,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
    | ~ v1_funct_1(X1)
    | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_359])).

cnf(c_798,plain,
    ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0_52,X0_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X0_52)))
    | ~ v1_funct_1(X0_51)
    | k1_xboole_0 = sK3
    | k1_partfun1(sK2,sK3,sK3,X0_52,sK4,X0_51) = k8_funct_2(sK2,sK3,X0_52,sK4,X0_51) ),
    inference(subtyping,[status(esa)],[c_360])).

cnf(c_1123,plain,
    ( k1_xboole_0 = sK3
    | k1_partfun1(sK2,sK3,sK3,X0_52,sK4,X0_51) = k8_funct_2(sK2,sK3,X0_52,sK4,X0_51)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0_52,X0_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X0_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_1712,plain,
    ( sK3 = k1_xboole_0
    | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1123])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_803,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1118,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_801,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1120,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_808,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
    | ~ v1_funct_1(X1_51)
    | ~ v1_funct_1(X0_51)
    | k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51) = k5_relat_1(X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1115,plain,
    ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X0_51,X1_51) = k5_relat_1(X0_51,X1_51)
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_1489,plain,
    ( k1_partfun1(sK2,sK3,X0_52,X1_52,sK4,X0_51) = k5_relat_1(sK4,X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_1115])).

cnf(c_18,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1629,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | k1_partfun1(sK2,sK3,X0_52,X1_52,sK4,X0_51) = k5_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1489,c_18])).

cnf(c_1630,plain,
    ( k1_partfun1(sK2,sK3,X0_52,X1_52,sK4,X0_51) = k5_relat_1(sK4,X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_1629])).

cnf(c_1636,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_1630])).

cnf(c_1282,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0_52,X1_52,sK3,sK1,X0_51,sK5) = k5_relat_1(X0_51,sK5) ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1649,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1636,c_15,c_13,c_12,c_11,c_1358])).

cnf(c_1713,plain,
    ( sK3 = k1_xboole_0
    | k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1712,c_1649])).

cnf(c_21,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1803,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1713,c_16,c_21,c_22,c_1,c_1227,c_1384,c_1556])).

cnf(c_7,negated_conjecture,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_807,negated_conjecture,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1806,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(demodulation,[status(thm)],[c_1803,c_807])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_809,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1233,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1234,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1864,c_1806,c_1234,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:14:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.74/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.01  
% 1.74/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.74/1.01  
% 1.74/1.01  ------  iProver source info
% 1.74/1.01  
% 1.74/1.01  git: date: 2020-06-30 10:37:57 +0100
% 1.74/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.74/1.01  git: non_committed_changes: false
% 1.74/1.01  git: last_make_outside_of_git: false
% 1.74/1.01  
% 1.74/1.01  ------ 
% 1.74/1.01  
% 1.74/1.01  ------ Input Options
% 1.74/1.01  
% 1.74/1.01  --out_options                           all
% 1.74/1.01  --tptp_safe_out                         true
% 1.74/1.01  --problem_path                          ""
% 1.74/1.01  --include_path                          ""
% 1.74/1.01  --clausifier                            res/vclausify_rel
% 1.74/1.01  --clausifier_options                    --mode clausify
% 1.74/1.01  --stdin                                 false
% 1.74/1.01  --stats_out                             all
% 1.74/1.01  
% 1.74/1.01  ------ General Options
% 1.74/1.01  
% 1.74/1.01  --fof                                   false
% 1.74/1.01  --time_out_real                         305.
% 1.74/1.01  --time_out_virtual                      -1.
% 1.74/1.01  --symbol_type_check                     false
% 1.74/1.01  --clausify_out                          false
% 1.74/1.01  --sig_cnt_out                           false
% 1.74/1.01  --trig_cnt_out                          false
% 1.74/1.01  --trig_cnt_out_tolerance                1.
% 1.74/1.01  --trig_cnt_out_sk_spl                   false
% 1.74/1.01  --abstr_cl_out                          false
% 1.74/1.01  
% 1.74/1.01  ------ Global Options
% 1.74/1.01  
% 1.74/1.01  --schedule                              default
% 1.74/1.01  --add_important_lit                     false
% 1.74/1.01  --prop_solver_per_cl                    1000
% 1.74/1.01  --min_unsat_core                        false
% 1.74/1.01  --soft_assumptions                      false
% 1.74/1.01  --soft_lemma_size                       3
% 1.74/1.01  --prop_impl_unit_size                   0
% 1.74/1.01  --prop_impl_unit                        []
% 1.74/1.01  --share_sel_clauses                     true
% 1.74/1.01  --reset_solvers                         false
% 1.74/1.01  --bc_imp_inh                            [conj_cone]
% 1.74/1.01  --conj_cone_tolerance                   3.
% 1.74/1.01  --extra_neg_conj                        none
% 1.74/1.01  --large_theory_mode                     true
% 1.74/1.01  --prolific_symb_bound                   200
% 1.74/1.01  --lt_threshold                          2000
% 1.74/1.01  --clause_weak_htbl                      true
% 1.74/1.01  --gc_record_bc_elim                     false
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing Options
% 1.74/1.01  
% 1.74/1.01  --preprocessing_flag                    true
% 1.74/1.01  --time_out_prep_mult                    0.1
% 1.74/1.01  --splitting_mode                        input
% 1.74/1.01  --splitting_grd                         true
% 1.74/1.01  --splitting_cvd                         false
% 1.74/1.01  --splitting_cvd_svl                     false
% 1.74/1.01  --splitting_nvd                         32
% 1.74/1.01  --sub_typing                            true
% 1.74/1.01  --prep_gs_sim                           true
% 1.74/1.01  --prep_unflatten                        true
% 1.74/1.01  --prep_res_sim                          true
% 1.74/1.01  --prep_upred                            true
% 1.74/1.01  --prep_sem_filter                       exhaustive
% 1.74/1.01  --prep_sem_filter_out                   false
% 1.74/1.01  --pred_elim                             true
% 1.74/1.01  --res_sim_input                         true
% 1.74/1.01  --eq_ax_congr_red                       true
% 1.74/1.01  --pure_diseq_elim                       true
% 1.74/1.01  --brand_transform                       false
% 1.74/1.01  --non_eq_to_eq                          false
% 1.74/1.01  --prep_def_merge                        true
% 1.74/1.01  --prep_def_merge_prop_impl              false
% 1.74/1.01  --prep_def_merge_mbd                    true
% 1.74/1.01  --prep_def_merge_tr_red                 false
% 1.74/1.01  --prep_def_merge_tr_cl                  false
% 1.74/1.01  --smt_preprocessing                     true
% 1.74/1.01  --smt_ac_axioms                         fast
% 1.74/1.01  --preprocessed_out                      false
% 1.74/1.01  --preprocessed_stats                    false
% 1.74/1.01  
% 1.74/1.01  ------ Abstraction refinement Options
% 1.74/1.01  
% 1.74/1.01  --abstr_ref                             []
% 1.74/1.01  --abstr_ref_prep                        false
% 1.74/1.01  --abstr_ref_until_sat                   false
% 1.74/1.01  --abstr_ref_sig_restrict                funpre
% 1.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.74/1.01  --abstr_ref_under                       []
% 1.74/1.01  
% 1.74/1.01  ------ SAT Options
% 1.74/1.01  
% 1.74/1.01  --sat_mode                              false
% 1.74/1.01  --sat_fm_restart_options                ""
% 1.74/1.01  --sat_gr_def                            false
% 1.74/1.01  --sat_epr_types                         true
% 1.74/1.01  --sat_non_cyclic_types                  false
% 1.74/1.01  --sat_finite_models                     false
% 1.74/1.01  --sat_fm_lemmas                         false
% 1.74/1.01  --sat_fm_prep                           false
% 1.74/1.01  --sat_fm_uc_incr                        true
% 1.74/1.01  --sat_out_model                         small
% 1.74/1.01  --sat_out_clauses                       false
% 1.74/1.01  
% 1.74/1.01  ------ QBF Options
% 1.74/1.01  
% 1.74/1.01  --qbf_mode                              false
% 1.74/1.01  --qbf_elim_univ                         false
% 1.74/1.01  --qbf_dom_inst                          none
% 1.74/1.01  --qbf_dom_pre_inst                      false
% 1.74/1.01  --qbf_sk_in                             false
% 1.74/1.01  --qbf_pred_elim                         true
% 1.74/1.01  --qbf_split                             512
% 1.74/1.01  
% 1.74/1.01  ------ BMC1 Options
% 1.74/1.01  
% 1.74/1.01  --bmc1_incremental                      false
% 1.74/1.01  --bmc1_axioms                           reachable_all
% 1.74/1.01  --bmc1_min_bound                        0
% 1.74/1.01  --bmc1_max_bound                        -1
% 1.74/1.01  --bmc1_max_bound_default                -1
% 1.74/1.01  --bmc1_symbol_reachability              true
% 1.74/1.01  --bmc1_property_lemmas                  false
% 1.74/1.01  --bmc1_k_induction                      false
% 1.74/1.01  --bmc1_non_equiv_states                 false
% 1.74/1.01  --bmc1_deadlock                         false
% 1.74/1.01  --bmc1_ucm                              false
% 1.74/1.01  --bmc1_add_unsat_core                   none
% 1.74/1.01  --bmc1_unsat_core_children              false
% 1.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.74/1.01  --bmc1_out_stat                         full
% 1.74/1.01  --bmc1_ground_init                      false
% 1.74/1.01  --bmc1_pre_inst_next_state              false
% 1.74/1.01  --bmc1_pre_inst_state                   false
% 1.74/1.01  --bmc1_pre_inst_reach_state             false
% 1.74/1.01  --bmc1_out_unsat_core                   false
% 1.74/1.01  --bmc1_aig_witness_out                  false
% 1.74/1.01  --bmc1_verbose                          false
% 1.74/1.01  --bmc1_dump_clauses_tptp                false
% 1.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.74/1.01  --bmc1_dump_file                        -
% 1.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.74/1.01  --bmc1_ucm_extend_mode                  1
% 1.74/1.01  --bmc1_ucm_init_mode                    2
% 1.74/1.01  --bmc1_ucm_cone_mode                    none
% 1.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.74/1.01  --bmc1_ucm_relax_model                  4
% 1.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.74/1.01  --bmc1_ucm_layered_model                none
% 1.74/1.01  --bmc1_ucm_max_lemma_size               10
% 1.74/1.01  
% 1.74/1.01  ------ AIG Options
% 1.74/1.01  
% 1.74/1.01  --aig_mode                              false
% 1.74/1.01  
% 1.74/1.01  ------ Instantiation Options
% 1.74/1.01  
% 1.74/1.01  --instantiation_flag                    true
% 1.74/1.01  --inst_sos_flag                         false
% 1.74/1.01  --inst_sos_phase                        true
% 1.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel_side                     num_symb
% 1.74/1.01  --inst_solver_per_active                1400
% 1.74/1.01  --inst_solver_calls_frac                1.
% 1.74/1.01  --inst_passive_queue_type               priority_queues
% 1.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.74/1.01  --inst_passive_queues_freq              [25;2]
% 1.74/1.01  --inst_dismatching                      true
% 1.74/1.01  --inst_eager_unprocessed_to_passive     true
% 1.74/1.01  --inst_prop_sim_given                   true
% 1.74/1.01  --inst_prop_sim_new                     false
% 1.74/1.01  --inst_subs_new                         false
% 1.74/1.01  --inst_eq_res_simp                      false
% 1.74/1.01  --inst_subs_given                       false
% 1.74/1.01  --inst_orphan_elimination               true
% 1.74/1.01  --inst_learning_loop_flag               true
% 1.74/1.01  --inst_learning_start                   3000
% 1.74/1.01  --inst_learning_factor                  2
% 1.74/1.01  --inst_start_prop_sim_after_learn       3
% 1.74/1.01  --inst_sel_renew                        solver
% 1.74/1.01  --inst_lit_activity_flag                true
% 1.74/1.01  --inst_restr_to_given                   false
% 1.74/1.01  --inst_activity_threshold               500
% 1.74/1.01  --inst_out_proof                        true
% 1.74/1.01  
% 1.74/1.01  ------ Resolution Options
% 1.74/1.01  
% 1.74/1.01  --resolution_flag                       true
% 1.74/1.01  --res_lit_sel                           adaptive
% 1.74/1.01  --res_lit_sel_side                      none
% 1.74/1.01  --res_ordering                          kbo
% 1.74/1.01  --res_to_prop_solver                    active
% 1.74/1.01  --res_prop_simpl_new                    false
% 1.74/1.01  --res_prop_simpl_given                  true
% 1.74/1.01  --res_passive_queue_type                priority_queues
% 1.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.74/1.01  --res_passive_queues_freq               [15;5]
% 1.74/1.01  --res_forward_subs                      full
% 1.74/1.01  --res_backward_subs                     full
% 1.74/1.01  --res_forward_subs_resolution           true
% 1.74/1.01  --res_backward_subs_resolution          true
% 1.74/1.01  --res_orphan_elimination                true
% 1.74/1.01  --res_time_limit                        2.
% 1.74/1.01  --res_out_proof                         true
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Options
% 1.74/1.01  
% 1.74/1.01  --superposition_flag                    true
% 1.74/1.01  --sup_passive_queue_type                priority_queues
% 1.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.74/1.01  --demod_completeness_check              fast
% 1.74/1.01  --demod_use_ground                      true
% 1.74/1.01  --sup_to_prop_solver                    passive
% 1.74/1.01  --sup_prop_simpl_new                    true
% 1.74/1.01  --sup_prop_simpl_given                  true
% 1.74/1.01  --sup_fun_splitting                     false
% 1.74/1.01  --sup_smt_interval                      50000
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Simplification Setup
% 1.74/1.01  
% 1.74/1.01  --sup_indices_passive                   []
% 1.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_full_bw                           [BwDemod]
% 1.74/1.01  --sup_immed_triv                        [TrivRules]
% 1.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_immed_bw_main                     []
% 1.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  
% 1.74/1.01  ------ Combination Options
% 1.74/1.01  
% 1.74/1.01  --comb_res_mult                         3
% 1.74/1.01  --comb_sup_mult                         2
% 1.74/1.01  --comb_inst_mult                        10
% 1.74/1.01  
% 1.74/1.01  ------ Debug Options
% 1.74/1.01  
% 1.74/1.01  --dbg_backtrace                         false
% 1.74/1.01  --dbg_dump_prop_clauses                 false
% 1.74/1.01  --dbg_dump_prop_clauses_file            -
% 1.74/1.01  --dbg_out_stat                          false
% 1.74/1.01  ------ Parsing...
% 1.74/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.74/1.01  ------ Proving...
% 1.74/1.01  ------ Problem Properties 
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  clauses                                 16
% 1.74/1.01  conjectures                             9
% 1.74/1.01  EPR                                     8
% 1.74/1.01  Horn                                    14
% 1.74/1.01  unary                                   10
% 1.74/1.01  binary                                  2
% 1.74/1.01  lits                                    32
% 1.74/1.01  lits eq                                 8
% 1.74/1.01  fd_pure                                 0
% 1.74/1.01  fd_pseudo                               0
% 1.74/1.01  fd_cond                                 1
% 1.74/1.01  fd_pseudo_cond                          0
% 1.74/1.01  AC symbols                              0
% 1.74/1.01  
% 1.74/1.01  ------ Schedule dynamic 5 is on 
% 1.74/1.01  
% 1.74/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  ------ 
% 1.74/1.01  Current options:
% 1.74/1.01  ------ 
% 1.74/1.01  
% 1.74/1.01  ------ Input Options
% 1.74/1.01  
% 1.74/1.01  --out_options                           all
% 1.74/1.01  --tptp_safe_out                         true
% 1.74/1.01  --problem_path                          ""
% 1.74/1.01  --include_path                          ""
% 1.74/1.01  --clausifier                            res/vclausify_rel
% 1.74/1.01  --clausifier_options                    --mode clausify
% 1.74/1.01  --stdin                                 false
% 1.74/1.01  --stats_out                             all
% 1.74/1.01  
% 1.74/1.01  ------ General Options
% 1.74/1.01  
% 1.74/1.01  --fof                                   false
% 1.74/1.01  --time_out_real                         305.
% 1.74/1.01  --time_out_virtual                      -1.
% 1.74/1.01  --symbol_type_check                     false
% 1.74/1.01  --clausify_out                          false
% 1.74/1.01  --sig_cnt_out                           false
% 1.74/1.01  --trig_cnt_out                          false
% 1.74/1.01  --trig_cnt_out_tolerance                1.
% 1.74/1.01  --trig_cnt_out_sk_spl                   false
% 1.74/1.01  --abstr_cl_out                          false
% 1.74/1.01  
% 1.74/1.01  ------ Global Options
% 1.74/1.01  
% 1.74/1.01  --schedule                              default
% 1.74/1.01  --add_important_lit                     false
% 1.74/1.01  --prop_solver_per_cl                    1000
% 1.74/1.01  --min_unsat_core                        false
% 1.74/1.01  --soft_assumptions                      false
% 1.74/1.01  --soft_lemma_size                       3
% 1.74/1.01  --prop_impl_unit_size                   0
% 1.74/1.01  --prop_impl_unit                        []
% 1.74/1.01  --share_sel_clauses                     true
% 1.74/1.01  --reset_solvers                         false
% 1.74/1.01  --bc_imp_inh                            [conj_cone]
% 1.74/1.01  --conj_cone_tolerance                   3.
% 1.74/1.01  --extra_neg_conj                        none
% 1.74/1.01  --large_theory_mode                     true
% 1.74/1.01  --prolific_symb_bound                   200
% 1.74/1.01  --lt_threshold                          2000
% 1.74/1.01  --clause_weak_htbl                      true
% 1.74/1.01  --gc_record_bc_elim                     false
% 1.74/1.01  
% 1.74/1.01  ------ Preprocessing Options
% 1.74/1.01  
% 1.74/1.01  --preprocessing_flag                    true
% 1.74/1.01  --time_out_prep_mult                    0.1
% 1.74/1.01  --splitting_mode                        input
% 1.74/1.01  --splitting_grd                         true
% 1.74/1.01  --splitting_cvd                         false
% 1.74/1.01  --splitting_cvd_svl                     false
% 1.74/1.01  --splitting_nvd                         32
% 1.74/1.01  --sub_typing                            true
% 1.74/1.01  --prep_gs_sim                           true
% 1.74/1.01  --prep_unflatten                        true
% 1.74/1.01  --prep_res_sim                          true
% 1.74/1.01  --prep_upred                            true
% 1.74/1.01  --prep_sem_filter                       exhaustive
% 1.74/1.01  --prep_sem_filter_out                   false
% 1.74/1.01  --pred_elim                             true
% 1.74/1.01  --res_sim_input                         true
% 1.74/1.01  --eq_ax_congr_red                       true
% 1.74/1.01  --pure_diseq_elim                       true
% 1.74/1.01  --brand_transform                       false
% 1.74/1.01  --non_eq_to_eq                          false
% 1.74/1.01  --prep_def_merge                        true
% 1.74/1.01  --prep_def_merge_prop_impl              false
% 1.74/1.01  --prep_def_merge_mbd                    true
% 1.74/1.01  --prep_def_merge_tr_red                 false
% 1.74/1.01  --prep_def_merge_tr_cl                  false
% 1.74/1.01  --smt_preprocessing                     true
% 1.74/1.01  --smt_ac_axioms                         fast
% 1.74/1.01  --preprocessed_out                      false
% 1.74/1.01  --preprocessed_stats                    false
% 1.74/1.01  
% 1.74/1.01  ------ Abstraction refinement Options
% 1.74/1.01  
% 1.74/1.01  --abstr_ref                             []
% 1.74/1.01  --abstr_ref_prep                        false
% 1.74/1.01  --abstr_ref_until_sat                   false
% 1.74/1.01  --abstr_ref_sig_restrict                funpre
% 1.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.74/1.01  --abstr_ref_under                       []
% 1.74/1.01  
% 1.74/1.01  ------ SAT Options
% 1.74/1.01  
% 1.74/1.01  --sat_mode                              false
% 1.74/1.01  --sat_fm_restart_options                ""
% 1.74/1.01  --sat_gr_def                            false
% 1.74/1.01  --sat_epr_types                         true
% 1.74/1.01  --sat_non_cyclic_types                  false
% 1.74/1.01  --sat_finite_models                     false
% 1.74/1.01  --sat_fm_lemmas                         false
% 1.74/1.01  --sat_fm_prep                           false
% 1.74/1.01  --sat_fm_uc_incr                        true
% 1.74/1.01  --sat_out_model                         small
% 1.74/1.01  --sat_out_clauses                       false
% 1.74/1.01  
% 1.74/1.01  ------ QBF Options
% 1.74/1.01  
% 1.74/1.01  --qbf_mode                              false
% 1.74/1.01  --qbf_elim_univ                         false
% 1.74/1.01  --qbf_dom_inst                          none
% 1.74/1.01  --qbf_dom_pre_inst                      false
% 1.74/1.01  --qbf_sk_in                             false
% 1.74/1.01  --qbf_pred_elim                         true
% 1.74/1.01  --qbf_split                             512
% 1.74/1.01  
% 1.74/1.01  ------ BMC1 Options
% 1.74/1.01  
% 1.74/1.01  --bmc1_incremental                      false
% 1.74/1.01  --bmc1_axioms                           reachable_all
% 1.74/1.01  --bmc1_min_bound                        0
% 1.74/1.01  --bmc1_max_bound                        -1
% 1.74/1.01  --bmc1_max_bound_default                -1
% 1.74/1.01  --bmc1_symbol_reachability              true
% 1.74/1.01  --bmc1_property_lemmas                  false
% 1.74/1.01  --bmc1_k_induction                      false
% 1.74/1.01  --bmc1_non_equiv_states                 false
% 1.74/1.01  --bmc1_deadlock                         false
% 1.74/1.01  --bmc1_ucm                              false
% 1.74/1.01  --bmc1_add_unsat_core                   none
% 1.74/1.01  --bmc1_unsat_core_children              false
% 1.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.74/1.01  --bmc1_out_stat                         full
% 1.74/1.01  --bmc1_ground_init                      false
% 1.74/1.01  --bmc1_pre_inst_next_state              false
% 1.74/1.01  --bmc1_pre_inst_state                   false
% 1.74/1.01  --bmc1_pre_inst_reach_state             false
% 1.74/1.01  --bmc1_out_unsat_core                   false
% 1.74/1.01  --bmc1_aig_witness_out                  false
% 1.74/1.01  --bmc1_verbose                          false
% 1.74/1.01  --bmc1_dump_clauses_tptp                false
% 1.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.74/1.01  --bmc1_dump_file                        -
% 1.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.74/1.01  --bmc1_ucm_extend_mode                  1
% 1.74/1.01  --bmc1_ucm_init_mode                    2
% 1.74/1.01  --bmc1_ucm_cone_mode                    none
% 1.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.74/1.01  --bmc1_ucm_relax_model                  4
% 1.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.74/1.01  --bmc1_ucm_layered_model                none
% 1.74/1.01  --bmc1_ucm_max_lemma_size               10
% 1.74/1.01  
% 1.74/1.01  ------ AIG Options
% 1.74/1.01  
% 1.74/1.01  --aig_mode                              false
% 1.74/1.01  
% 1.74/1.01  ------ Instantiation Options
% 1.74/1.01  
% 1.74/1.01  --instantiation_flag                    true
% 1.74/1.01  --inst_sos_flag                         false
% 1.74/1.01  --inst_sos_phase                        true
% 1.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.74/1.01  --inst_lit_sel_side                     none
% 1.74/1.01  --inst_solver_per_active                1400
% 1.74/1.01  --inst_solver_calls_frac                1.
% 1.74/1.01  --inst_passive_queue_type               priority_queues
% 1.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.74/1.01  --inst_passive_queues_freq              [25;2]
% 1.74/1.01  --inst_dismatching                      true
% 1.74/1.01  --inst_eager_unprocessed_to_passive     true
% 1.74/1.01  --inst_prop_sim_given                   true
% 1.74/1.01  --inst_prop_sim_new                     false
% 1.74/1.01  --inst_subs_new                         false
% 1.74/1.01  --inst_eq_res_simp                      false
% 1.74/1.01  --inst_subs_given                       false
% 1.74/1.01  --inst_orphan_elimination               true
% 1.74/1.01  --inst_learning_loop_flag               true
% 1.74/1.01  --inst_learning_start                   3000
% 1.74/1.01  --inst_learning_factor                  2
% 1.74/1.01  --inst_start_prop_sim_after_learn       3
% 1.74/1.01  --inst_sel_renew                        solver
% 1.74/1.01  --inst_lit_activity_flag                true
% 1.74/1.01  --inst_restr_to_given                   false
% 1.74/1.01  --inst_activity_threshold               500
% 1.74/1.01  --inst_out_proof                        true
% 1.74/1.01  
% 1.74/1.01  ------ Resolution Options
% 1.74/1.01  
% 1.74/1.01  --resolution_flag                       false
% 1.74/1.01  --res_lit_sel                           adaptive
% 1.74/1.01  --res_lit_sel_side                      none
% 1.74/1.01  --res_ordering                          kbo
% 1.74/1.01  --res_to_prop_solver                    active
% 1.74/1.01  --res_prop_simpl_new                    false
% 1.74/1.01  --res_prop_simpl_given                  true
% 1.74/1.01  --res_passive_queue_type                priority_queues
% 1.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.74/1.01  --res_passive_queues_freq               [15;5]
% 1.74/1.01  --res_forward_subs                      full
% 1.74/1.01  --res_backward_subs                     full
% 1.74/1.01  --res_forward_subs_resolution           true
% 1.74/1.01  --res_backward_subs_resolution          true
% 1.74/1.01  --res_orphan_elimination                true
% 1.74/1.01  --res_time_limit                        2.
% 1.74/1.01  --res_out_proof                         true
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Options
% 1.74/1.01  
% 1.74/1.01  --superposition_flag                    true
% 1.74/1.01  --sup_passive_queue_type                priority_queues
% 1.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.74/1.01  --demod_completeness_check              fast
% 1.74/1.01  --demod_use_ground                      true
% 1.74/1.01  --sup_to_prop_solver                    passive
% 1.74/1.01  --sup_prop_simpl_new                    true
% 1.74/1.01  --sup_prop_simpl_given                  true
% 1.74/1.01  --sup_fun_splitting                     false
% 1.74/1.01  --sup_smt_interval                      50000
% 1.74/1.01  
% 1.74/1.01  ------ Superposition Simplification Setup
% 1.74/1.01  
% 1.74/1.01  --sup_indices_passive                   []
% 1.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_full_bw                           [BwDemod]
% 1.74/1.01  --sup_immed_triv                        [TrivRules]
% 1.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_immed_bw_main                     []
% 1.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.01  
% 1.74/1.01  ------ Combination Options
% 1.74/1.01  
% 1.74/1.01  --comb_res_mult                         3
% 1.74/1.01  --comb_sup_mult                         2
% 1.74/1.01  --comb_inst_mult                        10
% 1.74/1.01  
% 1.74/1.01  ------ Debug Options
% 1.74/1.01  
% 1.74/1.01  --dbg_backtrace                         false
% 1.74/1.01  --dbg_dump_prop_clauses                 false
% 1.74/1.01  --dbg_dump_prop_clauses_file            -
% 1.74/1.01  --dbg_out_stat                          false
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  ------ Proving...
% 1.74/1.01  
% 1.74/1.01  
% 1.74/1.01  % SZS status Theorem for theBenchmark.p
% 1.74/1.01  
% 1.74/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.74/1.01  
% 1.74/1.01  fof(f8,conjecture,(
% 1.74/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.74/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.01  
% 1.74/1.01  fof(f9,negated_conjecture,(
% 1.74/1.01    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.74/1.01    inference(negated_conjecture,[],[f8])).
% 1.74/1.01  
% 1.74/1.01  fof(f20,plain,(
% 1.74/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.74/1.01    inference(ennf_transformation,[],[f9])).
% 1.74/1.01  
% 1.74/1.01  fof(f21,plain,(
% 1.74/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.74/1.01    inference(flattening,[],[f20])).
% 1.74/1.01  
% 1.74/1.01  fof(f27,plain,(
% 1.74/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f26,plain,(
% 1.74/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f25,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f24,plain,(
% 1.74/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f28,plain,(
% 1.74/1.02    (((k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 1.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f21,f27,f26,f25,f24])).
% 1.74/1.02  
% 1.74/1.02  fof(f40,plain,(
% 1.74/1.02    v1_funct_1(sK5)),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f42,plain,(
% 1.74/1.02    m1_subset_1(sK6,sK2)),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f3,axiom,(
% 1.74/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f11,plain,(
% 1.74/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.74/1.02    inference(ennf_transformation,[],[f3])).
% 1.74/1.02  
% 1.74/1.02  fof(f12,plain,(
% 1.74/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.74/1.02    inference(flattening,[],[f11])).
% 1.74/1.02  
% 1.74/1.02  fof(f31,plain,(
% 1.74/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f12])).
% 1.74/1.02  
% 1.74/1.02  fof(f7,axiom,(
% 1.74/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f18,plain,(
% 1.74/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.74/1.02    inference(ennf_transformation,[],[f7])).
% 1.74/1.02  
% 1.74/1.02  fof(f19,plain,(
% 1.74/1.02    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.74/1.02    inference(flattening,[],[f18])).
% 1.74/1.02  
% 1.74/1.02  fof(f35,plain,(
% 1.74/1.02    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f19])).
% 1.74/1.02  
% 1.74/1.02  fof(f38,plain,(
% 1.74/1.02    v1_funct_2(sK4,sK2,sK3)),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f37,plain,(
% 1.74/1.02    v1_funct_1(sK4)),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f39,plain,(
% 1.74/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f36,plain,(
% 1.74/1.02    ~v1_xboole_0(sK3)),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f2,axiom,(
% 1.74/1.02    ? [X0] : v1_xboole_0(X0)),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f22,plain,(
% 1.74/1.02    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK0)),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f23,plain,(
% 1.74/1.02    v1_xboole_0(sK0)),
% 1.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f22])).
% 1.74/1.02  
% 1.74/1.02  fof(f30,plain,(
% 1.74/1.02    v1_xboole_0(sK0)),
% 1.74/1.02    inference(cnf_transformation,[],[f23])).
% 1.74/1.02  
% 1.74/1.02  fof(f44,plain,(
% 1.74/1.02    k1_xboole_0 != sK2),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f1,axiom,(
% 1.74/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f10,plain,(
% 1.74/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.74/1.02    inference(ennf_transformation,[],[f1])).
% 1.74/1.02  
% 1.74/1.02  fof(f29,plain,(
% 1.74/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f10])).
% 1.74/1.02  
% 1.74/1.02  fof(f43,plain,(
% 1.74/1.02    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f5,axiom,(
% 1.74/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f14,plain,(
% 1.74/1.02    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.74/1.02    inference(ennf_transformation,[],[f5])).
% 1.74/1.02  
% 1.74/1.02  fof(f15,plain,(
% 1.74/1.02    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.74/1.02    inference(flattening,[],[f14])).
% 1.74/1.02  
% 1.74/1.02  fof(f33,plain,(
% 1.74/1.02    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f15])).
% 1.74/1.02  
% 1.74/1.02  fof(f41,plain,(
% 1.74/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f6,axiom,(
% 1.74/1.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f16,plain,(
% 1.74/1.02    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.74/1.02    inference(ennf_transformation,[],[f6])).
% 1.74/1.02  
% 1.74/1.02  fof(f17,plain,(
% 1.74/1.02    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.74/1.02    inference(flattening,[],[f16])).
% 1.74/1.02  
% 1.74/1.02  fof(f34,plain,(
% 1.74/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f17])).
% 1.74/1.02  
% 1.74/1.02  fof(f45,plain,(
% 1.74/1.02    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f4,axiom,(
% 1.74/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f13,plain,(
% 1.74/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/1.02    inference(ennf_transformation,[],[f4])).
% 1.74/1.02  
% 1.74/1.02  fof(f32,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.74/1.02    inference(cnf_transformation,[],[f13])).
% 1.74/1.02  
% 1.74/1.02  cnf(c_12,negated_conjecture,
% 1.74/1.02      ( v1_funct_1(sK5) ),
% 1.74/1.02      inference(cnf_transformation,[],[f40]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_802,negated_conjecture,
% 1.74/1.02      ( v1_funct_1(sK5) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1119,plain,
% 1.74/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_10,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK6,sK2) ),
% 1.74/1.02      inference(cnf_transformation,[],[f42]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_804,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK6,sK2) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1117,plain,
% 1.74/1.02      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f31]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_6,plain,
% 1.74/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.74/1.02      | ~ r2_hidden(X3,X1)
% 1.74/1.02      | ~ v1_funct_1(X4)
% 1.74/1.02      | ~ v1_funct_1(X0)
% 1.74/1.02      | ~ v1_relat_1(X4)
% 1.74/1.02      | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 1.74/1.02      | k1_xboole_0 = X2 ),
% 1.74/1.02      inference(cnf_transformation,[],[f35]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_14,negated_conjecture,
% 1.74/1.02      ( v1_funct_2(sK4,sK2,sK3) ),
% 1.74/1.02      inference(cnf_transformation,[],[f38]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_327,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.74/1.02      | ~ r2_hidden(X3,X1)
% 1.74/1.02      | ~ v1_funct_1(X4)
% 1.74/1.02      | ~ v1_funct_1(X0)
% 1.74/1.02      | ~ v1_relat_1(X4)
% 1.74/1.02      | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
% 1.74/1.02      | sK3 != X2
% 1.74/1.02      | sK2 != X1
% 1.74/1.02      | sK4 != X0
% 1.74/1.02      | k1_xboole_0 = X2 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_328,plain,
% 1.74/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 1.74/1.02      | ~ r2_hidden(X0,sK2)
% 1.74/1.02      | ~ v1_funct_1(X1)
% 1.74/1.02      | ~ v1_funct_1(sK4)
% 1.74/1.02      | ~ v1_relat_1(X1)
% 1.74/1.02      | k1_funct_1(X1,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,X1),X0)
% 1.74/1.02      | k1_xboole_0 = sK3 ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_327]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_15,negated_conjecture,
% 1.74/1.02      ( v1_funct_1(sK4) ),
% 1.74/1.02      inference(cnf_transformation,[],[f37]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_13,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 1.74/1.02      inference(cnf_transformation,[],[f39]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_332,plain,
% 1.74/1.02      ( ~ v1_funct_1(X1)
% 1.74/1.02      | ~ r2_hidden(X0,sK2)
% 1.74/1.02      | ~ v1_relat_1(X1)
% 1.74/1.02      | k1_funct_1(X1,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,X1),X0)
% 1.74/1.02      | k1_xboole_0 = sK3 ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_328,c_15,c_13]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_333,plain,
% 1.74/1.02      ( ~ r2_hidden(X0,sK2)
% 1.74/1.02      | ~ v1_funct_1(X1)
% 1.74/1.02      | ~ v1_relat_1(X1)
% 1.74/1.02      | k1_funct_1(X1,k1_funct_1(sK4,X0)) = k1_funct_1(k5_relat_1(sK4,X1),X0)
% 1.74/1.02      | k1_xboole_0 = sK3 ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_332]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_448,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,X1)
% 1.74/1.02      | ~ v1_funct_1(X2)
% 1.74/1.02      | ~ v1_relat_1(X2)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | X3 != X0
% 1.74/1.02      | k1_funct_1(k5_relat_1(sK4,X2),X3) = k1_funct_1(X2,k1_funct_1(sK4,X3))
% 1.74/1.02      | sK3 = k1_xboole_0
% 1.74/1.02      | sK2 != X1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_333]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_449,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,sK2)
% 1.74/1.02      | ~ v1_funct_1(X1)
% 1.74/1.02      | ~ v1_relat_1(X1)
% 1.74/1.02      | v1_xboole_0(sK2)
% 1.74/1.02      | k1_funct_1(k5_relat_1(sK4,X1),X0) = k1_funct_1(X1,k1_funct_1(sK4,X0))
% 1.74/1.02      | sK3 = k1_xboole_0 ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_448]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_797,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0_51,sK2)
% 1.74/1.02      | ~ v1_funct_1(X1_51)
% 1.74/1.02      | ~ v1_relat_1(X1_51)
% 1.74/1.02      | v1_xboole_0(sK2)
% 1.74/1.02      | sK3 = k1_xboole_0
% 1.74/1.02      | k1_funct_1(k5_relat_1(sK4,X1_51),X0_51) = k1_funct_1(X1_51,k1_funct_1(sK4,X0_51)) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_449]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_812,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0_51,sK2)
% 1.74/1.02      | ~ v1_funct_1(X1_51)
% 1.74/1.02      | ~ v1_relat_1(X1_51)
% 1.74/1.02      | k1_funct_1(k5_relat_1(sK4,X1_51),X0_51) = k1_funct_1(X1_51,k1_funct_1(sK4,X0_51))
% 1.74/1.02      | ~ sP0_iProver_split ),
% 1.74/1.02      inference(splitting,
% 1.74/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.74/1.02                [c_797]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1125,plain,
% 1.74/1.02      ( k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51))
% 1.74/1.02      | m1_subset_1(X1_51,sK2) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | v1_relat_1(X0_51) != iProver_top
% 1.74/1.02      | sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_16,negated_conjecture,
% 1.74/1.02      ( ~ v1_xboole_0(sK3) ),
% 1.74/1.02      inference(cnf_transformation,[],[f36]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1,plain,
% 1.74/1.02      ( v1_xboole_0(sK0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f30]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_8,negated_conjecture,
% 1.74/1.02      ( k1_xboole_0 != sK2 ),
% 1.74/1.02      inference(cnf_transformation,[],[f44]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_806,negated_conjecture,
% 1.74/1.02      ( k1_xboole_0 != sK2 ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_813,plain,
% 1.74/1.02      ( v1_xboole_0(sK2) | sP0_iProver_split | sK3 = k1_xboole_0 ),
% 1.74/1.02      inference(splitting,
% 1.74/1.02                [splitting(split),new_symbols(definition,[])],
% 1.74/1.02                [c_797]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_870,plain,
% 1.74/1.02      ( sK3 = k1_xboole_0
% 1.74/1.02      | v1_xboole_0(sK2) = iProver_top
% 1.74/1.02      | sP0_iProver_split = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_813]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_871,plain,
% 1.74/1.02      ( k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51))
% 1.74/1.02      | m1_subset_1(X1_51,sK2) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | v1_relat_1(X0_51) != iProver_top
% 1.74/1.02      | sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_0,plain,
% 1.74/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.74/1.02      inference(cnf_transformation,[],[f29]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_811,plain,
% 1.74/1.02      ( ~ v1_xboole_0(X0_52) | k1_xboole_0 = X0_52 ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1227,plain,
% 1.74/1.02      ( ~ v1_xboole_0(sK0) | k1_xboole_0 = sK0 ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_811]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1230,plain,
% 1.74/1.02      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_811]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1231,plain,
% 1.74/1.02      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_822,plain,
% 1.74/1.02      ( ~ v1_xboole_0(X0_52) | v1_xboole_0(X1_52) | X1_52 != X0_52 ),
% 1.74/1.02      theory(equality) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1243,plain,
% 1.74/1.02      ( v1_xboole_0(X0_52) | ~ v1_xboole_0(sK0) | X0_52 != sK0 ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_822]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1384,plain,
% 1.74/1.02      ( ~ v1_xboole_0(sK0)
% 1.74/1.02      | v1_xboole_0(k1_xboole_0)
% 1.74/1.02      | k1_xboole_0 != sK0 ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_1243]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1551,plain,
% 1.74/1.02      ( v1_xboole_0(X0_52)
% 1.74/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 1.74/1.02      | X0_52 != k1_xboole_0 ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_822]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1556,plain,
% 1.74/1.02      ( v1_xboole_0(sK3)
% 1.74/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 1.74/1.02      | sK3 != k1_xboole_0 ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_1551]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1846,plain,
% 1.74/1.02      ( v1_relat_1(X0_51) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | m1_subset_1(X1_51,sK2) != iProver_top
% 1.74/1.02      | k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51)) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_1125,c_16,c_1,c_806,c_870,c_871,c_1227,c_1231,c_1384,
% 1.74/1.02                 c_1556]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1847,plain,
% 1.74/1.02      ( k1_funct_1(k5_relat_1(sK4,X0_51),X1_51) = k1_funct_1(X0_51,k1_funct_1(sK4,X1_51))
% 1.74/1.02      | m1_subset_1(X1_51,sK2) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1846]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1856,plain,
% 1.74/1.02      ( k1_funct_1(X0_51,k1_funct_1(sK4,sK6)) = k1_funct_1(k5_relat_1(sK4,X0_51),sK6)
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | v1_relat_1(X0_51) != iProver_top ),
% 1.74/1.02      inference(superposition,[status(thm)],[c_1117,c_1847]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1864,plain,
% 1.74/1.02      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 1.74/1.02      | v1_relat_1(sK5) != iProver_top ),
% 1.74/1.02      inference(superposition,[status(thm)],[c_1119,c_1856]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_9,negated_conjecture,
% 1.74/1.02      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 1.74/1.02      inference(cnf_transformation,[],[f43]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_805,negated_conjecture,
% 1.74/1.02      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1116,plain,
% 1.74/1.02      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4,plain,
% 1.74/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 1.74/1.02      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 1.74/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.74/1.02      | ~ v1_funct_1(X4)
% 1.74/1.02      | ~ v1_funct_1(X0)
% 1.74/1.02      | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
% 1.74/1.02      | k1_xboole_0 = X2 ),
% 1.74/1.02      inference(cnf_transformation,[],[f33]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_354,plain,
% 1.74/1.02      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 1.74/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.74/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.74/1.02      | ~ v1_funct_1(X4)
% 1.74/1.02      | ~ v1_funct_1(X2)
% 1.74/1.02      | k1_partfun1(X0,X1,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,X4)
% 1.74/1.02      | sK3 != X1
% 1.74/1.02      | sK2 != X0
% 1.74/1.02      | sK4 != X2
% 1.74/1.02      | k1_xboole_0 = X1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_355,plain,
% 1.74/1.02      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 1.74/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 1.74/1.02      | ~ v1_funct_1(X1)
% 1.74/1.02      | ~ v1_funct_1(sK4)
% 1.74/1.02      | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 1.74/1.02      | k1_xboole_0 = sK3 ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_354]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_359,plain,
% 1.74/1.02      ( ~ v1_funct_1(X1)
% 1.74/1.02      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 1.74/1.02      | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 1.74/1.02      | k1_xboole_0 = sK3 ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_355,c_15,c_13]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_360,plain,
% 1.74/1.02      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,X1))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
% 1.74/1.02      | ~ v1_funct_1(X1)
% 1.74/1.02      | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 1.74/1.02      | k1_xboole_0 = sK3 ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_359]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_798,plain,
% 1.74/1.02      ( ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0_52,X0_51))
% 1.74/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X0_52)))
% 1.74/1.02      | ~ v1_funct_1(X0_51)
% 1.74/1.02      | k1_xboole_0 = sK3
% 1.74/1.02      | k1_partfun1(sK2,sK3,sK3,X0_52,sK4,X0_51) = k8_funct_2(sK2,sK3,X0_52,sK4,X0_51) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_360]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1123,plain,
% 1.74/1.02      ( k1_xboole_0 = sK3
% 1.74/1.02      | k1_partfun1(sK2,sK3,sK3,X0_52,sK4,X0_51) = k8_funct_2(sK2,sK3,X0_52,sK4,X0_51)
% 1.74/1.02      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0_52,X0_51)) != iProver_top
% 1.74/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X0_52))) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1712,plain,
% 1.74/1.02      ( sK3 = k1_xboole_0
% 1.74/1.02      | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
% 1.74/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 1.74/1.02      | v1_funct_1(sK5) != iProver_top ),
% 1.74/1.02      inference(superposition,[status(thm)],[c_1116,c_1123]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_11,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 1.74/1.02      inference(cnf_transformation,[],[f41]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_803,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1118,plain,
% 1.74/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_801,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1120,plain,
% 1.74/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_5,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.74/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.74/1.02      | ~ v1_funct_1(X3)
% 1.74/1.02      | ~ v1_funct_1(X0)
% 1.74/1.02      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f34]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_808,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.74/1.02      | ~ m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52)))
% 1.74/1.02      | ~ v1_funct_1(X1_51)
% 1.74/1.02      | ~ v1_funct_1(X0_51)
% 1.74/1.02      | k1_partfun1(X2_52,X3_52,X0_52,X1_52,X1_51,X0_51) = k5_relat_1(X1_51,X0_51) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1115,plain,
% 1.74/1.02      ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X0_51,X1_51) = k5_relat_1(X0_51,X1_51)
% 1.74/1.02      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 1.74/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | v1_funct_1(X1_51) != iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1489,plain,
% 1.74/1.02      ( k1_partfun1(sK2,sK3,X0_52,X1_52,sK4,X0_51) = k5_relat_1(sK4,X0_51)
% 1.74/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | v1_funct_1(sK4) != iProver_top ),
% 1.74/1.02      inference(superposition,[status(thm)],[c_1120,c_1115]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_18,plain,
% 1.74/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1629,plain,
% 1.74/1.02      ( v1_funct_1(X0_51) != iProver_top
% 1.74/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.74/1.02      | k1_partfun1(sK2,sK3,X0_52,X1_52,sK4,X0_51) = k5_relat_1(sK4,X0_51) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_1489,c_18]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1630,plain,
% 1.74/1.02      ( k1_partfun1(sK2,sK3,X0_52,X1_52,sK4,X0_51) = k5_relat_1(sK4,X0_51)
% 1.74/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.74/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1629]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1636,plain,
% 1.74/1.02      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 1.74/1.02      | v1_funct_1(sK5) != iProver_top ),
% 1.74/1.02      inference(superposition,[status(thm)],[c_1118,c_1630]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1282,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.74/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 1.74/1.02      | ~ v1_funct_1(X0_51)
% 1.74/1.02      | ~ v1_funct_1(sK5)
% 1.74/1.02      | k1_partfun1(X0_52,X1_52,sK3,sK1,X0_51,sK5) = k5_relat_1(X0_51,sK5) ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_808]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1358,plain,
% 1.74/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 1.74/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 1.74/1.02      | ~ v1_funct_1(sK4)
% 1.74/1.02      | ~ v1_funct_1(sK5)
% 1.74/1.02      | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_1282]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1649,plain,
% 1.74/1.02      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_1636,c_15,c_13,c_12,c_11,c_1358]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1713,plain,
% 1.74/1.02      ( sK3 = k1_xboole_0
% 1.74/1.02      | k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 1.74/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 1.74/1.02      | v1_funct_1(sK5) != iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_1712,c_1649]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_21,plain,
% 1.74/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_22,plain,
% 1.74/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1803,plain,
% 1.74/1.02      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_1713,c_16,c_21,c_22,c_1,c_1227,c_1384,c_1556]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_7,negated_conjecture,
% 1.74/1.02      ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 1.74/1.02      inference(cnf_transformation,[],[f45]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_807,negated_conjecture,
% 1.74/1.02      ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1806,plain,
% 1.74/1.02      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 1.74/1.02      inference(demodulation,[status(thm)],[c_1803,c_807]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.74/1.02      | v1_relat_1(X0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f32]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_809,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.74/1.02      | v1_relat_1(X0_51) ),
% 1.74/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1233,plain,
% 1.74/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 1.74/1.02      | v1_relat_1(sK5) ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_809]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1234,plain,
% 1.74/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 1.74/1.02      | v1_relat_1(sK5) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(contradiction,plain,
% 1.74/1.02      ( $false ),
% 1.74/1.02      inference(minisat,[status(thm)],[c_1864,c_1806,c_1234,c_22]) ).
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.74/1.02  
% 1.74/1.02  ------                               Statistics
% 1.74/1.02  
% 1.74/1.02  ------ General
% 1.74/1.02  
% 1.74/1.02  abstr_ref_over_cycles:                  0
% 1.74/1.02  abstr_ref_under_cycles:                 0
% 1.74/1.02  gc_basic_clause_elim:                   0
% 1.74/1.02  forced_gc_time:                         0
% 1.74/1.02  parsing_time:                           0.008
% 1.74/1.02  unif_index_cands_time:                  0.
% 1.74/1.02  unif_index_add_time:                    0.
% 1.74/1.02  orderings_time:                         0.
% 1.74/1.02  out_proof_time:                         0.013
% 1.74/1.02  total_time:                             0.096
% 1.74/1.02  num_of_symbols:                         60
% 1.74/1.02  num_of_terms:                           1800
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing
% 1.74/1.02  
% 1.74/1.02  num_of_splits:                          1
% 1.74/1.02  num_of_split_atoms:                     1
% 1.74/1.02  num_of_reused_defs:                     0
% 1.74/1.02  num_eq_ax_congr_red:                    19
% 1.74/1.02  num_of_sem_filtered_clauses:            1
% 1.74/1.02  num_of_subtypes:                        5
% 1.74/1.02  monotx_restored_types:                  0
% 1.74/1.02  sat_num_of_epr_types:                   0
% 1.74/1.02  sat_num_of_non_cyclic_types:            0
% 1.74/1.02  sat_guarded_non_collapsed_types:        1
% 1.74/1.02  num_pure_diseq_elim:                    0
% 1.74/1.02  simp_replaced_by:                       0
% 1.74/1.02  res_preprocessed:                       103
% 1.74/1.02  prep_upred:                             0
% 1.74/1.02  prep_unflattend:                        21
% 1.74/1.02  smt_new_axioms:                         0
% 1.74/1.02  pred_elim_cands:                        5
% 1.74/1.02  pred_elim:                              2
% 1.74/1.02  pred_elim_cl:                           2
% 1.74/1.02  pred_elim_cycles:                       13
% 1.74/1.02  merged_defs:                            0
% 1.74/1.02  merged_defs_ncl:                        0
% 1.74/1.02  bin_hyper_res:                          0
% 1.74/1.02  prep_cycles:                            4
% 1.74/1.02  pred_elim_time:                         0.011
% 1.74/1.02  splitting_time:                         0.
% 1.74/1.02  sem_filter_time:                        0.
% 1.74/1.02  monotx_time:                            0.
% 1.74/1.02  subtype_inf_time:                       0.
% 1.74/1.02  
% 1.74/1.02  ------ Problem properties
% 1.74/1.02  
% 1.74/1.02  clauses:                                16
% 1.74/1.02  conjectures:                            9
% 1.74/1.02  epr:                                    8
% 1.74/1.02  horn:                                   14
% 1.74/1.02  ground:                                 11
% 1.74/1.02  unary:                                  10
% 1.74/1.02  binary:                                 2
% 1.74/1.02  lits:                                   32
% 1.74/1.02  lits_eq:                                8
% 1.74/1.02  fd_pure:                                0
% 1.74/1.02  fd_pseudo:                              0
% 1.74/1.02  fd_cond:                                1
% 1.74/1.02  fd_pseudo_cond:                         0
% 1.74/1.02  ac_symbols:                             0
% 1.74/1.02  
% 1.74/1.02  ------ Propositional Solver
% 1.74/1.02  
% 1.74/1.02  prop_solver_calls:                      27
% 1.74/1.02  prop_fast_solver_calls:                 686
% 1.74/1.02  smt_solver_calls:                       0
% 1.74/1.02  smt_fast_solver_calls:                  0
% 1.74/1.02  prop_num_of_clauses:                    469
% 1.74/1.02  prop_preprocess_simplified:             2485
% 1.74/1.02  prop_fo_subsumed:                       16
% 1.74/1.02  prop_solver_time:                       0.
% 1.74/1.02  smt_solver_time:                        0.
% 1.74/1.02  smt_fast_solver_time:                   0.
% 1.74/1.02  prop_fast_solver_time:                  0.
% 1.74/1.02  prop_unsat_core_time:                   0.
% 1.74/1.02  
% 1.74/1.02  ------ QBF
% 1.74/1.02  
% 1.74/1.02  qbf_q_res:                              0
% 1.74/1.02  qbf_num_tautologies:                    0
% 1.74/1.02  qbf_prep_cycles:                        0
% 1.74/1.02  
% 1.74/1.02  ------ BMC1
% 1.74/1.02  
% 1.74/1.02  bmc1_current_bound:                     -1
% 1.74/1.02  bmc1_last_solved_bound:                 -1
% 1.74/1.02  bmc1_unsat_core_size:                   -1
% 1.74/1.02  bmc1_unsat_core_parents_size:           -1
% 1.74/1.02  bmc1_merge_next_fun:                    0
% 1.74/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.74/1.02  
% 1.74/1.02  ------ Instantiation
% 1.74/1.02  
% 1.74/1.02  inst_num_of_clauses:                    156
% 1.74/1.02  inst_num_in_passive:                    16
% 1.74/1.02  inst_num_in_active:                     132
% 1.74/1.02  inst_num_in_unprocessed:                8
% 1.74/1.02  inst_num_of_loops:                      140
% 1.74/1.02  inst_num_of_learning_restarts:          0
% 1.74/1.02  inst_num_moves_active_passive:          5
% 1.74/1.02  inst_lit_activity:                      0
% 1.74/1.02  inst_lit_activity_moves:                0
% 1.74/1.02  inst_num_tautologies:                   0
% 1.74/1.02  inst_num_prop_implied:                  0
% 1.74/1.02  inst_num_existing_simplified:           0
% 1.74/1.02  inst_num_eq_res_simplified:             0
% 1.74/1.02  inst_num_child_elim:                    0
% 1.74/1.02  inst_num_of_dismatching_blockings:      15
% 1.74/1.02  inst_num_of_non_proper_insts:           126
% 1.74/1.02  inst_num_of_duplicates:                 0
% 1.74/1.02  inst_inst_num_from_inst_to_res:         0
% 1.74/1.02  inst_dismatching_checking_time:         0.
% 1.74/1.02  
% 1.74/1.02  ------ Resolution
% 1.74/1.02  
% 1.74/1.02  res_num_of_clauses:                     0
% 1.74/1.02  res_num_in_passive:                     0
% 1.74/1.02  res_num_in_active:                      0
% 1.74/1.02  res_num_of_loops:                       107
% 1.74/1.02  res_forward_subset_subsumed:            33
% 1.74/1.02  res_backward_subset_subsumed:           0
% 1.74/1.02  res_forward_subsumed:                   0
% 1.74/1.02  res_backward_subsumed:                  0
% 1.74/1.02  res_forward_subsumption_resolution:     0
% 1.74/1.02  res_backward_subsumption_resolution:    0
% 1.74/1.02  res_clause_to_clause_subsumption:       54
% 1.74/1.02  res_orphan_elimination:                 0
% 1.74/1.02  res_tautology_del:                      23
% 1.74/1.02  res_num_eq_res_simplified:              0
% 1.74/1.02  res_num_sel_changes:                    0
% 1.74/1.02  res_moves_from_active_to_pass:          0
% 1.74/1.02  
% 1.74/1.02  ------ Superposition
% 1.74/1.02  
% 1.74/1.02  sup_time_total:                         0.
% 1.74/1.02  sup_time_generating:                    0.
% 1.74/1.02  sup_time_sim_full:                      0.
% 1.74/1.02  sup_time_sim_immed:                     0.
% 1.74/1.02  
% 1.74/1.02  sup_num_of_clauses:                     29
% 1.74/1.02  sup_num_in_active:                      26
% 1.74/1.02  sup_num_in_passive:                     3
% 1.74/1.02  sup_num_of_loops:                       27
% 1.74/1.02  sup_fw_superposition:                   12
% 1.74/1.02  sup_bw_superposition:                   2
% 1.74/1.02  sup_immediate_simplified:               1
% 1.74/1.02  sup_given_eliminated:                   0
% 1.74/1.02  comparisons_done:                       0
% 1.74/1.02  comparisons_avoided:                    2
% 1.74/1.02  
% 1.74/1.02  ------ Simplifications
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  sim_fw_subset_subsumed:                 0
% 1.74/1.02  sim_bw_subset_subsumed:                 0
% 1.74/1.02  sim_fw_subsumed:                        0
% 1.74/1.02  sim_bw_subsumed:                        0
% 1.74/1.02  sim_fw_subsumption_res:                 0
% 1.74/1.02  sim_bw_subsumption_res:                 0
% 1.74/1.02  sim_tautology_del:                      0
% 1.74/1.02  sim_eq_tautology_del:                   1
% 1.74/1.02  sim_eq_res_simp:                        0
% 1.74/1.02  sim_fw_demodulated:                     0
% 1.74/1.02  sim_bw_demodulated:                     2
% 1.74/1.02  sim_light_normalised:                   1
% 1.74/1.02  sim_joinable_taut:                      0
% 1.74/1.02  sim_joinable_simp:                      0
% 1.74/1.02  sim_ac_normalised:                      0
% 1.74/1.02  sim_smt_subsumption:                    0
% 1.74/1.02  
%------------------------------------------------------------------------------
