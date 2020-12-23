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
% DateTime   : Thu Dec  3 12:09:41 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 491 expanded)
%              Number of clauses        :   83 ( 141 expanded)
%              Number of leaves         :   13 ( 166 expanded)
%              Depth                    :   23
%              Number of atoms          :  480 (3857 expanded)
%              Number of equality atoms :  177 ( 997 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
            ( k1_funct_1(sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
                ( k1_funct_1(X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5)
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

fof(f27,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f26,f25,f24,f23])).

fof(f43,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_321,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | k1_partfun1(X0,X1,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,X4)
    | sK2 != X1
    | sK1 != X0
    | sK3 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_322,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_326,plain,
    ( ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_16,c_14])).

cnf(c_327,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ v1_funct_1(X1)
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_326])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
    | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4)
    | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
    | sK2 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_327])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_17,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_174,plain,
    ( sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_364,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4)
    | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_174])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
    | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4)
    | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3) ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
    | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4) ),
    inference(equality_resolution_simp,[status(thm)],[c_365])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_relset_1(sK2,X0_51,X0_50) != k1_relset_1(sK2,sK0,sK4)
    | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_499])).

cnf(c_937,plain,
    ( k1_relset_1(sK2,X0_51,X0_50) != k1_relset_1(sK2,sK0,sK4)
    | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_1713,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_937])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_641,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_931,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_639,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_933,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_929,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_1289,plain,
    ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_929])).

cnf(c_19,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1484,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1289,c_19])).

cnf(c_1485,plain,
    ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_1484])).

cnf(c_1491,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_1485])).

cnf(c_13,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1078,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0_51,X1_51,sK2,sK0,X0_50,sK4) = k5_relat_1(X0_50,sK4) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1504,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_16,c_14,c_13,c_12,c_1139])).

cnf(c_1714,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1713,c_1504])).

cnf(c_22,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1717,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1714,c_22,c_23])).

cnf(c_8,negated_conjecture,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_644,negated_conjecture,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1720,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1717,c_644])).

cnf(c_640,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_932,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_642,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_930,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
    | sK2 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_295,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_299,plain,
    ( ~ v1_funct_1(X1)
    | ~ r2_hidden(X0,sK1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_295,c_16,c_14])).

cnf(c_300,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_299])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | X3 != X0
    | k1_funct_1(k5_relat_1(sK3,X2),X3) = k1_funct_1(X2,k1_funct_1(sK3,X3))
    | sK2 = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_300])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(sK1)
    | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
    | sK2 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
    | v1_xboole_0(sK1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_174])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(sK1)
    | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | ~ v1_funct_1(X1_50)
    | ~ v1_relat_1(X1_50)
    | v1_xboole_0(sK1)
    | k1_funct_1(k5_relat_1(sK3,X1_50),X0_50) = k1_funct_1(X1_50,k1_funct_1(sK3,X0_50)) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_936,plain,
    ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
    | m1_subset_1(X1_50,sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_1530,plain,
    ( k1_funct_1(X0_50,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,X0_50),sK5)
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_936])).

cnf(c_1576,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_1530])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_927,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_647])).

cnf(c_1233,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_927])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_646,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_928,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_646])).

cnf(c_1315,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1233,c_928])).

cnf(c_1593,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v1_xboole_0(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1576,c_1315])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_648,plain,
    ( ~ v1_xboole_0(X0_51)
    | k1_xboole_0 = X0_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_926,plain,
    ( k1_xboole_0 = X0_51
    | v1_xboole_0(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_1599,plain,
    ( sK1 = k1_xboole_0
    | k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1593,c_926])).

cnf(c_9,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_643,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1316,plain,
    ( v1_relat_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1315])).

cnf(c_1590,plain,
    ( ~ v1_relat_1(sK4)
    | v1_xboole_0(sK1)
    | k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1576])).

cnf(c_1611,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_648])).

cnf(c_1653,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1599,c_643,c_1316,c_1590,c_1611])).

cnf(c_1721,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1720,c_1653])).

cnf(c_1722,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1721])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.51/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/0.99  
% 1.51/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.51/0.99  
% 1.51/0.99  ------  iProver source info
% 1.51/0.99  
% 1.51/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.51/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.51/0.99  git: non_committed_changes: false
% 1.51/0.99  git: last_make_outside_of_git: false
% 1.51/0.99  
% 1.51/0.99  ------ 
% 1.51/0.99  
% 1.51/0.99  ------ Input Options
% 1.51/0.99  
% 1.51/0.99  --out_options                           all
% 1.51/0.99  --tptp_safe_out                         true
% 1.51/0.99  --problem_path                          ""
% 1.51/0.99  --include_path                          ""
% 1.51/0.99  --clausifier                            res/vclausify_rel
% 1.51/0.99  --clausifier_options                    --mode clausify
% 1.51/0.99  --stdin                                 false
% 1.51/0.99  --stats_out                             all
% 1.51/0.99  
% 1.51/0.99  ------ General Options
% 1.51/0.99  
% 1.51/0.99  --fof                                   false
% 1.51/0.99  --time_out_real                         305.
% 1.51/0.99  --time_out_virtual                      -1.
% 1.51/0.99  --symbol_type_check                     false
% 1.51/0.99  --clausify_out                          false
% 1.51/0.99  --sig_cnt_out                           false
% 1.51/0.99  --trig_cnt_out                          false
% 1.51/0.99  --trig_cnt_out_tolerance                1.
% 1.51/0.99  --trig_cnt_out_sk_spl                   false
% 1.51/0.99  --abstr_cl_out                          false
% 1.51/0.99  
% 1.51/0.99  ------ Global Options
% 1.51/0.99  
% 1.51/0.99  --schedule                              default
% 1.51/0.99  --add_important_lit                     false
% 1.51/0.99  --prop_solver_per_cl                    1000
% 1.51/0.99  --min_unsat_core                        false
% 1.51/0.99  --soft_assumptions                      false
% 1.51/0.99  --soft_lemma_size                       3
% 1.51/0.99  --prop_impl_unit_size                   0
% 1.51/0.99  --prop_impl_unit                        []
% 1.51/0.99  --share_sel_clauses                     true
% 1.51/0.99  --reset_solvers                         false
% 1.51/0.99  --bc_imp_inh                            [conj_cone]
% 1.51/0.99  --conj_cone_tolerance                   3.
% 1.51/0.99  --extra_neg_conj                        none
% 1.51/0.99  --large_theory_mode                     true
% 1.51/0.99  --prolific_symb_bound                   200
% 1.51/0.99  --lt_threshold                          2000
% 1.51/0.99  --clause_weak_htbl                      true
% 1.51/0.99  --gc_record_bc_elim                     false
% 1.51/0.99  
% 1.51/0.99  ------ Preprocessing Options
% 1.51/0.99  
% 1.51/0.99  --preprocessing_flag                    true
% 1.51/0.99  --time_out_prep_mult                    0.1
% 1.51/0.99  --splitting_mode                        input
% 1.51/0.99  --splitting_grd                         true
% 1.51/0.99  --splitting_cvd                         false
% 1.51/0.99  --splitting_cvd_svl                     false
% 1.51/0.99  --splitting_nvd                         32
% 1.51/0.99  --sub_typing                            true
% 1.51/0.99  --prep_gs_sim                           true
% 1.51/0.99  --prep_unflatten                        true
% 1.51/0.99  --prep_res_sim                          true
% 1.51/0.99  --prep_upred                            true
% 1.51/0.99  --prep_sem_filter                       exhaustive
% 1.51/0.99  --prep_sem_filter_out                   false
% 1.51/0.99  --pred_elim                             true
% 1.51/0.99  --res_sim_input                         true
% 1.51/0.99  --eq_ax_congr_red                       true
% 1.51/0.99  --pure_diseq_elim                       true
% 1.51/0.99  --brand_transform                       false
% 1.51/0.99  --non_eq_to_eq                          false
% 1.51/0.99  --prep_def_merge                        true
% 1.51/0.99  --prep_def_merge_prop_impl              false
% 1.51/1.00  --prep_def_merge_mbd                    true
% 1.51/1.00  --prep_def_merge_tr_red                 false
% 1.51/1.00  --prep_def_merge_tr_cl                  false
% 1.51/1.00  --smt_preprocessing                     true
% 1.51/1.00  --smt_ac_axioms                         fast
% 1.51/1.00  --preprocessed_out                      false
% 1.51/1.00  --preprocessed_stats                    false
% 1.51/1.00  
% 1.51/1.00  ------ Abstraction refinement Options
% 1.51/1.00  
% 1.51/1.00  --abstr_ref                             []
% 1.51/1.00  --abstr_ref_prep                        false
% 1.51/1.00  --abstr_ref_until_sat                   false
% 1.51/1.00  --abstr_ref_sig_restrict                funpre
% 1.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/1.00  --abstr_ref_under                       []
% 1.51/1.00  
% 1.51/1.00  ------ SAT Options
% 1.51/1.00  
% 1.51/1.00  --sat_mode                              false
% 1.51/1.00  --sat_fm_restart_options                ""
% 1.51/1.00  --sat_gr_def                            false
% 1.51/1.00  --sat_epr_types                         true
% 1.51/1.00  --sat_non_cyclic_types                  false
% 1.51/1.00  --sat_finite_models                     false
% 1.51/1.00  --sat_fm_lemmas                         false
% 1.51/1.00  --sat_fm_prep                           false
% 1.51/1.00  --sat_fm_uc_incr                        true
% 1.51/1.00  --sat_out_model                         small
% 1.51/1.00  --sat_out_clauses                       false
% 1.51/1.00  
% 1.51/1.00  ------ QBF Options
% 1.51/1.00  
% 1.51/1.00  --qbf_mode                              false
% 1.51/1.00  --qbf_elim_univ                         false
% 1.51/1.00  --qbf_dom_inst                          none
% 1.51/1.00  --qbf_dom_pre_inst                      false
% 1.51/1.00  --qbf_sk_in                             false
% 1.51/1.00  --qbf_pred_elim                         true
% 1.51/1.00  --qbf_split                             512
% 1.51/1.00  
% 1.51/1.00  ------ BMC1 Options
% 1.51/1.00  
% 1.51/1.00  --bmc1_incremental                      false
% 1.51/1.00  --bmc1_axioms                           reachable_all
% 1.51/1.00  --bmc1_min_bound                        0
% 1.51/1.00  --bmc1_max_bound                        -1
% 1.51/1.00  --bmc1_max_bound_default                -1
% 1.51/1.00  --bmc1_symbol_reachability              true
% 1.51/1.00  --bmc1_property_lemmas                  false
% 1.51/1.00  --bmc1_k_induction                      false
% 1.51/1.00  --bmc1_non_equiv_states                 false
% 1.51/1.00  --bmc1_deadlock                         false
% 1.51/1.00  --bmc1_ucm                              false
% 1.51/1.00  --bmc1_add_unsat_core                   none
% 1.51/1.00  --bmc1_unsat_core_children              false
% 1.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/1.00  --bmc1_out_stat                         full
% 1.51/1.00  --bmc1_ground_init                      false
% 1.51/1.00  --bmc1_pre_inst_next_state              false
% 1.51/1.00  --bmc1_pre_inst_state                   false
% 1.51/1.00  --bmc1_pre_inst_reach_state             false
% 1.51/1.00  --bmc1_out_unsat_core                   false
% 1.51/1.00  --bmc1_aig_witness_out                  false
% 1.51/1.00  --bmc1_verbose                          false
% 1.51/1.00  --bmc1_dump_clauses_tptp                false
% 1.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.51/1.00  --bmc1_dump_file                        -
% 1.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.51/1.00  --bmc1_ucm_extend_mode                  1
% 1.51/1.00  --bmc1_ucm_init_mode                    2
% 1.51/1.00  --bmc1_ucm_cone_mode                    none
% 1.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.51/1.00  --bmc1_ucm_relax_model                  4
% 1.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/1.00  --bmc1_ucm_layered_model                none
% 1.51/1.00  --bmc1_ucm_max_lemma_size               10
% 1.51/1.00  
% 1.51/1.00  ------ AIG Options
% 1.51/1.00  
% 1.51/1.00  --aig_mode                              false
% 1.51/1.00  
% 1.51/1.00  ------ Instantiation Options
% 1.51/1.00  
% 1.51/1.00  --instantiation_flag                    true
% 1.51/1.00  --inst_sos_flag                         false
% 1.51/1.00  --inst_sos_phase                        true
% 1.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/1.00  --inst_lit_sel_side                     num_symb
% 1.51/1.00  --inst_solver_per_active                1400
% 1.51/1.00  --inst_solver_calls_frac                1.
% 1.51/1.00  --inst_passive_queue_type               priority_queues
% 1.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/1.00  --inst_passive_queues_freq              [25;2]
% 1.51/1.00  --inst_dismatching                      true
% 1.51/1.00  --inst_eager_unprocessed_to_passive     true
% 1.51/1.00  --inst_prop_sim_given                   true
% 1.51/1.00  --inst_prop_sim_new                     false
% 1.51/1.00  --inst_subs_new                         false
% 1.51/1.00  --inst_eq_res_simp                      false
% 1.51/1.00  --inst_subs_given                       false
% 1.51/1.00  --inst_orphan_elimination               true
% 1.51/1.00  --inst_learning_loop_flag               true
% 1.51/1.00  --inst_learning_start                   3000
% 1.51/1.00  --inst_learning_factor                  2
% 1.51/1.00  --inst_start_prop_sim_after_learn       3
% 1.51/1.00  --inst_sel_renew                        solver
% 1.51/1.00  --inst_lit_activity_flag                true
% 1.51/1.00  --inst_restr_to_given                   false
% 1.51/1.00  --inst_activity_threshold               500
% 1.51/1.00  --inst_out_proof                        true
% 1.51/1.00  
% 1.51/1.00  ------ Resolution Options
% 1.51/1.00  
% 1.51/1.00  --resolution_flag                       true
% 1.51/1.00  --res_lit_sel                           adaptive
% 1.51/1.00  --res_lit_sel_side                      none
% 1.51/1.00  --res_ordering                          kbo
% 1.51/1.00  --res_to_prop_solver                    active
% 1.51/1.00  --res_prop_simpl_new                    false
% 1.51/1.00  --res_prop_simpl_given                  true
% 1.51/1.00  --res_passive_queue_type                priority_queues
% 1.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/1.00  --res_passive_queues_freq               [15;5]
% 1.51/1.00  --res_forward_subs                      full
% 1.51/1.00  --res_backward_subs                     full
% 1.51/1.00  --res_forward_subs_resolution           true
% 1.51/1.00  --res_backward_subs_resolution          true
% 1.51/1.00  --res_orphan_elimination                true
% 1.51/1.00  --res_time_limit                        2.
% 1.51/1.00  --res_out_proof                         true
% 1.51/1.00  
% 1.51/1.00  ------ Superposition Options
% 1.51/1.00  
% 1.51/1.00  --superposition_flag                    true
% 1.51/1.00  --sup_passive_queue_type                priority_queues
% 1.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.51/1.00  --demod_completeness_check              fast
% 1.51/1.00  --demod_use_ground                      true
% 1.51/1.00  --sup_to_prop_solver                    passive
% 1.51/1.00  --sup_prop_simpl_new                    true
% 1.51/1.00  --sup_prop_simpl_given                  true
% 1.51/1.00  --sup_fun_splitting                     false
% 1.51/1.00  --sup_smt_interval                      50000
% 1.51/1.00  
% 1.51/1.00  ------ Superposition Simplification Setup
% 1.51/1.00  
% 1.51/1.00  --sup_indices_passive                   []
% 1.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.00  --sup_full_bw                           [BwDemod]
% 1.51/1.00  --sup_immed_triv                        [TrivRules]
% 1.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.00  --sup_immed_bw_main                     []
% 1.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.00  
% 1.51/1.00  ------ Combination Options
% 1.51/1.00  
% 1.51/1.00  --comb_res_mult                         3
% 1.51/1.00  --comb_sup_mult                         2
% 1.51/1.00  --comb_inst_mult                        10
% 1.51/1.00  
% 1.51/1.00  ------ Debug Options
% 1.51/1.00  
% 1.51/1.00  --dbg_backtrace                         false
% 1.51/1.00  --dbg_dump_prop_clauses                 false
% 1.51/1.00  --dbg_dump_prop_clauses_file            -
% 1.51/1.00  --dbg_out_stat                          false
% 1.51/1.00  ------ Parsing...
% 1.51/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.51/1.00  
% 1.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.51/1.00  
% 1.51/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.51/1.00  
% 1.51/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.51/1.00  ------ Proving...
% 1.51/1.00  ------ Problem Properties 
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  clauses                                 15
% 1.51/1.00  conjectures                             8
% 1.51/1.00  EPR                                     7
% 1.51/1.00  Horn                                    14
% 1.51/1.00  unary                                   10
% 1.51/1.00  binary                                  1
% 1.51/1.00  lits                                    29
% 1.51/1.00  lits eq                                 7
% 1.51/1.00  fd_pure                                 0
% 1.51/1.00  fd_pseudo                               0
% 1.51/1.00  fd_cond                                 1
% 1.51/1.00  fd_pseudo_cond                          0
% 1.51/1.00  AC symbols                              0
% 1.51/1.00  
% 1.51/1.00  ------ Schedule dynamic 5 is on 
% 1.51/1.00  
% 1.51/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  ------ 
% 1.51/1.00  Current options:
% 1.51/1.00  ------ 
% 1.51/1.00  
% 1.51/1.00  ------ Input Options
% 1.51/1.00  
% 1.51/1.00  --out_options                           all
% 1.51/1.00  --tptp_safe_out                         true
% 1.51/1.00  --problem_path                          ""
% 1.51/1.00  --include_path                          ""
% 1.51/1.00  --clausifier                            res/vclausify_rel
% 1.51/1.00  --clausifier_options                    --mode clausify
% 1.51/1.00  --stdin                                 false
% 1.51/1.00  --stats_out                             all
% 1.51/1.00  
% 1.51/1.00  ------ General Options
% 1.51/1.00  
% 1.51/1.00  --fof                                   false
% 1.51/1.00  --time_out_real                         305.
% 1.51/1.00  --time_out_virtual                      -1.
% 1.51/1.00  --symbol_type_check                     false
% 1.51/1.00  --clausify_out                          false
% 1.51/1.00  --sig_cnt_out                           false
% 1.51/1.00  --trig_cnt_out                          false
% 1.51/1.00  --trig_cnt_out_tolerance                1.
% 1.51/1.00  --trig_cnt_out_sk_spl                   false
% 1.51/1.00  --abstr_cl_out                          false
% 1.51/1.00  
% 1.51/1.00  ------ Global Options
% 1.51/1.00  
% 1.51/1.00  --schedule                              default
% 1.51/1.00  --add_important_lit                     false
% 1.51/1.00  --prop_solver_per_cl                    1000
% 1.51/1.00  --min_unsat_core                        false
% 1.51/1.00  --soft_assumptions                      false
% 1.51/1.00  --soft_lemma_size                       3
% 1.51/1.00  --prop_impl_unit_size                   0
% 1.51/1.00  --prop_impl_unit                        []
% 1.51/1.00  --share_sel_clauses                     true
% 1.51/1.00  --reset_solvers                         false
% 1.51/1.00  --bc_imp_inh                            [conj_cone]
% 1.51/1.00  --conj_cone_tolerance                   3.
% 1.51/1.00  --extra_neg_conj                        none
% 1.51/1.00  --large_theory_mode                     true
% 1.51/1.00  --prolific_symb_bound                   200
% 1.51/1.00  --lt_threshold                          2000
% 1.51/1.00  --clause_weak_htbl                      true
% 1.51/1.00  --gc_record_bc_elim                     false
% 1.51/1.00  
% 1.51/1.00  ------ Preprocessing Options
% 1.51/1.00  
% 1.51/1.00  --preprocessing_flag                    true
% 1.51/1.00  --time_out_prep_mult                    0.1
% 1.51/1.00  --splitting_mode                        input
% 1.51/1.00  --splitting_grd                         true
% 1.51/1.00  --splitting_cvd                         false
% 1.51/1.00  --splitting_cvd_svl                     false
% 1.51/1.00  --splitting_nvd                         32
% 1.51/1.00  --sub_typing                            true
% 1.51/1.00  --prep_gs_sim                           true
% 1.51/1.00  --prep_unflatten                        true
% 1.51/1.00  --prep_res_sim                          true
% 1.51/1.00  --prep_upred                            true
% 1.51/1.00  --prep_sem_filter                       exhaustive
% 1.51/1.00  --prep_sem_filter_out                   false
% 1.51/1.00  --pred_elim                             true
% 1.51/1.00  --res_sim_input                         true
% 1.51/1.00  --eq_ax_congr_red                       true
% 1.51/1.00  --pure_diseq_elim                       true
% 1.51/1.00  --brand_transform                       false
% 1.51/1.00  --non_eq_to_eq                          false
% 1.51/1.00  --prep_def_merge                        true
% 1.51/1.00  --prep_def_merge_prop_impl              false
% 1.51/1.00  --prep_def_merge_mbd                    true
% 1.51/1.00  --prep_def_merge_tr_red                 false
% 1.51/1.00  --prep_def_merge_tr_cl                  false
% 1.51/1.00  --smt_preprocessing                     true
% 1.51/1.00  --smt_ac_axioms                         fast
% 1.51/1.00  --preprocessed_out                      false
% 1.51/1.00  --preprocessed_stats                    false
% 1.51/1.00  
% 1.51/1.00  ------ Abstraction refinement Options
% 1.51/1.00  
% 1.51/1.00  --abstr_ref                             []
% 1.51/1.00  --abstr_ref_prep                        false
% 1.51/1.00  --abstr_ref_until_sat                   false
% 1.51/1.00  --abstr_ref_sig_restrict                funpre
% 1.51/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.51/1.00  --abstr_ref_under                       []
% 1.51/1.00  
% 1.51/1.00  ------ SAT Options
% 1.51/1.00  
% 1.51/1.00  --sat_mode                              false
% 1.51/1.00  --sat_fm_restart_options                ""
% 1.51/1.00  --sat_gr_def                            false
% 1.51/1.00  --sat_epr_types                         true
% 1.51/1.00  --sat_non_cyclic_types                  false
% 1.51/1.00  --sat_finite_models                     false
% 1.51/1.00  --sat_fm_lemmas                         false
% 1.51/1.00  --sat_fm_prep                           false
% 1.51/1.00  --sat_fm_uc_incr                        true
% 1.51/1.00  --sat_out_model                         small
% 1.51/1.00  --sat_out_clauses                       false
% 1.51/1.00  
% 1.51/1.00  ------ QBF Options
% 1.51/1.00  
% 1.51/1.00  --qbf_mode                              false
% 1.51/1.00  --qbf_elim_univ                         false
% 1.51/1.00  --qbf_dom_inst                          none
% 1.51/1.00  --qbf_dom_pre_inst                      false
% 1.51/1.00  --qbf_sk_in                             false
% 1.51/1.00  --qbf_pred_elim                         true
% 1.51/1.00  --qbf_split                             512
% 1.51/1.00  
% 1.51/1.00  ------ BMC1 Options
% 1.51/1.00  
% 1.51/1.00  --bmc1_incremental                      false
% 1.51/1.00  --bmc1_axioms                           reachable_all
% 1.51/1.00  --bmc1_min_bound                        0
% 1.51/1.00  --bmc1_max_bound                        -1
% 1.51/1.00  --bmc1_max_bound_default                -1
% 1.51/1.00  --bmc1_symbol_reachability              true
% 1.51/1.00  --bmc1_property_lemmas                  false
% 1.51/1.00  --bmc1_k_induction                      false
% 1.51/1.00  --bmc1_non_equiv_states                 false
% 1.51/1.00  --bmc1_deadlock                         false
% 1.51/1.00  --bmc1_ucm                              false
% 1.51/1.00  --bmc1_add_unsat_core                   none
% 1.51/1.00  --bmc1_unsat_core_children              false
% 1.51/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.51/1.00  --bmc1_out_stat                         full
% 1.51/1.00  --bmc1_ground_init                      false
% 1.51/1.00  --bmc1_pre_inst_next_state              false
% 1.51/1.00  --bmc1_pre_inst_state                   false
% 1.51/1.00  --bmc1_pre_inst_reach_state             false
% 1.51/1.00  --bmc1_out_unsat_core                   false
% 1.51/1.00  --bmc1_aig_witness_out                  false
% 1.51/1.00  --bmc1_verbose                          false
% 1.51/1.00  --bmc1_dump_clauses_tptp                false
% 1.51/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.51/1.00  --bmc1_dump_file                        -
% 1.51/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.51/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.51/1.00  --bmc1_ucm_extend_mode                  1
% 1.51/1.00  --bmc1_ucm_init_mode                    2
% 1.51/1.00  --bmc1_ucm_cone_mode                    none
% 1.51/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.51/1.00  --bmc1_ucm_relax_model                  4
% 1.51/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.51/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.51/1.00  --bmc1_ucm_layered_model                none
% 1.51/1.00  --bmc1_ucm_max_lemma_size               10
% 1.51/1.00  
% 1.51/1.00  ------ AIG Options
% 1.51/1.00  
% 1.51/1.00  --aig_mode                              false
% 1.51/1.00  
% 1.51/1.00  ------ Instantiation Options
% 1.51/1.00  
% 1.51/1.00  --instantiation_flag                    true
% 1.51/1.00  --inst_sos_flag                         false
% 1.51/1.00  --inst_sos_phase                        true
% 1.51/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.51/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.51/1.00  --inst_lit_sel_side                     none
% 1.51/1.00  --inst_solver_per_active                1400
% 1.51/1.00  --inst_solver_calls_frac                1.
% 1.51/1.00  --inst_passive_queue_type               priority_queues
% 1.51/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.51/1.00  --inst_passive_queues_freq              [25;2]
% 1.51/1.00  --inst_dismatching                      true
% 1.51/1.00  --inst_eager_unprocessed_to_passive     true
% 1.51/1.00  --inst_prop_sim_given                   true
% 1.51/1.00  --inst_prop_sim_new                     false
% 1.51/1.00  --inst_subs_new                         false
% 1.51/1.00  --inst_eq_res_simp                      false
% 1.51/1.00  --inst_subs_given                       false
% 1.51/1.00  --inst_orphan_elimination               true
% 1.51/1.00  --inst_learning_loop_flag               true
% 1.51/1.00  --inst_learning_start                   3000
% 1.51/1.00  --inst_learning_factor                  2
% 1.51/1.00  --inst_start_prop_sim_after_learn       3
% 1.51/1.00  --inst_sel_renew                        solver
% 1.51/1.00  --inst_lit_activity_flag                true
% 1.51/1.00  --inst_restr_to_given                   false
% 1.51/1.00  --inst_activity_threshold               500
% 1.51/1.00  --inst_out_proof                        true
% 1.51/1.00  
% 1.51/1.00  ------ Resolution Options
% 1.51/1.00  
% 1.51/1.00  --resolution_flag                       false
% 1.51/1.00  --res_lit_sel                           adaptive
% 1.51/1.00  --res_lit_sel_side                      none
% 1.51/1.00  --res_ordering                          kbo
% 1.51/1.00  --res_to_prop_solver                    active
% 1.51/1.00  --res_prop_simpl_new                    false
% 1.51/1.00  --res_prop_simpl_given                  true
% 1.51/1.00  --res_passive_queue_type                priority_queues
% 1.51/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.51/1.00  --res_passive_queues_freq               [15;5]
% 1.51/1.00  --res_forward_subs                      full
% 1.51/1.00  --res_backward_subs                     full
% 1.51/1.00  --res_forward_subs_resolution           true
% 1.51/1.00  --res_backward_subs_resolution          true
% 1.51/1.00  --res_orphan_elimination                true
% 1.51/1.00  --res_time_limit                        2.
% 1.51/1.00  --res_out_proof                         true
% 1.51/1.00  
% 1.51/1.00  ------ Superposition Options
% 1.51/1.00  
% 1.51/1.00  --superposition_flag                    true
% 1.51/1.00  --sup_passive_queue_type                priority_queues
% 1.51/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.51/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.51/1.00  --demod_completeness_check              fast
% 1.51/1.00  --demod_use_ground                      true
% 1.51/1.00  --sup_to_prop_solver                    passive
% 1.51/1.00  --sup_prop_simpl_new                    true
% 1.51/1.00  --sup_prop_simpl_given                  true
% 1.51/1.00  --sup_fun_splitting                     false
% 1.51/1.00  --sup_smt_interval                      50000
% 1.51/1.00  
% 1.51/1.00  ------ Superposition Simplification Setup
% 1.51/1.00  
% 1.51/1.00  --sup_indices_passive                   []
% 1.51/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.51/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.51/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.00  --sup_full_bw                           [BwDemod]
% 1.51/1.00  --sup_immed_triv                        [TrivRules]
% 1.51/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.51/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.00  --sup_immed_bw_main                     []
% 1.51/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.51/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.51/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.51/1.00  
% 1.51/1.00  ------ Combination Options
% 1.51/1.00  
% 1.51/1.00  --comb_res_mult                         3
% 1.51/1.00  --comb_sup_mult                         2
% 1.51/1.00  --comb_inst_mult                        10
% 1.51/1.00  
% 1.51/1.00  ------ Debug Options
% 1.51/1.00  
% 1.51/1.00  --dbg_backtrace                         false
% 1.51/1.00  --dbg_dump_prop_clauses                 false
% 1.51/1.00  --dbg_dump_prop_clauses_file            -
% 1.51/1.00  --dbg_out_stat                          false
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  ------ Proving...
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  % SZS status Theorem for theBenchmark.p
% 1.51/1.00  
% 1.51/1.00   Resolution empty clause
% 1.51/1.00  
% 1.51/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.51/1.00  
% 1.51/1.00  fof(f9,conjecture,(
% 1.51/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f10,negated_conjecture,(
% 1.51/1.00    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.51/1.00    inference(negated_conjecture,[],[f9])).
% 1.51/1.00  
% 1.51/1.00  fof(f21,plain,(
% 1.51/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.51/1.00    inference(ennf_transformation,[],[f10])).
% 1.51/1.00  
% 1.51/1.00  fof(f22,plain,(
% 1.51/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.51/1.00    inference(flattening,[],[f21])).
% 1.51/1.00  
% 1.51/1.00  fof(f26,plain,(
% 1.51/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 1.51/1.00    introduced(choice_axiom,[])).
% 1.51/1.00  
% 1.51/1.00  fof(f25,plain,(
% 1.51/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 1.51/1.00    introduced(choice_axiom,[])).
% 1.51/1.00  
% 1.51/1.00  fof(f24,plain,(
% 1.51/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 1.51/1.00    introduced(choice_axiom,[])).
% 1.51/1.00  
% 1.51/1.00  fof(f23,plain,(
% 1.51/1.00    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 1.51/1.00    introduced(choice_axiom,[])).
% 1.51/1.00  
% 1.51/1.00  fof(f27,plain,(
% 1.51/1.00    (((k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 1.51/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f22,f26,f25,f24,f23])).
% 1.51/1.00  
% 1.51/1.00  fof(f43,plain,(
% 1.51/1.00    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f6,axiom,(
% 1.51/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f15,plain,(
% 1.51/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.51/1.00    inference(ennf_transformation,[],[f6])).
% 1.51/1.00  
% 1.51/1.00  fof(f16,plain,(
% 1.51/1.00    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.51/1.00    inference(flattening,[],[f15])).
% 1.51/1.00  
% 1.51/1.00  fof(f33,plain,(
% 1.51/1.00    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.51/1.00    inference(cnf_transformation,[],[f16])).
% 1.51/1.00  
% 1.51/1.00  fof(f38,plain,(
% 1.51/1.00    v1_funct_2(sK3,sK1,sK2)),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f37,plain,(
% 1.51/1.00    v1_funct_1(sK3)),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f39,plain,(
% 1.51/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f1,axiom,(
% 1.51/1.00    v1_xboole_0(k1_xboole_0)),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f28,plain,(
% 1.51/1.00    v1_xboole_0(k1_xboole_0)),
% 1.51/1.00    inference(cnf_transformation,[],[f1])).
% 1.51/1.00  
% 1.51/1.00  fof(f36,plain,(
% 1.51/1.00    ~v1_xboole_0(sK2)),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f41,plain,(
% 1.51/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f7,axiom,(
% 1.51/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f17,plain,(
% 1.51/1.00    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.51/1.00    inference(ennf_transformation,[],[f7])).
% 1.51/1.00  
% 1.51/1.00  fof(f18,plain,(
% 1.51/1.00    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.51/1.00    inference(flattening,[],[f17])).
% 1.51/1.00  
% 1.51/1.00  fof(f34,plain,(
% 1.51/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.51/1.00    inference(cnf_transformation,[],[f18])).
% 1.51/1.00  
% 1.51/1.00  fof(f40,plain,(
% 1.51/1.00    v1_funct_1(sK4)),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f45,plain,(
% 1.51/1.00    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f42,plain,(
% 1.51/1.00    m1_subset_1(sK5,sK1)),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  fof(f3,axiom,(
% 1.51/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f12,plain,(
% 1.51/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.51/1.00    inference(ennf_transformation,[],[f3])).
% 1.51/1.00  
% 1.51/1.00  fof(f13,plain,(
% 1.51/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.51/1.00    inference(flattening,[],[f12])).
% 1.51/1.00  
% 1.51/1.00  fof(f30,plain,(
% 1.51/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.51/1.00    inference(cnf_transformation,[],[f13])).
% 1.51/1.00  
% 1.51/1.00  fof(f8,axiom,(
% 1.51/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1))))),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f19,plain,(
% 1.51/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.51/1.00    inference(ennf_transformation,[],[f8])).
% 1.51/1.00  
% 1.51/1.00  fof(f20,plain,(
% 1.51/1.00    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.51/1.00    inference(flattening,[],[f19])).
% 1.51/1.00  
% 1.51/1.00  fof(f35,plain,(
% 1.51/1.00    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.51/1.00    inference(cnf_transformation,[],[f20])).
% 1.51/1.00  
% 1.51/1.00  fof(f4,axiom,(
% 1.51/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f14,plain,(
% 1.51/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.51/1.00    inference(ennf_transformation,[],[f4])).
% 1.51/1.00  
% 1.51/1.00  fof(f31,plain,(
% 1.51/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.51/1.00    inference(cnf_transformation,[],[f14])).
% 1.51/1.00  
% 1.51/1.00  fof(f5,axiom,(
% 1.51/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f32,plain,(
% 1.51/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.51/1.00    inference(cnf_transformation,[],[f5])).
% 1.51/1.00  
% 1.51/1.00  fof(f2,axiom,(
% 1.51/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.51/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.51/1.00  
% 1.51/1.00  fof(f11,plain,(
% 1.51/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.51/1.00    inference(ennf_transformation,[],[f2])).
% 1.51/1.00  
% 1.51/1.00  fof(f29,plain,(
% 1.51/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.51/1.00    inference(cnf_transformation,[],[f11])).
% 1.51/1.00  
% 1.51/1.00  fof(f44,plain,(
% 1.51/1.00    k1_xboole_0 != sK1),
% 1.51/1.00    inference(cnf_transformation,[],[f27])).
% 1.51/1.00  
% 1.51/1.00  cnf(c_10,negated_conjecture,
% 1.51/1.00      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 1.51/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_5,plain,
% 1.51/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.51/1.00      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 1.51/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/1.00      | ~ v1_funct_1(X4)
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
% 1.51/1.00      | k1_xboole_0 = X2 ),
% 1.51/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_15,negated_conjecture,
% 1.51/1.00      ( v1_funct_2(sK3,sK1,sK2) ),
% 1.51/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_321,plain,
% 1.51/1.00      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 1.51/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.51/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.51/1.00      | ~ v1_funct_1(X4)
% 1.51/1.00      | ~ v1_funct_1(X2)
% 1.51/1.00      | k1_partfun1(X0,X1,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,X4)
% 1.51/1.00      | sK2 != X1
% 1.51/1.00      | sK1 != X0
% 1.51/1.00      | sK3 != X2
% 1.51/1.00      | k1_xboole_0 = X1 ),
% 1.51/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_322,plain,
% 1.51/1.00      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.51/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.51/1.00      | ~ v1_funct_1(X1)
% 1.51/1.00      | ~ v1_funct_1(sK3)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.51/1.00      | k1_xboole_0 = sK2 ),
% 1.51/1.00      inference(unflattening,[status(thm)],[c_321]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_16,negated_conjecture,
% 1.51/1.00      ( v1_funct_1(sK3) ),
% 1.51/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_14,negated_conjecture,
% 1.51/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.51/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_326,plain,
% 1.51/1.00      ( ~ v1_funct_1(X1)
% 1.51/1.00      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.51/1.00      | k1_xboole_0 = sK2 ),
% 1.51/1.00      inference(global_propositional_subsumption,
% 1.51/1.00                [status(thm)],
% 1.51/1.00                [c_322,c_16,c_14]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_327,plain,
% 1.51/1.00      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.51/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.51/1.00      | ~ v1_funct_1(X1)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.51/1.00      | k1_xboole_0 = sK2 ),
% 1.51/1.00      inference(renaming,[status(thm)],[c_326]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_360,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
% 1.51/1.00      | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4)
% 1.51/1.00      | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
% 1.51/1.00      | sK2 = k1_xboole_0 ),
% 1.51/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_327]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_0,plain,
% 1.51/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.51/1.00      inference(cnf_transformation,[],[f28]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_17,negated_conjecture,
% 1.51/1.00      ( ~ v1_xboole_0(sK2) ),
% 1.51/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_174,plain,
% 1.51/1.00      ( sK2 != k1_xboole_0 ),
% 1.51/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_364,plain,
% 1.51/1.00      ( k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3)
% 1.51/1.00      | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) ),
% 1.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_360,c_174]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_365,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
% 1.51/1.00      | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4)
% 1.51/1.00      | k2_relset_1(sK1,sK2,sK3) != k2_relset_1(sK1,sK2,sK3) ),
% 1.51/1.00      inference(renaming,[status(thm)],[c_364]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_499,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) = k8_funct_2(sK1,sK2,X1,sK3,X0)
% 1.51/1.00      | k1_relset_1(sK2,X1,X0) != k1_relset_1(sK2,sK0,sK4) ),
% 1.51/1.00      inference(equality_resolution_simp,[status(thm)],[c_365]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_635,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51)))
% 1.51/1.00      | ~ v1_funct_1(X0_50)
% 1.51/1.00      | k1_relset_1(sK2,X0_51,X0_50) != k1_relset_1(sK2,sK0,sK4)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_499]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_937,plain,
% 1.51/1.00      ( k1_relset_1(sK2,X0_51,X0_50) != k1_relset_1(sK2,sK0,sK4)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
% 1.51/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 1.51/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1713,plain,
% 1.51/1.00      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
% 1.51/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 1.51/1.00      | v1_funct_1(sK4) != iProver_top ),
% 1.51/1.00      inference(equality_resolution,[status(thm)],[c_937]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_12,negated_conjecture,
% 1.51/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 1.51/1.00      inference(cnf_transformation,[],[f41]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_641,negated_conjecture,
% 1.51/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_931,plain,
% 1.51/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_639,negated_conjecture,
% 1.51/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_933,plain,
% 1.51/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_6,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.51/1.00      | ~ v1_funct_1(X3)
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.51/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_645,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 1.51/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 1.51/1.00      | ~ v1_funct_1(X0_50)
% 1.51/1.00      | ~ v1_funct_1(X1_50)
% 1.51/1.00      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_929,plain,
% 1.51/1.00      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 1.51/1.00      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 1.51/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.51/1.00      | v1_funct_1(X0_50) != iProver_top
% 1.51/1.00      | v1_funct_1(X1_50) != iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1289,plain,
% 1.51/1.00      ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
% 1.51/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.51/1.00      | v1_funct_1(X0_50) != iProver_top
% 1.51/1.00      | v1_funct_1(sK3) != iProver_top ),
% 1.51/1.00      inference(superposition,[status(thm)],[c_933,c_929]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_19,plain,
% 1.51/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1484,plain,
% 1.51/1.00      ( v1_funct_1(X0_50) != iProver_top
% 1.51/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.51/1.00      | k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50) ),
% 1.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1289,c_19]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1485,plain,
% 1.51/1.00      ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
% 1.51/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.51/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 1.51/1.00      inference(renaming,[status(thm)],[c_1484]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1491,plain,
% 1.51/1.00      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 1.51/1.00      | v1_funct_1(sK4) != iProver_top ),
% 1.51/1.00      inference(superposition,[status(thm)],[c_931,c_1485]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_13,negated_conjecture,
% 1.51/1.00      ( v1_funct_1(sK4) ),
% 1.51/1.00      inference(cnf_transformation,[],[f40]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1078,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 1.51/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.51/1.00      | ~ v1_funct_1(X0_50)
% 1.51/1.00      | ~ v1_funct_1(sK4)
% 1.51/1.00      | k1_partfun1(X0_51,X1_51,sK2,sK0,X0_50,sK4) = k5_relat_1(X0_50,sK4) ),
% 1.51/1.00      inference(instantiation,[status(thm)],[c_645]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1139,plain,
% 1.51/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.51/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.51/1.00      | ~ v1_funct_1(sK3)
% 1.51/1.00      | ~ v1_funct_1(sK4)
% 1.51/1.00      | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.51/1.00      inference(instantiation,[status(thm)],[c_1078]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1504,plain,
% 1.51/1.00      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.51/1.00      inference(global_propositional_subsumption,
% 1.51/1.00                [status(thm)],
% 1.51/1.00                [c_1491,c_16,c_14,c_13,c_12,c_1139]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1714,plain,
% 1.51/1.00      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 1.51/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 1.51/1.00      | v1_funct_1(sK4) != iProver_top ),
% 1.51/1.00      inference(light_normalisation,[status(thm)],[c_1713,c_1504]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_22,plain,
% 1.51/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_23,plain,
% 1.51/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1717,plain,
% 1.51/1.00      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.51/1.00      inference(global_propositional_subsumption,
% 1.51/1.00                [status(thm)],
% 1.51/1.00                [c_1714,c_22,c_23]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_8,negated_conjecture,
% 1.51/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 1.51/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_644,negated_conjecture,
% 1.51/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1720,plain,
% 1.51/1.00      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.51/1.00      inference(demodulation,[status(thm)],[c_1717,c_644]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_640,negated_conjecture,
% 1.51/1.00      ( v1_funct_1(sK4) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_932,plain,
% 1.51/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_11,negated_conjecture,
% 1.51/1.00      ( m1_subset_1(sK5,sK1) ),
% 1.51/1.00      inference(cnf_transformation,[],[f42]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_642,negated_conjecture,
% 1.51/1.00      ( m1_subset_1(sK5,sK1) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_930,plain,
% 1.51/1.00      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_2,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.51/1.00      inference(cnf_transformation,[],[f30]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_7,plain,
% 1.51/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.51/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/1.00      | ~ r2_hidden(X3,X1)
% 1.51/1.00      | ~ v1_funct_1(X4)
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | ~ v1_relat_1(X4)
% 1.51/1.00      | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 1.51/1.00      | k1_xboole_0 = X2 ),
% 1.51/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_294,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.51/1.00      | ~ r2_hidden(X3,X1)
% 1.51/1.00      | ~ v1_funct_1(X4)
% 1.51/1.00      | ~ v1_funct_1(X0)
% 1.51/1.00      | ~ v1_relat_1(X4)
% 1.51/1.00      | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
% 1.51/1.00      | sK2 != X2
% 1.51/1.00      | sK1 != X1
% 1.51/1.00      | sK3 != X0
% 1.51/1.00      | k1_xboole_0 = X2 ),
% 1.51/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_295,plain,
% 1.51/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.51/1.00      | ~ r2_hidden(X0,sK1)
% 1.51/1.00      | ~ v1_funct_1(X1)
% 1.51/1.00      | ~ v1_funct_1(sK3)
% 1.51/1.00      | ~ v1_relat_1(X1)
% 1.51/1.00      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.51/1.00      | k1_xboole_0 = sK2 ),
% 1.51/1.00      inference(unflattening,[status(thm)],[c_294]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_299,plain,
% 1.51/1.00      ( ~ v1_funct_1(X1)
% 1.51/1.00      | ~ r2_hidden(X0,sK1)
% 1.51/1.00      | ~ v1_relat_1(X1)
% 1.51/1.00      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.51/1.00      | k1_xboole_0 = sK2 ),
% 1.51/1.00      inference(global_propositional_subsumption,
% 1.51/1.00                [status(thm)],
% 1.51/1.00                [c_295,c_16,c_14]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_300,plain,
% 1.51/1.00      ( ~ r2_hidden(X0,sK1)
% 1.51/1.00      | ~ v1_funct_1(X1)
% 1.51/1.00      | ~ v1_relat_1(X1)
% 1.51/1.00      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.51/1.00      | k1_xboole_0 = sK2 ),
% 1.51/1.00      inference(renaming,[status(thm)],[c_299]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_392,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,X1)
% 1.51/1.00      | ~ v1_funct_1(X2)
% 1.51/1.00      | ~ v1_relat_1(X2)
% 1.51/1.00      | v1_xboole_0(X1)
% 1.51/1.00      | X3 != X0
% 1.51/1.00      | k1_funct_1(k5_relat_1(sK3,X2),X3) = k1_funct_1(X2,k1_funct_1(sK3,X3))
% 1.51/1.00      | sK2 = k1_xboole_0
% 1.51/1.00      | sK1 != X1 ),
% 1.51/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_300]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_393,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,sK1)
% 1.51/1.00      | ~ v1_funct_1(X1)
% 1.51/1.00      | ~ v1_relat_1(X1)
% 1.51/1.00      | v1_xboole_0(sK1)
% 1.51/1.00      | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
% 1.51/1.00      | sK2 = k1_xboole_0 ),
% 1.51/1.00      inference(unflattening,[status(thm)],[c_392]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_397,plain,
% 1.51/1.00      ( k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
% 1.51/1.00      | v1_xboole_0(sK1)
% 1.51/1.00      | ~ v1_relat_1(X1)
% 1.51/1.00      | ~ v1_funct_1(X1)
% 1.51/1.00      | ~ m1_subset_1(X0,sK1) ),
% 1.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_393,c_174]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_398,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,sK1)
% 1.51/1.00      | ~ v1_funct_1(X1)
% 1.51/1.00      | ~ v1_relat_1(X1)
% 1.51/1.00      | v1_xboole_0(sK1)
% 1.51/1.00      | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0)) ),
% 1.51/1.00      inference(renaming,[status(thm)],[c_397]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_636,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0_50,sK1)
% 1.51/1.00      | ~ v1_funct_1(X1_50)
% 1.51/1.00      | ~ v1_relat_1(X1_50)
% 1.51/1.00      | v1_xboole_0(sK1)
% 1.51/1.00      | k1_funct_1(k5_relat_1(sK3,X1_50),X0_50) = k1_funct_1(X1_50,k1_funct_1(sK3,X0_50)) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_398]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_936,plain,
% 1.51/1.00      ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
% 1.51/1.00      | m1_subset_1(X1_50,sK1) != iProver_top
% 1.51/1.00      | v1_funct_1(X0_50) != iProver_top
% 1.51/1.00      | v1_relat_1(X0_50) != iProver_top
% 1.51/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1530,plain,
% 1.51/1.00      ( k1_funct_1(X0_50,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,X0_50),sK5)
% 1.51/1.00      | v1_funct_1(X0_50) != iProver_top
% 1.51/1.00      | v1_relat_1(X0_50) != iProver_top
% 1.51/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 1.51/1.00      inference(superposition,[status(thm)],[c_930,c_936]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1576,plain,
% 1.51/1.00      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 1.51/1.00      | v1_relat_1(sK4) != iProver_top
% 1.51/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 1.51/1.00      inference(superposition,[status(thm)],[c_932,c_1530]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_3,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.51/1.00      inference(cnf_transformation,[],[f31]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_647,plain,
% 1.51/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 1.51/1.00      | ~ v1_relat_1(X1_50)
% 1.51/1.00      | v1_relat_1(X0_50) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_927,plain,
% 1.51/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 1.51/1.00      | v1_relat_1(X1_50) != iProver_top
% 1.51/1.00      | v1_relat_1(X0_50) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_647]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1233,plain,
% 1.51/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 1.51/1.00      | v1_relat_1(sK4) = iProver_top ),
% 1.51/1.00      inference(superposition,[status(thm)],[c_931,c_927]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_4,plain,
% 1.51/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.51/1.00      inference(cnf_transformation,[],[f32]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_646,plain,
% 1.51/1.00      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_928,plain,
% 1.51/1.00      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) = iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_646]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1315,plain,
% 1.51/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 1.51/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1233,c_928]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1593,plain,
% 1.51/1.00      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 1.51/1.00      | v1_xboole_0(sK1) = iProver_top ),
% 1.51/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1576,c_1315]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1,plain,
% 1.51/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.51/1.00      inference(cnf_transformation,[],[f29]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_648,plain,
% 1.51/1.00      ( ~ v1_xboole_0(X0_51) | k1_xboole_0 = X0_51 ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_926,plain,
% 1.51/1.00      ( k1_xboole_0 = X0_51 | v1_xboole_0(X0_51) != iProver_top ),
% 1.51/1.00      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1599,plain,
% 1.51/1.00      ( sK1 = k1_xboole_0
% 1.51/1.00      | k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.51/1.00      inference(superposition,[status(thm)],[c_1593,c_926]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_9,negated_conjecture,
% 1.51/1.00      ( k1_xboole_0 != sK1 ),
% 1.51/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_643,negated_conjecture,
% 1.51/1.00      ( k1_xboole_0 != sK1 ),
% 1.51/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1316,plain,
% 1.51/1.00      ( v1_relat_1(sK4) ),
% 1.51/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1315]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1590,plain,
% 1.51/1.00      ( ~ v1_relat_1(sK4)
% 1.51/1.00      | v1_xboole_0(sK1)
% 1.51/1.00      | k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.51/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1576]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1611,plain,
% 1.51/1.00      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 1.51/1.00      inference(instantiation,[status(thm)],[c_648]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1653,plain,
% 1.51/1.00      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.51/1.00      inference(global_propositional_subsumption,
% 1.51/1.00                [status(thm)],
% 1.51/1.00                [c_1599,c_643,c_1316,c_1590,c_1611]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1721,plain,
% 1.51/1.00      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.51/1.00      inference(light_normalisation,[status(thm)],[c_1720,c_1653]) ).
% 1.51/1.00  
% 1.51/1.00  cnf(c_1722,plain,
% 1.51/1.00      ( $false ),
% 1.51/1.00      inference(equality_resolution_simp,[status(thm)],[c_1721]) ).
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.51/1.00  
% 1.51/1.00  ------                               Statistics
% 1.51/1.00  
% 1.51/1.00  ------ General
% 1.51/1.00  
% 1.51/1.00  abstr_ref_over_cycles:                  0
% 1.51/1.00  abstr_ref_under_cycles:                 0
% 1.51/1.00  gc_basic_clause_elim:                   0
% 1.51/1.00  forced_gc_time:                         0
% 1.51/1.00  parsing_time:                           0.011
% 1.51/1.00  unif_index_cands_time:                  0.
% 1.51/1.00  unif_index_add_time:                    0.
% 1.51/1.00  orderings_time:                         0.
% 1.51/1.00  out_proof_time:                         0.014
% 1.51/1.00  total_time:                             0.093
% 1.51/1.00  num_of_symbols:                         56
% 1.51/1.00  num_of_terms:                           1657
% 1.51/1.00  
% 1.51/1.00  ------ Preprocessing
% 1.51/1.00  
% 1.51/1.00  num_of_splits:                          0
% 1.51/1.00  num_of_split_atoms:                     0
% 1.51/1.00  num_of_reused_defs:                     0
% 1.51/1.00  num_eq_ax_congr_red:                    16
% 1.51/1.00  num_of_sem_filtered_clauses:            1
% 1.51/1.00  num_of_subtypes:                        3
% 1.51/1.00  monotx_restored_types:                  0
% 1.51/1.00  sat_num_of_epr_types:                   0
% 1.51/1.00  sat_num_of_non_cyclic_types:            0
% 1.51/1.00  sat_guarded_non_collapsed_types:        1
% 1.51/1.00  num_pure_diseq_elim:                    0
% 1.51/1.00  simp_replaced_by:                       0
% 1.51/1.00  res_preprocessed:                       98
% 1.51/1.00  prep_upred:                             0
% 1.51/1.00  prep_unflattend:                        17
% 1.51/1.00  smt_new_axioms:                         0
% 1.51/1.00  pred_elim_cands:                        4
% 1.51/1.00  pred_elim:                              3
% 1.51/1.00  pred_elim_cl:                           3
% 1.51/1.00  pred_elim_cycles:                       8
% 1.51/1.00  merged_defs:                            0
% 1.51/1.00  merged_defs_ncl:                        0
% 1.51/1.00  bin_hyper_res:                          0
% 1.51/1.00  prep_cycles:                            4
% 1.51/1.00  pred_elim_time:                         0.008
% 1.51/1.00  splitting_time:                         0.
% 1.51/1.00  sem_filter_time:                        0.
% 1.51/1.00  monotx_time:                            0.
% 1.51/1.00  subtype_inf_time:                       0.
% 1.51/1.00  
% 1.51/1.00  ------ Problem properties
% 1.51/1.00  
% 1.51/1.00  clauses:                                15
% 1.51/1.00  conjectures:                            8
% 1.51/1.00  epr:                                    7
% 1.51/1.00  horn:                                   14
% 1.51/1.00  ground:                                 9
% 1.51/1.00  unary:                                  10
% 1.51/1.00  binary:                                 1
% 1.51/1.00  lits:                                   29
% 1.51/1.00  lits_eq:                                7
% 1.51/1.00  fd_pure:                                0
% 1.51/1.00  fd_pseudo:                              0
% 1.51/1.00  fd_cond:                                1
% 1.51/1.00  fd_pseudo_cond:                         0
% 1.51/1.00  ac_symbols:                             0
% 1.51/1.00  
% 1.51/1.00  ------ Propositional Solver
% 1.51/1.00  
% 1.51/1.00  prop_solver_calls:                      27
% 1.51/1.00  prop_fast_solver_calls:                 639
% 1.51/1.00  smt_solver_calls:                       0
% 1.51/1.00  smt_fast_solver_calls:                  0
% 1.51/1.00  prop_num_of_clauses:                    462
% 1.51/1.00  prop_preprocess_simplified:             2432
% 1.51/1.00  prop_fo_subsumed:                       21
% 1.51/1.00  prop_solver_time:                       0.
% 1.51/1.00  smt_solver_time:                        0.
% 1.51/1.00  smt_fast_solver_time:                   0.
% 1.51/1.00  prop_fast_solver_time:                  0.
% 1.51/1.00  prop_unsat_core_time:                   0.
% 1.51/1.00  
% 1.51/1.00  ------ QBF
% 1.51/1.00  
% 1.51/1.00  qbf_q_res:                              0
% 1.51/1.00  qbf_num_tautologies:                    0
% 1.51/1.00  qbf_prep_cycles:                        0
% 1.51/1.00  
% 1.51/1.00  ------ BMC1
% 1.51/1.00  
% 1.51/1.00  bmc1_current_bound:                     -1
% 1.51/1.00  bmc1_last_solved_bound:                 -1
% 1.51/1.00  bmc1_unsat_core_size:                   -1
% 1.51/1.00  bmc1_unsat_core_parents_size:           -1
% 1.51/1.00  bmc1_merge_next_fun:                    0
% 1.51/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.51/1.00  
% 1.51/1.00  ------ Instantiation
% 1.51/1.00  
% 1.51/1.00  inst_num_of_clauses:                    153
% 1.51/1.00  inst_num_in_passive:                    2
% 1.51/1.00  inst_num_in_active:                     131
% 1.51/1.00  inst_num_in_unprocessed:                20
% 1.51/1.00  inst_num_of_loops:                      140
% 1.51/1.00  inst_num_of_learning_restarts:          0
% 1.51/1.00  inst_num_moves_active_passive:          5
% 1.51/1.00  inst_lit_activity:                      0
% 1.51/1.00  inst_lit_activity_moves:                0
% 1.51/1.00  inst_num_tautologies:                   0
% 1.51/1.00  inst_num_prop_implied:                  0
% 1.51/1.00  inst_num_existing_simplified:           0
% 1.51/1.00  inst_num_eq_res_simplified:             0
% 1.51/1.00  inst_num_child_elim:                    0
% 1.51/1.00  inst_num_of_dismatching_blockings:      23
% 1.51/1.00  inst_num_of_non_proper_insts:           150
% 1.51/1.00  inst_num_of_duplicates:                 0
% 1.51/1.00  inst_inst_num_from_inst_to_res:         0
% 1.51/1.00  inst_dismatching_checking_time:         0.
% 1.51/1.00  
% 1.51/1.00  ------ Resolution
% 1.51/1.00  
% 1.51/1.00  res_num_of_clauses:                     0
% 1.51/1.00  res_num_in_passive:                     0
% 1.51/1.00  res_num_in_active:                      0
% 1.51/1.00  res_num_of_loops:                       102
% 1.51/1.00  res_forward_subset_subsumed:            34
% 1.51/1.00  res_backward_subset_subsumed:           2
% 1.51/1.00  res_forward_subsumed:                   0
% 1.51/1.00  res_backward_subsumed:                  0
% 1.51/1.00  res_forward_subsumption_resolution:     0
% 1.51/1.00  res_backward_subsumption_resolution:    0
% 1.51/1.00  res_clause_to_clause_subsumption:       49
% 1.51/1.00  res_orphan_elimination:                 0
% 1.51/1.00  res_tautology_del:                      31
% 1.51/1.00  res_num_eq_res_simplified:              1
% 1.51/1.00  res_num_sel_changes:                    0
% 1.51/1.00  res_moves_from_active_to_pass:          0
% 1.51/1.00  
% 1.51/1.00  ------ Superposition
% 1.51/1.00  
% 1.51/1.00  sup_time_total:                         0.
% 1.51/1.00  sup_time_generating:                    0.
% 1.51/1.00  sup_time_sim_full:                      0.
% 1.51/1.00  sup_time_sim_immed:                     0.
% 1.51/1.00  
% 1.51/1.00  sup_num_of_clauses:                     27
% 1.51/1.00  sup_num_in_active:                      25
% 1.51/1.00  sup_num_in_passive:                     2
% 1.51/1.00  sup_num_of_loops:                       27
% 1.51/1.00  sup_fw_superposition:                   12
% 1.51/1.00  sup_bw_superposition:                   1
% 1.51/1.00  sup_immediate_simplified:               1
% 1.51/1.00  sup_given_eliminated:                   0
% 1.51/1.00  comparisons_done:                       0
% 1.51/1.00  comparisons_avoided:                    0
% 1.51/1.00  
% 1.51/1.00  ------ Simplifications
% 1.51/1.00  
% 1.51/1.00  
% 1.51/1.00  sim_fw_subset_subsumed:                 0
% 1.51/1.00  sim_bw_subset_subsumed:                 1
% 1.51/1.00  sim_fw_subsumed:                        0
% 1.51/1.00  sim_bw_subsumed:                        0
% 1.51/1.00  sim_fw_subsumption_res:                 1
% 1.51/1.00  sim_bw_subsumption_res:                 0
% 1.51/1.00  sim_tautology_del:                      0
% 1.51/1.00  sim_eq_tautology_del:                   1
% 1.51/1.00  sim_eq_res_simp:                        0
% 1.51/1.00  sim_fw_demodulated:                     0
% 1.51/1.00  sim_bw_demodulated:                     1
% 1.51/1.00  sim_light_normalised:                   2
% 1.51/1.00  sim_joinable_taut:                      0
% 1.51/1.00  sim_joinable_simp:                      0
% 1.51/1.00  sim_ac_normalised:                      0
% 1.51/1.00  sim_smt_subsumption:                    0
% 1.51/1.00  
%------------------------------------------------------------------------------
