%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:40 EST 2020

% Result     : Theorem 1.34s
% Output     : CNFRefutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 426 expanded)
%              Number of clauses        :   81 ( 126 expanded)
%              Number of leaves         :   17 ( 153 expanded)
%              Depth                    :   17
%              Number of atoms          :  503 (3464 expanded)
%              Number of equality atoms :  177 ( 902 expanded)
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
    inference(ennf_transformation,[],[f10])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f26,f25,f24,f23])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
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

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f36,plain,(
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
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f8])).

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

fof(f38,plain,(
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

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_529,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_902,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_531,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_900,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X5_52)))
    | ~ v1_funct_1(X3_52)
    | ~ v1_funct_1(X0_52)
    | k1_partfun1(X4_52,X5_52,X1_52,X2_52,X3_52,X0_52) = k5_relat_1(X3_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_897,plain,
    ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X4_52,X5_52) = k5_relat_1(X4_52,X5_52)
    | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
    | m1_subset_1(X4_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X5_52) != iProver_top
    | v1_funct_1(X4_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1595,plain,
    ( k1_partfun1(X0_52,X1_52,sK2,sK0,X2_52,sK4) = k5_relat_1(X2_52,sK4)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_897])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_25,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1762,plain,
    ( v1_funct_1(X2_52) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | k1_partfun1(X0_52,X1_52,sK2,sK0,X2_52,sK4) = k5_relat_1(X2_52,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1595,c_25])).

cnf(c_1763,plain,
    ( k1_partfun1(X0_52,X1_52,sK2,sK0,X2_52,sK4) = k5_relat_1(X2_52,sK4)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_1762])).

cnf(c_1772,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_1763])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_533,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_898,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_316,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_317,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_321,plain,
    ( ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_19,c_17])).

cnf(c_322,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ v1_funct_1(X1)
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_321])).

cnf(c_525,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52)))
    | ~ v1_funct_1(X1_52)
    | k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_907,plain,
    ( k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
    | k1_xboole_0 = sK2
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_548,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_579,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_600,plain,
    ( k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
    | k1_xboole_0 = sK2
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_550,plain,
    ( ~ v1_xboole_0(X0_52)
    | v1_xboole_0(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1070,plain,
    ( v1_xboole_0(X0_52)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_52 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_1072,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_549,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1328,plain,
    ( X0_52 != X1_52
    | X0_52 = k1_xboole_0
    | k1_xboole_0 != X1_52 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_1329,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1328])).

cnf(c_1465,plain,
    ( k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_907,c_20,c_0,c_579,c_600,c_1072,c_1329])).

cnf(c_1475,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_1465])).

cnf(c_26,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1478,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1475,c_25,c_26])).

cnf(c_1784,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1772,c_1478])).

cnf(c_562,plain,
    ( X0_52 != X1_52
    | X2_52 != X3_52
    | k1_funct_1(X0_52,X2_52) = k1_funct_1(X1_52,X3_52) ),
    theory(equality)).

cnf(c_1726,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) != k5_relat_1(sK3,sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_537,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1555,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1217,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != X0_52
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != X0_52 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_1549,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_243,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X5)
    | v1_xboole_0(X4)
    | X6 != X3
    | X1 != X4
    | k1_funct_1(X5,k1_funct_1(X0,X6)) = k1_funct_1(k5_relat_1(X0,X5),X6)
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_244,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X4)
    | ~ v1_relat_1(X4)
    | v1_xboole_0(X1)
    | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X4)
    | v1_xboole_0(X1)
    | k1_funct_1(X4,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X4),X0)
    | sK2 != X3
    | sK1 != X1
    | sK3 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_244,c_18])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(sK1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_291,plain,
    ( ~ v1_funct_1(X1)
    | ~ m1_subset_1(X0,sK1)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(sK1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_19,c_17])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(sK1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0_52,sK1)
    | ~ v1_funct_1(X1_52)
    | ~ v1_relat_1(X1_52)
    | v1_xboole_0(sK1)
    | k1_funct_1(X1_52,k1_funct_1(sK3,X0_52)) = k1_funct_1(k5_relat_1(sK3,X1_52),X0_52)
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_292])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0_52,sK1)
    | ~ v1_funct_1(X1_52)
    | ~ v1_relat_1(X1_52)
    | k1_funct_1(X1_52,k1_funct_1(sK3,X0_52)) = k1_funct_1(k5_relat_1(sK3,X1_52),X0_52)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_526])).

cnf(c_1538,plain,
    ( ~ m1_subset_1(X0_52,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,k1_funct_1(sK3,X0_52)) = k1_funct_1(k5_relat_1(sK3,sK4),X0_52) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1548,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ sP0_iProver_split
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_1459,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1045,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X1_52,X2_52)) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1331,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1149,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_1097,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != X0_52
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != X0_52
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_1148,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)
    | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_541,plain,
    ( ~ v1_xboole_0(X0_52)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1042,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_544,plain,
    ( v1_xboole_0(sK1)
    | sP0_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_526])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_534,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_11,negated_conjecture,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_535,negated_conjecture,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1784,c_1726,c_1555,c_1549,c_1548,c_1459,c_1331,c_1329,c_1149,c_1148,c_1072,c_1042,c_544,c_534,c_535,c_579,c_0,c_14,c_15,c_16,c_22,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n003.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 20:13:12 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 1.34/0.83  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.34/0.83  
% 1.34/0.83  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.34/0.83  
% 1.34/0.83  ------  iProver source info
% 1.34/0.83  
% 1.34/0.83  git: date: 2020-06-30 10:37:57 +0100
% 1.34/0.83  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.34/0.83  git: non_committed_changes: false
% 1.34/0.83  git: last_make_outside_of_git: false
% 1.34/0.83  
% 1.34/0.83  ------ 
% 1.34/0.83  
% 1.34/0.83  ------ Input Options
% 1.34/0.83  
% 1.34/0.83  --out_options                           all
% 1.34/0.83  --tptp_safe_out                         true
% 1.34/0.83  --problem_path                          ""
% 1.34/0.83  --include_path                          ""
% 1.34/0.83  --clausifier                            res/vclausify_rel
% 1.34/0.83  --clausifier_options                    --mode clausify
% 1.34/0.83  --stdin                                 false
% 1.34/0.83  --stats_out                             all
% 1.34/0.83  
% 1.34/0.83  ------ General Options
% 1.34/0.83  
% 1.34/0.83  --fof                                   false
% 1.34/0.83  --time_out_real                         305.
% 1.34/0.83  --time_out_virtual                      -1.
% 1.34/0.83  --symbol_type_check                     false
% 1.34/0.83  --clausify_out                          false
% 1.34/0.83  --sig_cnt_out                           false
% 1.34/0.83  --trig_cnt_out                          false
% 1.34/0.83  --trig_cnt_out_tolerance                1.
% 1.34/0.83  --trig_cnt_out_sk_spl                   false
% 1.34/0.83  --abstr_cl_out                          false
% 1.34/0.83  
% 1.34/0.83  ------ Global Options
% 1.34/0.83  
% 1.34/0.83  --schedule                              default
% 1.34/0.83  --add_important_lit                     false
% 1.34/0.83  --prop_solver_per_cl                    1000
% 1.34/0.83  --min_unsat_core                        false
% 1.34/0.83  --soft_assumptions                      false
% 1.34/0.83  --soft_lemma_size                       3
% 1.34/0.83  --prop_impl_unit_size                   0
% 1.34/0.83  --prop_impl_unit                        []
% 1.34/0.83  --share_sel_clauses                     true
% 1.34/0.83  --reset_solvers                         false
% 1.34/0.83  --bc_imp_inh                            [conj_cone]
% 1.34/0.83  --conj_cone_tolerance                   3.
% 1.34/0.83  --extra_neg_conj                        none
% 1.34/0.83  --large_theory_mode                     true
% 1.34/0.83  --prolific_symb_bound                   200
% 1.34/0.83  --lt_threshold                          2000
% 1.34/0.83  --clause_weak_htbl                      true
% 1.34/0.83  --gc_record_bc_elim                     false
% 1.34/0.83  
% 1.34/0.83  ------ Preprocessing Options
% 1.34/0.83  
% 1.34/0.83  --preprocessing_flag                    true
% 1.34/0.83  --time_out_prep_mult                    0.1
% 1.34/0.83  --splitting_mode                        input
% 1.34/0.83  --splitting_grd                         true
% 1.34/0.83  --splitting_cvd                         false
% 1.34/0.83  --splitting_cvd_svl                     false
% 1.34/0.83  --splitting_nvd                         32
% 1.34/0.83  --sub_typing                            true
% 1.34/0.83  --prep_gs_sim                           true
% 1.34/0.83  --prep_unflatten                        true
% 1.34/0.83  --prep_res_sim                          true
% 1.34/0.83  --prep_upred                            true
% 1.34/0.83  --prep_sem_filter                       exhaustive
% 1.34/0.83  --prep_sem_filter_out                   false
% 1.34/0.83  --pred_elim                             true
% 1.34/0.83  --res_sim_input                         true
% 1.34/0.83  --eq_ax_congr_red                       true
% 1.34/0.83  --pure_diseq_elim                       true
% 1.34/0.83  --brand_transform                       false
% 1.34/0.83  --non_eq_to_eq                          false
% 1.34/0.83  --prep_def_merge                        true
% 1.34/0.83  --prep_def_merge_prop_impl              false
% 1.34/0.83  --prep_def_merge_mbd                    true
% 1.34/0.83  --prep_def_merge_tr_red                 false
% 1.34/0.83  --prep_def_merge_tr_cl                  false
% 1.34/0.83  --smt_preprocessing                     true
% 1.34/0.83  --smt_ac_axioms                         fast
% 1.34/0.83  --preprocessed_out                      false
% 1.34/0.83  --preprocessed_stats                    false
% 1.34/0.83  
% 1.34/0.83  ------ Abstraction refinement Options
% 1.34/0.83  
% 1.34/0.83  --abstr_ref                             []
% 1.34/0.83  --abstr_ref_prep                        false
% 1.34/0.83  --abstr_ref_until_sat                   false
% 1.34/0.83  --abstr_ref_sig_restrict                funpre
% 1.34/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 1.34/0.83  --abstr_ref_under                       []
% 1.34/0.83  
% 1.34/0.83  ------ SAT Options
% 1.34/0.83  
% 1.34/0.83  --sat_mode                              false
% 1.34/0.83  --sat_fm_restart_options                ""
% 1.34/0.83  --sat_gr_def                            false
% 1.34/0.83  --sat_epr_types                         true
% 1.34/0.83  --sat_non_cyclic_types                  false
% 1.34/0.83  --sat_finite_models                     false
% 1.34/0.83  --sat_fm_lemmas                         false
% 1.34/0.83  --sat_fm_prep                           false
% 1.34/0.83  --sat_fm_uc_incr                        true
% 1.34/0.83  --sat_out_model                         small
% 1.34/0.83  --sat_out_clauses                       false
% 1.34/0.83  
% 1.34/0.83  ------ QBF Options
% 1.34/0.83  
% 1.34/0.83  --qbf_mode                              false
% 1.34/0.83  --qbf_elim_univ                         false
% 1.34/0.83  --qbf_dom_inst                          none
% 1.34/0.83  --qbf_dom_pre_inst                      false
% 1.34/0.83  --qbf_sk_in                             false
% 1.34/0.83  --qbf_pred_elim                         true
% 1.34/0.83  --qbf_split                             512
% 1.34/0.83  
% 1.34/0.83  ------ BMC1 Options
% 1.34/0.83  
% 1.34/0.83  --bmc1_incremental                      false
% 1.34/0.83  --bmc1_axioms                           reachable_all
% 1.34/0.83  --bmc1_min_bound                        0
% 1.34/0.83  --bmc1_max_bound                        -1
% 1.34/0.83  --bmc1_max_bound_default                -1
% 1.34/0.83  --bmc1_symbol_reachability              true
% 1.34/0.83  --bmc1_property_lemmas                  false
% 1.34/0.83  --bmc1_k_induction                      false
% 1.34/0.83  --bmc1_non_equiv_states                 false
% 1.34/0.83  --bmc1_deadlock                         false
% 1.34/0.83  --bmc1_ucm                              false
% 1.34/0.83  --bmc1_add_unsat_core                   none
% 1.34/0.83  --bmc1_unsat_core_children              false
% 1.34/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 1.34/0.83  --bmc1_out_stat                         full
% 1.34/0.83  --bmc1_ground_init                      false
% 1.34/0.83  --bmc1_pre_inst_next_state              false
% 1.34/0.83  --bmc1_pre_inst_state                   false
% 1.34/0.83  --bmc1_pre_inst_reach_state             false
% 1.34/0.83  --bmc1_out_unsat_core                   false
% 1.34/0.83  --bmc1_aig_witness_out                  false
% 1.34/0.83  --bmc1_verbose                          false
% 1.34/0.83  --bmc1_dump_clauses_tptp                false
% 1.34/0.83  --bmc1_dump_unsat_core_tptp             false
% 1.34/0.83  --bmc1_dump_file                        -
% 1.34/0.83  --bmc1_ucm_expand_uc_limit              128
% 1.34/0.83  --bmc1_ucm_n_expand_iterations          6
% 1.34/0.83  --bmc1_ucm_extend_mode                  1
% 1.34/0.83  --bmc1_ucm_init_mode                    2
% 1.34/0.83  --bmc1_ucm_cone_mode                    none
% 1.34/0.83  --bmc1_ucm_reduced_relation_type        0
% 1.34/0.83  --bmc1_ucm_relax_model                  4
% 1.34/0.83  --bmc1_ucm_full_tr_after_sat            true
% 1.34/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 1.34/0.83  --bmc1_ucm_layered_model                none
% 1.34/0.83  --bmc1_ucm_max_lemma_size               10
% 1.34/0.83  
% 1.34/0.83  ------ AIG Options
% 1.34/0.83  
% 1.34/0.83  --aig_mode                              false
% 1.34/0.83  
% 1.34/0.83  ------ Instantiation Options
% 1.34/0.83  
% 1.34/0.83  --instantiation_flag                    true
% 1.34/0.83  --inst_sos_flag                         false
% 1.34/0.83  --inst_sos_phase                        true
% 1.34/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.34/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.34/0.83  --inst_lit_sel_side                     num_symb
% 1.34/0.83  --inst_solver_per_active                1400
% 1.34/0.83  --inst_solver_calls_frac                1.
% 1.34/0.83  --inst_passive_queue_type               priority_queues
% 1.34/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.34/0.83  --inst_passive_queues_freq              [25;2]
% 1.34/0.83  --inst_dismatching                      true
% 1.34/0.83  --inst_eager_unprocessed_to_passive     true
% 1.34/0.83  --inst_prop_sim_given                   true
% 1.34/0.83  --inst_prop_sim_new                     false
% 1.34/0.83  --inst_subs_new                         false
% 1.34/0.83  --inst_eq_res_simp                      false
% 1.34/0.83  --inst_subs_given                       false
% 1.34/0.83  --inst_orphan_elimination               true
% 1.34/0.83  --inst_learning_loop_flag               true
% 1.34/0.83  --inst_learning_start                   3000
% 1.34/0.83  --inst_learning_factor                  2
% 1.34/0.83  --inst_start_prop_sim_after_learn       3
% 1.34/0.83  --inst_sel_renew                        solver
% 1.34/0.83  --inst_lit_activity_flag                true
% 1.34/0.83  --inst_restr_to_given                   false
% 1.34/0.83  --inst_activity_threshold               500
% 1.34/0.83  --inst_out_proof                        true
% 1.34/0.83  
% 1.34/0.83  ------ Resolution Options
% 1.34/0.83  
% 1.34/0.83  --resolution_flag                       true
% 1.34/0.83  --res_lit_sel                           adaptive
% 1.34/0.83  --res_lit_sel_side                      none
% 1.34/0.83  --res_ordering                          kbo
% 1.34/0.83  --res_to_prop_solver                    active
% 1.34/0.83  --res_prop_simpl_new                    false
% 1.34/0.83  --res_prop_simpl_given                  true
% 1.34/0.83  --res_passive_queue_type                priority_queues
% 1.34/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.34/0.83  --res_passive_queues_freq               [15;5]
% 1.34/0.83  --res_forward_subs                      full
% 1.34/0.83  --res_backward_subs                     full
% 1.34/0.83  --res_forward_subs_resolution           true
% 1.34/0.83  --res_backward_subs_resolution          true
% 1.34/0.83  --res_orphan_elimination                true
% 1.34/0.83  --res_time_limit                        2.
% 1.34/0.83  --res_out_proof                         true
% 1.34/0.83  
% 1.34/0.83  ------ Superposition Options
% 1.34/0.83  
% 1.34/0.83  --superposition_flag                    true
% 1.34/0.83  --sup_passive_queue_type                priority_queues
% 1.34/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.34/0.83  --sup_passive_queues_freq               [8;1;4]
% 1.34/0.83  --demod_completeness_check              fast
% 1.34/0.83  --demod_use_ground                      true
% 1.34/0.83  --sup_to_prop_solver                    passive
% 1.34/0.83  --sup_prop_simpl_new                    true
% 1.34/0.83  --sup_prop_simpl_given                  true
% 1.34/0.83  --sup_fun_splitting                     false
% 1.34/0.83  --sup_smt_interval                      50000
% 1.34/0.83  
% 1.34/0.83  ------ Superposition Simplification Setup
% 1.34/0.83  
% 1.34/0.83  --sup_indices_passive                   []
% 1.34/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 1.34/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.83  --sup_full_bw                           [BwDemod]
% 1.34/0.83  --sup_immed_triv                        [TrivRules]
% 1.34/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.34/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.83  --sup_immed_bw_main                     []
% 1.34/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 1.34/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.83  
% 1.34/0.83  ------ Combination Options
% 1.34/0.83  
% 1.34/0.83  --comb_res_mult                         3
% 1.34/0.83  --comb_sup_mult                         2
% 1.34/0.83  --comb_inst_mult                        10
% 1.34/0.83  
% 1.34/0.83  ------ Debug Options
% 1.34/0.83  
% 1.34/0.83  --dbg_backtrace                         false
% 1.34/0.83  --dbg_dump_prop_clauses                 false
% 1.34/0.83  --dbg_dump_prop_clauses_file            -
% 1.34/0.83  --dbg_out_stat                          false
% 1.34/0.83  ------ Parsing...
% 1.34/0.83  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.34/0.83  
% 1.34/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.34/0.83  
% 1.34/0.83  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.34/0.83  
% 1.34/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.34/0.83  ------ Proving...
% 1.34/0.83  ------ Problem Properties 
% 1.34/0.83  
% 1.34/0.83  
% 1.34/0.83  clauses                                 19
% 1.34/0.83  conjectures                             9
% 1.34/0.83  EPR                                     10
% 1.34/0.83  Horn                                    17
% 1.34/0.83  unary                                   11
% 1.34/0.83  binary                                  1
% 1.34/0.83  lits                                    40
% 1.34/0.83  lits eq                                 8
% 1.34/0.83  fd_pure                                 0
% 1.34/0.83  fd_pseudo                               0
% 1.34/0.83  fd_cond                                 1
% 1.34/0.83  fd_pseudo_cond                          0
% 1.34/0.83  AC symbols                              0
% 1.34/0.83  
% 1.34/0.83  ------ Schedule dynamic 5 is on 
% 1.34/0.83  
% 1.34/0.83  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.34/0.83  
% 1.34/0.83  
% 1.34/0.83  ------ 
% 1.34/0.83  Current options:
% 1.34/0.83  ------ 
% 1.34/0.83  
% 1.34/0.83  ------ Input Options
% 1.34/0.83  
% 1.34/0.83  --out_options                           all
% 1.34/0.83  --tptp_safe_out                         true
% 1.34/0.83  --problem_path                          ""
% 1.34/0.83  --include_path                          ""
% 1.34/0.83  --clausifier                            res/vclausify_rel
% 1.34/0.83  --clausifier_options                    --mode clausify
% 1.34/0.83  --stdin                                 false
% 1.34/0.83  --stats_out                             all
% 1.34/0.83  
% 1.34/0.83  ------ General Options
% 1.34/0.83  
% 1.34/0.83  --fof                                   false
% 1.34/0.83  --time_out_real                         305.
% 1.34/0.83  --time_out_virtual                      -1.
% 1.34/0.83  --symbol_type_check                     false
% 1.34/0.83  --clausify_out                          false
% 1.34/0.83  --sig_cnt_out                           false
% 1.34/0.83  --trig_cnt_out                          false
% 1.34/0.83  --trig_cnt_out_tolerance                1.
% 1.34/0.83  --trig_cnt_out_sk_spl                   false
% 1.34/0.83  --abstr_cl_out                          false
% 1.34/0.83  
% 1.34/0.83  ------ Global Options
% 1.34/0.83  
% 1.34/0.83  --schedule                              default
% 1.34/0.83  --add_important_lit                     false
% 1.34/0.83  --prop_solver_per_cl                    1000
% 1.34/0.83  --min_unsat_core                        false
% 1.34/0.83  --soft_assumptions                      false
% 1.34/0.83  --soft_lemma_size                       3
% 1.34/0.83  --prop_impl_unit_size                   0
% 1.34/0.83  --prop_impl_unit                        []
% 1.34/0.83  --share_sel_clauses                     true
% 1.34/0.83  --reset_solvers                         false
% 1.34/0.83  --bc_imp_inh                            [conj_cone]
% 1.34/0.83  --conj_cone_tolerance                   3.
% 1.34/0.83  --extra_neg_conj                        none
% 1.34/0.83  --large_theory_mode                     true
% 1.34/0.83  --prolific_symb_bound                   200
% 1.34/0.83  --lt_threshold                          2000
% 1.34/0.83  --clause_weak_htbl                      true
% 1.34/0.83  --gc_record_bc_elim                     false
% 1.34/0.83  
% 1.34/0.83  ------ Preprocessing Options
% 1.34/0.83  
% 1.34/0.83  --preprocessing_flag                    true
% 1.34/0.83  --time_out_prep_mult                    0.1
% 1.34/0.83  --splitting_mode                        input
% 1.34/0.83  --splitting_grd                         true
% 1.34/0.83  --splitting_cvd                         false
% 1.34/0.83  --splitting_cvd_svl                     false
% 1.34/0.83  --splitting_nvd                         32
% 1.34/0.83  --sub_typing                            true
% 1.34/0.83  --prep_gs_sim                           true
% 1.34/0.83  --prep_unflatten                        true
% 1.34/0.83  --prep_res_sim                          true
% 1.34/0.83  --prep_upred                            true
% 1.34/0.83  --prep_sem_filter                       exhaustive
% 1.34/0.83  --prep_sem_filter_out                   false
% 1.34/0.83  --pred_elim                             true
% 1.34/0.83  --res_sim_input                         true
% 1.34/0.83  --eq_ax_congr_red                       true
% 1.34/0.83  --pure_diseq_elim                       true
% 1.34/0.83  --brand_transform                       false
% 1.34/0.83  --non_eq_to_eq                          false
% 1.34/0.83  --prep_def_merge                        true
% 1.34/0.83  --prep_def_merge_prop_impl              false
% 1.34/0.83  --prep_def_merge_mbd                    true
% 1.34/0.83  --prep_def_merge_tr_red                 false
% 1.34/0.83  --prep_def_merge_tr_cl                  false
% 1.34/0.83  --smt_preprocessing                     true
% 1.34/0.83  --smt_ac_axioms                         fast
% 1.34/0.83  --preprocessed_out                      false
% 1.34/0.83  --preprocessed_stats                    false
% 1.34/0.83  
% 1.34/0.83  ------ Abstraction refinement Options
% 1.34/0.83  
% 1.34/0.83  --abstr_ref                             []
% 1.34/0.83  --abstr_ref_prep                        false
% 1.34/0.83  --abstr_ref_until_sat                   false
% 1.34/0.83  --abstr_ref_sig_restrict                funpre
% 1.34/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 1.34/0.83  --abstr_ref_under                       []
% 1.34/0.83  
% 1.34/0.83  ------ SAT Options
% 1.34/0.83  
% 1.34/0.83  --sat_mode                              false
% 1.34/0.83  --sat_fm_restart_options                ""
% 1.34/0.83  --sat_gr_def                            false
% 1.34/0.83  --sat_epr_types                         true
% 1.34/0.83  --sat_non_cyclic_types                  false
% 1.34/0.83  --sat_finite_models                     false
% 1.34/0.83  --sat_fm_lemmas                         false
% 1.34/0.83  --sat_fm_prep                           false
% 1.34/0.83  --sat_fm_uc_incr                        true
% 1.34/0.83  --sat_out_model                         small
% 1.34/0.83  --sat_out_clauses                       false
% 1.34/0.83  
% 1.34/0.83  ------ QBF Options
% 1.34/0.83  
% 1.34/0.83  --qbf_mode                              false
% 1.34/0.83  --qbf_elim_univ                         false
% 1.34/0.83  --qbf_dom_inst                          none
% 1.34/0.83  --qbf_dom_pre_inst                      false
% 1.34/0.83  --qbf_sk_in                             false
% 1.34/0.83  --qbf_pred_elim                         true
% 1.34/0.83  --qbf_split                             512
% 1.34/0.83  
% 1.34/0.83  ------ BMC1 Options
% 1.34/0.83  
% 1.34/0.83  --bmc1_incremental                      false
% 1.34/0.83  --bmc1_axioms                           reachable_all
% 1.34/0.83  --bmc1_min_bound                        0
% 1.34/0.83  --bmc1_max_bound                        -1
% 1.34/0.83  --bmc1_max_bound_default                -1
% 1.34/0.83  --bmc1_symbol_reachability              true
% 1.34/0.83  --bmc1_property_lemmas                  false
% 1.34/0.83  --bmc1_k_induction                      false
% 1.34/0.83  --bmc1_non_equiv_states                 false
% 1.34/0.83  --bmc1_deadlock                         false
% 1.34/0.83  --bmc1_ucm                              false
% 1.34/0.83  --bmc1_add_unsat_core                   none
% 1.34/0.83  --bmc1_unsat_core_children              false
% 1.34/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 1.34/0.83  --bmc1_out_stat                         full
% 1.34/0.83  --bmc1_ground_init                      false
% 1.34/0.83  --bmc1_pre_inst_next_state              false
% 1.34/0.83  --bmc1_pre_inst_state                   false
% 1.34/0.83  --bmc1_pre_inst_reach_state             false
% 1.34/0.83  --bmc1_out_unsat_core                   false
% 1.34/0.83  --bmc1_aig_witness_out                  false
% 1.34/0.83  --bmc1_verbose                          false
% 1.34/0.83  --bmc1_dump_clauses_tptp                false
% 1.34/0.83  --bmc1_dump_unsat_core_tptp             false
% 1.34/0.83  --bmc1_dump_file                        -
% 1.34/0.83  --bmc1_ucm_expand_uc_limit              128
% 1.34/0.83  --bmc1_ucm_n_expand_iterations          6
% 1.34/0.83  --bmc1_ucm_extend_mode                  1
% 1.34/0.83  --bmc1_ucm_init_mode                    2
% 1.34/0.83  --bmc1_ucm_cone_mode                    none
% 1.34/0.83  --bmc1_ucm_reduced_relation_type        0
% 1.34/0.83  --bmc1_ucm_relax_model                  4
% 1.34/0.83  --bmc1_ucm_full_tr_after_sat            true
% 1.34/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 1.34/0.83  --bmc1_ucm_layered_model                none
% 1.34/0.83  --bmc1_ucm_max_lemma_size               10
% 1.34/0.83  
% 1.34/0.83  ------ AIG Options
% 1.34/0.83  
% 1.34/0.83  --aig_mode                              false
% 1.34/0.83  
% 1.34/0.83  ------ Instantiation Options
% 1.34/0.83  
% 1.34/0.83  --instantiation_flag                    true
% 1.34/0.83  --inst_sos_flag                         false
% 1.34/0.83  --inst_sos_phase                        true
% 1.34/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.34/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.34/0.83  --inst_lit_sel_side                     none
% 1.34/0.83  --inst_solver_per_active                1400
% 1.34/0.83  --inst_solver_calls_frac                1.
% 1.34/0.83  --inst_passive_queue_type               priority_queues
% 1.34/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.34/0.83  --inst_passive_queues_freq              [25;2]
% 1.34/0.83  --inst_dismatching                      true
% 1.34/0.83  --inst_eager_unprocessed_to_passive     true
% 1.34/0.83  --inst_prop_sim_given                   true
% 1.34/0.83  --inst_prop_sim_new                     false
% 1.34/0.83  --inst_subs_new                         false
% 1.34/0.83  --inst_eq_res_simp                      false
% 1.34/0.83  --inst_subs_given                       false
% 1.34/0.83  --inst_orphan_elimination               true
% 1.34/0.83  --inst_learning_loop_flag               true
% 1.34/0.83  --inst_learning_start                   3000
% 1.34/0.83  --inst_learning_factor                  2
% 1.34/0.83  --inst_start_prop_sim_after_learn       3
% 1.34/0.83  --inst_sel_renew                        solver
% 1.34/0.83  --inst_lit_activity_flag                true
% 1.34/0.83  --inst_restr_to_given                   false
% 1.34/0.83  --inst_activity_threshold               500
% 1.34/0.83  --inst_out_proof                        true
% 1.34/0.83  
% 1.34/0.83  ------ Resolution Options
% 1.34/0.83  
% 1.34/0.83  --resolution_flag                       false
% 1.34/0.83  --res_lit_sel                           adaptive
% 1.34/0.83  --res_lit_sel_side                      none
% 1.34/0.83  --res_ordering                          kbo
% 1.34/0.83  --res_to_prop_solver                    active
% 1.34/0.83  --res_prop_simpl_new                    false
% 1.34/0.83  --res_prop_simpl_given                  true
% 1.34/0.83  --res_passive_queue_type                priority_queues
% 1.34/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.34/0.83  --res_passive_queues_freq               [15;5]
% 1.34/0.83  --res_forward_subs                      full
% 1.34/0.83  --res_backward_subs                     full
% 1.34/0.83  --res_forward_subs_resolution           true
% 1.34/0.83  --res_backward_subs_resolution          true
% 1.34/0.83  --res_orphan_elimination                true
% 1.34/0.83  --res_time_limit                        2.
% 1.34/0.83  --res_out_proof                         true
% 1.34/0.83  
% 1.34/0.83  ------ Superposition Options
% 1.34/0.83  
% 1.34/0.83  --superposition_flag                    true
% 1.34/0.83  --sup_passive_queue_type                priority_queues
% 1.34/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.34/0.83  --sup_passive_queues_freq               [8;1;4]
% 1.34/0.83  --demod_completeness_check              fast
% 1.34/0.83  --demod_use_ground                      true
% 1.34/0.83  --sup_to_prop_solver                    passive
% 1.34/0.83  --sup_prop_simpl_new                    true
% 1.34/0.83  --sup_prop_simpl_given                  true
% 1.34/0.83  --sup_fun_splitting                     false
% 1.34/0.83  --sup_smt_interval                      50000
% 1.34/0.83  
% 1.34/0.83  ------ Superposition Simplification Setup
% 1.34/0.83  
% 1.34/0.83  --sup_indices_passive                   []
% 1.34/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.34/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 1.34/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.83  --sup_full_bw                           [BwDemod]
% 1.34/0.83  --sup_immed_triv                        [TrivRules]
% 1.34/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.34/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.83  --sup_immed_bw_main                     []
% 1.34/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 1.34/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.34/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.34/0.83  
% 1.34/0.83  ------ Combination Options
% 1.34/0.83  
% 1.34/0.83  --comb_res_mult                         3
% 1.34/0.83  --comb_sup_mult                         2
% 1.34/0.83  --comb_inst_mult                        10
% 1.34/0.83  
% 1.34/0.83  ------ Debug Options
% 1.34/0.83  
% 1.34/0.83  --dbg_backtrace                         false
% 1.34/0.83  --dbg_dump_prop_clauses                 false
% 1.34/0.83  --dbg_dump_prop_clauses_file            -
% 1.34/0.83  --dbg_out_stat                          false
% 1.34/0.83  
% 1.34/0.83  
% 1.34/0.83  
% 1.34/0.83  
% 1.34/0.83  ------ Proving...
% 1.34/0.83  
% 1.34/0.83  
% 1.34/0.83  % SZS status Theorem for theBenchmark.p
% 1.34/0.83  
% 1.34/0.83  % SZS output start CNFRefutation for theBenchmark.p
% 1.34/0.83  
% 1.34/0.83  fof(f9,conjecture,(
% 1.34/0.83    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f10,negated_conjecture,(
% 1.34/0.83    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.34/0.83    inference(negated_conjecture,[],[f9])).
% 1.34/0.83  
% 1.34/0.83  fof(f20,plain,(
% 1.34/0.83    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.34/0.83    inference(ennf_transformation,[],[f10])).
% 1.34/0.83  
% 1.34/0.83  fof(f21,plain,(
% 1.34/0.83    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.34/0.83    inference(flattening,[],[f20])).
% 1.34/0.83  
% 1.34/0.83  fof(f26,plain,(
% 1.34/0.83    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 1.34/0.83    introduced(choice_axiom,[])).
% 1.34/0.83  
% 1.34/0.83  fof(f25,plain,(
% 1.34/0.83    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 1.34/0.83    introduced(choice_axiom,[])).
% 1.34/0.83  
% 1.34/0.83  fof(f24,plain,(
% 1.34/0.83    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 1.34/0.83    introduced(choice_axiom,[])).
% 1.34/0.83  
% 1.34/0.83  fof(f23,plain,(
% 1.34/0.83    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 1.34/0.83    introduced(choice_axiom,[])).
% 1.34/0.83  
% 1.34/0.83  fof(f27,plain,(
% 1.34/0.83    (((k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 1.34/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f26,f25,f24,f23])).
% 1.34/0.83  
% 1.34/0.83  fof(f42,plain,(
% 1.34/0.83    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f44,plain,(
% 1.34/0.83    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f7,axiom,(
% 1.34/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f16,plain,(
% 1.34/0.83    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.34/0.83    inference(ennf_transformation,[],[f7])).
% 1.34/0.83  
% 1.34/0.83  fof(f17,plain,(
% 1.34/0.83    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.34/0.83    inference(flattening,[],[f16])).
% 1.34/0.83  
% 1.34/0.83  fof(f37,plain,(
% 1.34/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.34/0.83    inference(cnf_transformation,[],[f17])).
% 1.34/0.83  
% 1.34/0.83  fof(f43,plain,(
% 1.34/0.83    v1_funct_1(sK4)),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f46,plain,(
% 1.34/0.83    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f6,axiom,(
% 1.34/0.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f14,plain,(
% 1.34/0.83    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.34/0.83    inference(ennf_transformation,[],[f6])).
% 1.34/0.83  
% 1.34/0.83  fof(f15,plain,(
% 1.34/0.83    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.34/0.83    inference(flattening,[],[f14])).
% 1.34/0.83  
% 1.34/0.83  fof(f36,plain,(
% 1.34/0.83    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.34/0.83    inference(cnf_transformation,[],[f15])).
% 1.34/0.83  
% 1.34/0.83  fof(f41,plain,(
% 1.34/0.83    v1_funct_2(sK3,sK1,sK2)),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f40,plain,(
% 1.34/0.83    v1_funct_1(sK3)),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f39,plain,(
% 1.34/0.83    ~v1_xboole_0(sK2)),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f1,axiom,(
% 1.34/0.83    v1_xboole_0(k1_xboole_0)),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f28,plain,(
% 1.34/0.83    v1_xboole_0(k1_xboole_0)),
% 1.34/0.83    inference(cnf_transformation,[],[f1])).
% 1.34/0.83  
% 1.34/0.83  fof(f5,axiom,(
% 1.34/0.83    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f35,plain,(
% 1.34/0.83    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.83    inference(cnf_transformation,[],[f5])).
% 1.34/0.83  
% 1.34/0.83  fof(f3,axiom,(
% 1.34/0.83    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f12,plain,(
% 1.34/0.83    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.34/0.83    inference(ennf_transformation,[],[f3])).
% 1.34/0.83  
% 1.34/0.83  fof(f22,plain,(
% 1.34/0.83    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.34/0.83    inference(nnf_transformation,[],[f12])).
% 1.34/0.83  
% 1.34/0.83  fof(f30,plain,(
% 1.34/0.83    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.34/0.83    inference(cnf_transformation,[],[f22])).
% 1.34/0.83  
% 1.34/0.83  fof(f8,axiom,(
% 1.34/0.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1))))),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f18,plain,(
% 1.34/0.83    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.34/0.83    inference(ennf_transformation,[],[f8])).
% 1.34/0.83  
% 1.34/0.83  fof(f19,plain,(
% 1.34/0.83    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.34/0.83    inference(flattening,[],[f18])).
% 1.34/0.83  
% 1.34/0.83  fof(f38,plain,(
% 1.34/0.83    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.34/0.83    inference(cnf_transformation,[],[f19])).
% 1.34/0.83  
% 1.34/0.83  fof(f4,axiom,(
% 1.34/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f13,plain,(
% 1.34/0.83    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.83    inference(ennf_transformation,[],[f4])).
% 1.34/0.83  
% 1.34/0.83  fof(f34,plain,(
% 1.34/0.83    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.34/0.83    inference(cnf_transformation,[],[f13])).
% 1.34/0.83  
% 1.34/0.83  fof(f2,axiom,(
% 1.34/0.83    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.34/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.34/0.83  
% 1.34/0.83  fof(f11,plain,(
% 1.34/0.83    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.34/0.83    inference(ennf_transformation,[],[f2])).
% 1.34/0.83  
% 1.34/0.83  fof(f29,plain,(
% 1.34/0.83    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.34/0.83    inference(cnf_transformation,[],[f11])).
% 1.34/0.83  
% 1.34/0.83  fof(f47,plain,(
% 1.34/0.83    k1_xboole_0 != sK1),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f48,plain,(
% 1.34/0.83    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  fof(f45,plain,(
% 1.34/0.83    m1_subset_1(sK5,sK1)),
% 1.34/0.83    inference(cnf_transformation,[],[f27])).
% 1.34/0.83  
% 1.34/0.83  cnf(c_17,negated_conjecture,
% 1.34/0.83      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.34/0.83      inference(cnf_transformation,[],[f42]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_529,negated_conjecture,
% 1.34/0.83      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_17]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_902,plain,
% 1.34/0.83      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_15,negated_conjecture,
% 1.34/0.83      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 1.34/0.83      inference(cnf_transformation,[],[f44]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_531,negated_conjecture,
% 1.34/0.83      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_15]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_900,plain,
% 1.34/0.83      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_9,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.34/0.83      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.34/0.83      | ~ v1_funct_1(X3)
% 1.34/0.83      | ~ v1_funct_1(X0)
% 1.34/0.83      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.34/0.83      inference(cnf_transformation,[],[f37]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_536,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.34/0.83      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X5_52)))
% 1.34/0.83      | ~ v1_funct_1(X3_52)
% 1.34/0.83      | ~ v1_funct_1(X0_52)
% 1.34/0.83      | k1_partfun1(X4_52,X5_52,X1_52,X2_52,X3_52,X0_52) = k5_relat_1(X3_52,X0_52) ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_9]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_897,plain,
% 1.34/0.83      ( k1_partfun1(X0_52,X1_52,X2_52,X3_52,X4_52,X5_52) = k5_relat_1(X4_52,X5_52)
% 1.34/0.83      | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X2_52,X3_52))) != iProver_top
% 1.34/0.83      | m1_subset_1(X4_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.34/0.83      | v1_funct_1(X5_52) != iProver_top
% 1.34/0.83      | v1_funct_1(X4_52) != iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1595,plain,
% 1.34/0.83      ( k1_partfun1(X0_52,X1_52,sK2,sK0,X2_52,sK4) = k5_relat_1(X2_52,sK4)
% 1.34/0.83      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.34/0.83      | v1_funct_1(X2_52) != iProver_top
% 1.34/0.83      | v1_funct_1(sK4) != iProver_top ),
% 1.34/0.83      inference(superposition,[status(thm)],[c_900,c_897]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_16,negated_conjecture,
% 1.34/0.83      ( v1_funct_1(sK4) ),
% 1.34/0.83      inference(cnf_transformation,[],[f43]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_25,plain,
% 1.34/0.83      ( v1_funct_1(sK4) = iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1762,plain,
% 1.34/0.83      ( v1_funct_1(X2_52) != iProver_top
% 1.34/0.83      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.34/0.83      | k1_partfun1(X0_52,X1_52,sK2,sK0,X2_52,sK4) = k5_relat_1(X2_52,sK4) ),
% 1.34/0.83      inference(global_propositional_subsumption,
% 1.34/0.83                [status(thm)],
% 1.34/0.83                [c_1595,c_25]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1763,plain,
% 1.34/0.83      ( k1_partfun1(X0_52,X1_52,sK2,sK0,X2_52,sK4) = k5_relat_1(X2_52,sK4)
% 1.34/0.83      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.34/0.83      | v1_funct_1(X2_52) != iProver_top ),
% 1.34/0.83      inference(renaming,[status(thm)],[c_1762]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1772,plain,
% 1.34/0.83      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 1.34/0.83      | v1_funct_1(sK3) != iProver_top ),
% 1.34/0.83      inference(superposition,[status(thm)],[c_902,c_1763]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_13,negated_conjecture,
% 1.34/0.83      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 1.34/0.83      inference(cnf_transformation,[],[f46]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_533,negated_conjecture,
% 1.34/0.83      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_13]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_898,plain,
% 1.34/0.83      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_8,plain,
% 1.34/0.83      ( ~ v1_funct_2(X0,X1,X2)
% 1.34/0.83      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 1.34/0.83      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.34/0.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.34/0.83      | ~ v1_funct_1(X4)
% 1.34/0.83      | ~ v1_funct_1(X0)
% 1.34/0.83      | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
% 1.34/0.83      | k1_xboole_0 = X2 ),
% 1.34/0.83      inference(cnf_transformation,[],[f36]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_18,negated_conjecture,
% 1.34/0.83      ( v1_funct_2(sK3,sK1,sK2) ),
% 1.34/0.83      inference(cnf_transformation,[],[f41]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_316,plain,
% 1.34/0.83      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 1.34/0.83      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.34/0.83      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.34/0.83      | ~ v1_funct_1(X4)
% 1.34/0.83      | ~ v1_funct_1(X2)
% 1.34/0.83      | k1_partfun1(X0,X1,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,X4)
% 1.34/0.83      | sK2 != X1
% 1.34/0.83      | sK1 != X0
% 1.34/0.83      | sK3 != X2
% 1.34/0.83      | k1_xboole_0 = X1 ),
% 1.34/0.83      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_317,plain,
% 1.34/0.83      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.34/0.83      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.34/0.83      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.34/0.83      | ~ v1_funct_1(X1)
% 1.34/0.83      | ~ v1_funct_1(sK3)
% 1.34/0.83      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(unflattening,[status(thm)],[c_316]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_19,negated_conjecture,
% 1.34/0.83      ( v1_funct_1(sK3) ),
% 1.34/0.83      inference(cnf_transformation,[],[f40]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_321,plain,
% 1.34/0.83      ( ~ v1_funct_1(X1)
% 1.34/0.83      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.34/0.83      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.34/0.83      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(global_propositional_subsumption,
% 1.34/0.83                [status(thm)],
% 1.34/0.83                [c_317,c_19,c_17]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_322,plain,
% 1.34/0.83      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.34/0.83      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.34/0.83      | ~ v1_funct_1(X1)
% 1.34/0.83      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(renaming,[status(thm)],[c_321]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_525,plain,
% 1.34/0.83      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52))
% 1.34/0.83      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52)))
% 1.34/0.83      | ~ v1_funct_1(X1_52)
% 1.34/0.83      | k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_322]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_907,plain,
% 1.34/0.83      ( k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
% 1.34/0.83      | k1_xboole_0 = sK2
% 1.34/0.83      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52)) != iProver_top
% 1.34/0.83      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52))) != iProver_top
% 1.34/0.83      | v1_funct_1(X1_52) != iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_20,negated_conjecture,
% 1.34/0.83      ( ~ v1_xboole_0(sK2) ),
% 1.34/0.83      inference(cnf_transformation,[],[f39]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_0,plain,
% 1.34/0.83      ( v1_xboole_0(k1_xboole_0) ),
% 1.34/0.83      inference(cnf_transformation,[],[f28]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_548,plain,( X0_52 = X0_52 ),theory(equality) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_579,plain,
% 1.34/0.83      ( sK2 = sK2 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_548]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_600,plain,
% 1.34/0.83      ( k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
% 1.34/0.83      | k1_xboole_0 = sK2
% 1.34/0.83      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52)) != iProver_top
% 1.34/0.83      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52))) != iProver_top
% 1.34/0.83      | v1_funct_1(X1_52) != iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_550,plain,
% 1.34/0.83      ( ~ v1_xboole_0(X0_52) | v1_xboole_0(X1_52) | X1_52 != X0_52 ),
% 1.34/0.83      theory(equality) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1070,plain,
% 1.34/0.83      ( v1_xboole_0(X0_52)
% 1.34/0.83      | ~ v1_xboole_0(k1_xboole_0)
% 1.34/0.83      | X0_52 != k1_xboole_0 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_550]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1072,plain,
% 1.34/0.83      ( v1_xboole_0(sK2)
% 1.34/0.83      | ~ v1_xboole_0(k1_xboole_0)
% 1.34/0.83      | sK2 != k1_xboole_0 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_1070]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_549,plain,
% 1.34/0.83      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 1.34/0.83      theory(equality) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1328,plain,
% 1.34/0.83      ( X0_52 != X1_52 | X0_52 = k1_xboole_0 | k1_xboole_0 != X1_52 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_549]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1329,plain,
% 1.34/0.83      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_1328]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1465,plain,
% 1.34/0.83      ( k1_partfun1(sK1,sK2,sK2,X0_52,sK3,X1_52) = k8_funct_2(sK1,sK2,X0_52,sK3,X1_52)
% 1.34/0.83      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_52,X1_52)) != iProver_top
% 1.34/0.83      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_52))) != iProver_top
% 1.34/0.83      | v1_funct_1(X1_52) != iProver_top ),
% 1.34/0.83      inference(global_propositional_subsumption,
% 1.34/0.83                [status(thm)],
% 1.34/0.83                [c_907,c_20,c_0,c_579,c_600,c_1072,c_1329]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1475,plain,
% 1.34/0.83      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
% 1.34/0.83      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 1.34/0.83      | v1_funct_1(sK4) != iProver_top ),
% 1.34/0.83      inference(superposition,[status(thm)],[c_898,c_1465]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_26,plain,
% 1.34/0.83      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1478,plain,
% 1.34/0.83      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4) ),
% 1.34/0.83      inference(global_propositional_subsumption,
% 1.34/0.83                [status(thm)],
% 1.34/0.83                [c_1475,c_25,c_26]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1784,plain,
% 1.34/0.83      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 1.34/0.83      | v1_funct_1(sK3) != iProver_top ),
% 1.34/0.83      inference(demodulation,[status(thm)],[c_1772,c_1478]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_562,plain,
% 1.34/0.83      ( X0_52 != X1_52
% 1.34/0.83      | X2_52 != X3_52
% 1.34/0.83      | k1_funct_1(X0_52,X2_52) = k1_funct_1(X1_52,X3_52) ),
% 1.34/0.83      theory(equality) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1726,plain,
% 1.34/0.83      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) != k5_relat_1(sK3,sK4)
% 1.34/0.83      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)
% 1.34/0.83      | sK5 != sK5 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_562]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_7,plain,
% 1.34/0.83      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.34/0.83      inference(cnf_transformation,[],[f35]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_537,plain,
% 1.34/0.83      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_7]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1555,plain,
% 1.34/0.83      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_537]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1217,plain,
% 1.34/0.83      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != X0_52
% 1.34/0.83      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != X0_52 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_549]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1549,plain,
% 1.34/0.83      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
% 1.34/0.83      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_1217]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_5,plain,
% 1.34/0.83      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 1.34/0.83      inference(cnf_transformation,[],[f30]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_10,plain,
% 1.34/0.83      ( ~ v1_funct_2(X0,X1,X2)
% 1.34/0.83      | ~ r2_hidden(X3,X1)
% 1.34/0.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.34/0.83      | ~ v1_funct_1(X4)
% 1.34/0.83      | ~ v1_funct_1(X0)
% 1.34/0.83      | ~ v1_relat_1(X4)
% 1.34/0.83      | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 1.34/0.83      | k1_xboole_0 = X2 ),
% 1.34/0.83      inference(cnf_transformation,[],[f38]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_243,plain,
% 1.34/0.83      ( ~ v1_funct_2(X0,X1,X2)
% 1.34/0.83      | ~ m1_subset_1(X3,X4)
% 1.34/0.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.34/0.83      | ~ v1_funct_1(X0)
% 1.34/0.83      | ~ v1_funct_1(X5)
% 1.34/0.83      | ~ v1_relat_1(X5)
% 1.34/0.83      | v1_xboole_0(X4)
% 1.34/0.83      | X6 != X3
% 1.34/0.83      | X1 != X4
% 1.34/0.83      | k1_funct_1(X5,k1_funct_1(X0,X6)) = k1_funct_1(k5_relat_1(X0,X5),X6)
% 1.34/0.83      | k1_xboole_0 = X2 ),
% 1.34/0.83      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_244,plain,
% 1.34/0.83      ( ~ v1_funct_2(X0,X1,X2)
% 1.34/0.83      | ~ m1_subset_1(X3,X1)
% 1.34/0.83      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.34/0.83      | ~ v1_funct_1(X0)
% 1.34/0.83      | ~ v1_funct_1(X4)
% 1.34/0.83      | ~ v1_relat_1(X4)
% 1.34/0.83      | v1_xboole_0(X1)
% 1.34/0.83      | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
% 1.34/0.83      | k1_xboole_0 = X2 ),
% 1.34/0.83      inference(unflattening,[status(thm)],[c_243]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_286,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0,X1)
% 1.34/0.83      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.34/0.83      | ~ v1_funct_1(X4)
% 1.34/0.83      | ~ v1_funct_1(X2)
% 1.34/0.83      | ~ v1_relat_1(X4)
% 1.34/0.83      | v1_xboole_0(X1)
% 1.34/0.83      | k1_funct_1(X4,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X4),X0)
% 1.34/0.83      | sK2 != X3
% 1.34/0.83      | sK1 != X1
% 1.34/0.83      | sK3 != X2
% 1.34/0.83      | k1_xboole_0 = X3 ),
% 1.34/0.83      inference(resolution_lifted,[status(thm)],[c_244,c_18]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_287,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0,sK1)
% 1.34/0.83      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.34/0.83      | ~ v1_funct_1(X1)
% 1.34/0.83      | ~ v1_funct_1(sK3)
% 1.34/0.83      | ~ v1_relat_1(X1)
% 1.34/0.83      | v1_xboole_0(sK1)
% 1.34/0.83      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(unflattening,[status(thm)],[c_286]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_291,plain,
% 1.34/0.83      ( ~ v1_funct_1(X1)
% 1.34/0.83      | ~ m1_subset_1(X0,sK1)
% 1.34/0.83      | ~ v1_relat_1(X1)
% 1.34/0.83      | v1_xboole_0(sK1)
% 1.34/0.83      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(global_propositional_subsumption,
% 1.34/0.83                [status(thm)],
% 1.34/0.83                [c_287,c_19,c_17]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_292,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0,sK1)
% 1.34/0.83      | ~ v1_funct_1(X1)
% 1.34/0.83      | ~ v1_relat_1(X1)
% 1.34/0.83      | v1_xboole_0(sK1)
% 1.34/0.83      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(renaming,[status(thm)],[c_291]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_526,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0_52,sK1)
% 1.34/0.83      | ~ v1_funct_1(X1_52)
% 1.34/0.83      | ~ v1_relat_1(X1_52)
% 1.34/0.83      | v1_xboole_0(sK1)
% 1.34/0.83      | k1_funct_1(X1_52,k1_funct_1(sK3,X0_52)) = k1_funct_1(k5_relat_1(sK3,X1_52),X0_52)
% 1.34/0.83      | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_292]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_543,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0_52,sK1)
% 1.34/0.83      | ~ v1_funct_1(X1_52)
% 1.34/0.83      | ~ v1_relat_1(X1_52)
% 1.34/0.83      | k1_funct_1(X1_52,k1_funct_1(sK3,X0_52)) = k1_funct_1(k5_relat_1(sK3,X1_52),X0_52)
% 1.34/0.83      | ~ sP0_iProver_split ),
% 1.34/0.83      inference(splitting,
% 1.34/0.83                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.34/0.83                [c_526]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1538,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0_52,sK1)
% 1.34/0.83      | ~ v1_funct_1(sK4)
% 1.34/0.83      | ~ v1_relat_1(sK4)
% 1.34/0.83      | ~ sP0_iProver_split
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,X0_52)) = k1_funct_1(k5_relat_1(sK3,sK4),X0_52) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_543]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1548,plain,
% 1.34/0.83      ( ~ m1_subset_1(sK5,sK1)
% 1.34/0.83      | ~ v1_funct_1(sK4)
% 1.34/0.83      | ~ v1_relat_1(sK4)
% 1.34/0.83      | ~ sP0_iProver_split
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_1538]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1459,plain,
% 1.34/0.83      ( sK5 = sK5 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_548]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_6,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.34/0.83      | ~ v1_relat_1(X1)
% 1.34/0.83      | v1_relat_1(X0) ),
% 1.34/0.83      inference(cnf_transformation,[],[f34]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_538,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 1.34/0.83      | ~ v1_relat_1(X1_52)
% 1.34/0.83      | v1_relat_1(X0_52) ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_6]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1045,plain,
% 1.34/0.83      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 1.34/0.83      | v1_relat_1(X0_52)
% 1.34/0.83      | ~ v1_relat_1(k2_zfmisc_1(X1_52,X2_52)) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_538]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1331,plain,
% 1.34/0.83      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.34/0.83      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
% 1.34/0.83      | v1_relat_1(sK4) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_1045]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1149,plain,
% 1.34/0.83      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_548]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1097,plain,
% 1.34/0.83      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != X0_52
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != X0_52
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_549]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1148,plain,
% 1.34/0.83      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)
% 1.34/0.83      | k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_1097]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1,plain,
% 1.34/0.83      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 1.34/0.83      inference(cnf_transformation,[],[f29]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_541,plain,
% 1.34/0.83      ( ~ v1_xboole_0(X0_52) | k1_xboole_0 = X0_52 ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_1]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_1042,plain,
% 1.34/0.83      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 1.34/0.83      inference(instantiation,[status(thm)],[c_541]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_544,plain,
% 1.34/0.83      ( v1_xboole_0(sK1) | sP0_iProver_split | k1_xboole_0 = sK2 ),
% 1.34/0.83      inference(splitting,
% 1.34/0.83                [splitting(split),new_symbols(definition,[])],
% 1.34/0.83                [c_526]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_12,negated_conjecture,
% 1.34/0.83      ( k1_xboole_0 != sK1 ),
% 1.34/0.83      inference(cnf_transformation,[],[f47]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_534,negated_conjecture,
% 1.34/0.83      ( k1_xboole_0 != sK1 ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_12]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_11,negated_conjecture,
% 1.34/0.83      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 1.34/0.83      inference(cnf_transformation,[],[f48]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_535,negated_conjecture,
% 1.34/0.83      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 1.34/0.83      inference(subtyping,[status(esa)],[c_11]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_14,negated_conjecture,
% 1.34/0.83      ( m1_subset_1(sK5,sK1) ),
% 1.34/0.83      inference(cnf_transformation,[],[f45]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(c_22,plain,
% 1.34/0.83      ( v1_funct_1(sK3) = iProver_top ),
% 1.34/0.83      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.34/0.83  
% 1.34/0.83  cnf(contradiction,plain,
% 1.34/0.83      ( $false ),
% 1.34/0.83      inference(minisat,
% 1.34/0.83                [status(thm)],
% 1.34/0.83                [c_1784,c_1726,c_1555,c_1549,c_1548,c_1459,c_1331,c_1329,
% 1.34/0.83                 c_1149,c_1148,c_1072,c_1042,c_544,c_534,c_535,c_579,c_0,
% 1.34/0.83                 c_14,c_15,c_16,c_22,c_20]) ).
% 1.34/0.83  
% 1.34/0.83  
% 1.34/0.83  % SZS output end CNFRefutation for theBenchmark.p
% 1.34/0.83  
% 1.34/0.83  ------                               Statistics
% 1.34/0.83  
% 1.34/0.83  ------ General
% 1.34/0.83  
% 1.34/0.83  abstr_ref_over_cycles:                  0
% 1.34/0.83  abstr_ref_under_cycles:                 0
% 1.34/0.83  gc_basic_clause_elim:                   0
% 1.34/0.83  forced_gc_time:                         0
% 1.34/0.83  parsing_time:                           0.006
% 1.34/0.83  unif_index_cands_time:                  0.
% 1.34/0.83  unif_index_add_time:                    0.
% 1.34/0.83  orderings_time:                         0.
% 1.34/0.83  out_proof_time:                         0.013
% 1.34/0.83  total_time:                             0.072
% 1.34/0.83  num_of_symbols:                         57
% 1.34/0.83  num_of_terms:                           1850
% 1.34/0.83  
% 1.34/0.83  ------ Preprocessing
% 1.34/0.83  
% 1.34/0.83  num_of_splits:                          1
% 1.34/0.83  num_of_split_atoms:                     1
% 1.34/0.83  num_of_reused_defs:                     0
% 1.34/0.83  num_eq_ax_congr_red:                    16
% 1.34/0.83  num_of_sem_filtered_clauses:            1
% 1.34/0.83  num_of_subtypes:                        3
% 1.34/0.83  monotx_restored_types:                  1
% 1.34/0.83  sat_num_of_epr_types:                   0
% 1.34/0.83  sat_num_of_non_cyclic_types:            0
% 1.34/0.83  sat_guarded_non_collapsed_types:        0
% 1.34/0.83  num_pure_diseq_elim:                    0
% 1.34/0.83  simp_replaced_by:                       0
% 1.34/0.83  res_preprocessed:                       112
% 1.34/0.83  prep_upred:                             0
% 1.34/0.83  prep_unflattend:                        8
% 1.34/0.83  smt_new_axioms:                         0
% 1.34/0.83  pred_elim_cands:                        5
% 1.34/0.83  pred_elim:                              2
% 1.34/0.83  pred_elim_cl:                           3
% 1.34/0.83  pred_elim_cycles:                       5
% 1.34/0.83  merged_defs:                            0
% 1.34/0.83  merged_defs_ncl:                        0
% 1.34/0.83  bin_hyper_res:                          0
% 1.34/0.83  prep_cycles:                            4
% 1.34/0.83  pred_elim_time:                         0.003
% 1.34/0.83  splitting_time:                         0.
% 1.34/0.83  sem_filter_time:                        0.
% 1.34/0.83  monotx_time:                            0.
% 1.34/0.83  subtype_inf_time:                       0.001
% 1.34/0.83  
% 1.34/0.83  ------ Problem properties
% 1.34/0.83  
% 1.34/0.83  clauses:                                19
% 1.34/0.83  conjectures:                            9
% 1.34/0.83  epr:                                    10
% 1.34/0.83  horn:                                   17
% 1.34/0.83  ground:                                 11
% 1.34/0.83  unary:                                  11
% 1.34/0.83  binary:                                 1
% 1.34/0.83  lits:                                   40
% 1.34/0.83  lits_eq:                                8
% 1.34/0.83  fd_pure:                                0
% 1.34/0.83  fd_pseudo:                              0
% 1.34/0.83  fd_cond:                                1
% 1.34/0.83  fd_pseudo_cond:                         0
% 1.34/0.83  ac_symbols:                             0
% 1.34/0.83  
% 1.34/0.83  ------ Propositional Solver
% 1.34/0.83  
% 1.34/0.83  prop_solver_calls:                      26
% 1.34/0.83  prop_fast_solver_calls:                 686
% 1.34/0.83  smt_solver_calls:                       0
% 1.34/0.83  smt_fast_solver_calls:                  0
% 1.34/0.83  prop_num_of_clauses:                    493
% 1.34/0.84  prop_preprocess_simplified:             2739
% 1.34/0.84  prop_fo_subsumed:                       18
% 1.34/0.84  prop_solver_time:                       0.
% 1.34/0.84  smt_solver_time:                        0.
% 1.34/0.84  smt_fast_solver_time:                   0.
% 1.34/0.84  prop_fast_solver_time:                  0.
% 1.34/0.84  prop_unsat_core_time:                   0.
% 1.34/0.84  
% 1.34/0.84  ------ QBF
% 1.34/0.84  
% 1.34/0.84  qbf_q_res:                              0
% 1.34/0.84  qbf_num_tautologies:                    0
% 1.34/0.84  qbf_prep_cycles:                        0
% 1.34/0.84  
% 1.34/0.84  ------ BMC1
% 1.34/0.84  
% 1.34/0.84  bmc1_current_bound:                     -1
% 1.34/0.84  bmc1_last_solved_bound:                 -1
% 1.34/0.84  bmc1_unsat_core_size:                   -1
% 1.34/0.84  bmc1_unsat_core_parents_size:           -1
% 1.34/0.84  bmc1_merge_next_fun:                    0
% 1.34/0.84  bmc1_unsat_core_clauses_time:           0.
% 1.34/0.84  
% 1.34/0.84  ------ Instantiation
% 1.34/0.84  
% 1.34/0.84  inst_num_of_clauses:                    161
% 1.34/0.84  inst_num_in_passive:                    22
% 1.34/0.84  inst_num_in_active:                     131
% 1.34/0.84  inst_num_in_unprocessed:                8
% 1.34/0.84  inst_num_of_loops:                      150
% 1.34/0.84  inst_num_of_learning_restarts:          0
% 1.34/0.84  inst_num_moves_active_passive:          16
% 1.34/0.84  inst_lit_activity:                      0
% 1.34/0.84  inst_lit_activity_moves:                0
% 1.34/0.84  inst_num_tautologies:                   0
% 1.34/0.84  inst_num_prop_implied:                  0
% 1.34/0.84  inst_num_existing_simplified:           0
% 1.34/0.84  inst_num_eq_res_simplified:             0
% 1.34/0.84  inst_num_child_elim:                    0
% 1.34/0.84  inst_num_of_dismatching_blockings:      14
% 1.34/0.84  inst_num_of_non_proper_insts:           145
% 1.34/0.84  inst_num_of_duplicates:                 0
% 1.34/0.84  inst_inst_num_from_inst_to_res:         0
% 1.34/0.84  inst_dismatching_checking_time:         0.
% 1.34/0.84  
% 1.34/0.84  ------ Resolution
% 1.34/0.84  
% 1.34/0.84  res_num_of_clauses:                     0
% 1.34/0.84  res_num_in_passive:                     0
% 1.34/0.84  res_num_in_active:                      0
% 1.34/0.84  res_num_of_loops:                       116
% 1.34/0.84  res_forward_subset_subsumed:            41
% 1.34/0.84  res_backward_subset_subsumed:           0
% 1.34/0.84  res_forward_subsumed:                   0
% 1.34/0.84  res_backward_subsumed:                  0
% 1.34/0.84  res_forward_subsumption_resolution:     0
% 1.34/0.84  res_backward_subsumption_resolution:    0
% 1.34/0.84  res_clause_to_clause_subsumption:       54
% 1.34/0.84  res_orphan_elimination:                 0
% 1.34/0.84  res_tautology_del:                      26
% 1.34/0.84  res_num_eq_res_simplified:              0
% 1.34/0.84  res_num_sel_changes:                    0
% 1.34/0.84  res_moves_from_active_to_pass:          0
% 1.34/0.84  
% 1.34/0.84  ------ Superposition
% 1.34/0.84  
% 1.34/0.84  sup_time_total:                         0.
% 1.34/0.84  sup_time_generating:                    0.
% 1.34/0.84  sup_time_sim_full:                      0.
% 1.34/0.84  sup_time_sim_immed:                     0.
% 1.34/0.84  
% 1.34/0.84  sup_num_of_clauses:                     36
% 1.34/0.84  sup_num_in_active:                      27
% 1.34/0.84  sup_num_in_passive:                     9
% 1.34/0.84  sup_num_of_loops:                       28
% 1.34/0.84  sup_fw_superposition:                   19
% 1.34/0.84  sup_bw_superposition:                   2
% 1.34/0.84  sup_immediate_simplified:               2
% 1.34/0.84  sup_given_eliminated:                   0
% 1.34/0.84  comparisons_done:                       0
% 1.34/0.84  comparisons_avoided:                    0
% 1.34/0.84  
% 1.34/0.84  ------ Simplifications
% 1.34/0.84  
% 1.34/0.84  
% 1.34/0.84  sim_fw_subset_subsumed:                 1
% 1.34/0.84  sim_bw_subset_subsumed:                 2
% 1.34/0.84  sim_fw_subsumed:                        0
% 1.34/0.84  sim_bw_subsumed:                        0
% 1.34/0.84  sim_fw_subsumption_res:                 0
% 1.34/0.84  sim_bw_subsumption_res:                 0
% 1.34/0.84  sim_tautology_del:                      1
% 1.34/0.84  sim_eq_tautology_del:                   1
% 1.34/0.84  sim_eq_res_simp:                        0
% 1.34/0.84  sim_fw_demodulated:                     1
% 1.34/0.84  sim_bw_demodulated:                     0
% 1.34/0.84  sim_light_normalised:                   0
% 1.34/0.84  sim_joinable_taut:                      0
% 1.34/0.84  sim_joinable_simp:                      0
% 1.34/0.84  sim_ac_normalised:                      0
% 1.34/0.84  sim_smt_subsumption:                    0
% 1.34/0.84  
%------------------------------------------------------------------------------
