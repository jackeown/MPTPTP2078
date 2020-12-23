%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:37 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 435 expanded)
%              Number of clauses        :   74 ( 109 expanded)
%              Number of leaves         :   19 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :  508 (3276 expanded)
%              Number of equality atoms :  162 ( 835 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
            ( k1_funct_1(sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                ( k1_funct_1(X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5)
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

fof(f38,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f37,f36,f35,f34])).

fof(f56,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_670,plain,
    ( X0 != X1
    | X2 != X3
    | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
    theory(equality)).

cnf(c_3232,plain,
    ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) != k5_relat_1(sK5,sK6)
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(k5_relat_1(sK5,sK6),sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_657,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1656,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != X0
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != X0 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_2709,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k1_funct_1(k5_relat_1(sK5,sK6),sK7)
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k5_relat_1(sK5,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_1656])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2264,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1582,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2263,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1582])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1045,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1047,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1050,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1751,plain,
    ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1050])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2140,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1751,c_28])).

cnf(c_2141,plain,
    ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2140])).

cnf(c_2150,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_2141])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1049,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_368,plain,
    ( ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_22,c_20])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
    | k1_xboole_0 = sK4 ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_1041,plain,
    ( k1_partfun1(sK3,sK4,sK4,X0,sK5,X1) = k8_funct_2(sK3,sK4,X0,sK5,X1)
    | k1_xboole_0 = sK4
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_1482,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | sK4 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1049,c_1041])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_48,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_52,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_322,plain,
    ( sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_1208,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,sK6))
    | ~ v1_funct_1(sK6)
    | k1_partfun1(sK3,sK4,sK4,X0,sK5,sK6) = k8_funct_2(sK3,sK4,X0,sK5,sK6)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_1426,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    | ~ v1_funct_1(sK6)
    | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_1431,plain,
    ( X0 != X1
    | X0 = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_1432,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_1589,plain,
    ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1482,c_19,c_18,c_16,c_48,c_52,c_322,c_1426,c_1432])).

cnf(c_2153,plain,
    ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2150,c_1589])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1218,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1862,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1310,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1742,plain,
    ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_337,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r2_hidden(X0,sK3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,X1),X0)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_341,plain,
    ( ~ v1_funct_1(X1)
    | ~ r2_hidden(X0,sK3)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,X1),X0)
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_22,c_20])).

cnf(c_342,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,X1),X0)
    | k1_xboole_0 = sK4 ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_1196,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,sK6),X0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_1538,plain,
    ( ~ r2_hidden(sK7,sK3)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(k5_relat_1(sK5,sK6),sK7)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1505,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_656,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1398,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_1262,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != X0
    | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != X0
    | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_1397,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
    | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1346,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1259,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1244,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_14,negated_conjecture,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3232,c_2709,c_2264,c_2263,c_2153,c_1862,c_1742,c_1538,c_1505,c_1432,c_1398,c_1397,c_1346,c_1259,c_1244,c_1221,c_322,c_5,c_52,c_48,c_14,c_15,c_17,c_18,c_19,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:57:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.99/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/0.94  
% 1.99/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.94  
% 1.99/0.94  ------  iProver source info
% 1.99/0.94  
% 1.99/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.94  git: non_committed_changes: false
% 1.99/0.94  git: last_make_outside_of_git: false
% 1.99/0.94  
% 1.99/0.94  ------ 
% 1.99/0.94  
% 1.99/0.94  ------ Input Options
% 1.99/0.94  
% 1.99/0.94  --out_options                           all
% 1.99/0.94  --tptp_safe_out                         true
% 1.99/0.94  --problem_path                          ""
% 1.99/0.94  --include_path                          ""
% 1.99/0.94  --clausifier                            res/vclausify_rel
% 1.99/0.94  --clausifier_options                    --mode clausify
% 1.99/0.94  --stdin                                 false
% 1.99/0.94  --stats_out                             all
% 1.99/0.94  
% 1.99/0.94  ------ General Options
% 1.99/0.94  
% 1.99/0.94  --fof                                   false
% 1.99/0.94  --time_out_real                         305.
% 1.99/0.94  --time_out_virtual                      -1.
% 1.99/0.94  --symbol_type_check                     false
% 1.99/0.94  --clausify_out                          false
% 1.99/0.94  --sig_cnt_out                           false
% 1.99/0.94  --trig_cnt_out                          false
% 1.99/0.94  --trig_cnt_out_tolerance                1.
% 1.99/0.94  --trig_cnt_out_sk_spl                   false
% 1.99/0.94  --abstr_cl_out                          false
% 1.99/0.94  
% 1.99/0.94  ------ Global Options
% 1.99/0.94  
% 1.99/0.94  --schedule                              default
% 1.99/0.94  --add_important_lit                     false
% 1.99/0.94  --prop_solver_per_cl                    1000
% 1.99/0.94  --min_unsat_core                        false
% 1.99/0.94  --soft_assumptions                      false
% 1.99/0.94  --soft_lemma_size                       3
% 1.99/0.94  --prop_impl_unit_size                   0
% 1.99/0.94  --prop_impl_unit                        []
% 1.99/0.94  --share_sel_clauses                     true
% 1.99/0.94  --reset_solvers                         false
% 1.99/0.94  --bc_imp_inh                            [conj_cone]
% 1.99/0.94  --conj_cone_tolerance                   3.
% 1.99/0.94  --extra_neg_conj                        none
% 1.99/0.94  --large_theory_mode                     true
% 1.99/0.94  --prolific_symb_bound                   200
% 1.99/0.94  --lt_threshold                          2000
% 1.99/0.94  --clause_weak_htbl                      true
% 1.99/0.94  --gc_record_bc_elim                     false
% 1.99/0.94  
% 1.99/0.94  ------ Preprocessing Options
% 1.99/0.94  
% 1.99/0.94  --preprocessing_flag                    true
% 1.99/0.94  --time_out_prep_mult                    0.1
% 1.99/0.94  --splitting_mode                        input
% 1.99/0.94  --splitting_grd                         true
% 1.99/0.94  --splitting_cvd                         false
% 1.99/0.94  --splitting_cvd_svl                     false
% 1.99/0.94  --splitting_nvd                         32
% 1.99/0.94  --sub_typing                            true
% 1.99/0.94  --prep_gs_sim                           true
% 1.99/0.94  --prep_unflatten                        true
% 1.99/0.94  --prep_res_sim                          true
% 1.99/0.94  --prep_upred                            true
% 1.99/0.94  --prep_sem_filter                       exhaustive
% 1.99/0.94  --prep_sem_filter_out                   false
% 1.99/0.94  --pred_elim                             true
% 1.99/0.94  --res_sim_input                         true
% 1.99/0.94  --eq_ax_congr_red                       true
% 1.99/0.94  --pure_diseq_elim                       true
% 1.99/0.94  --brand_transform                       false
% 1.99/0.94  --non_eq_to_eq                          false
% 1.99/0.94  --prep_def_merge                        true
% 1.99/0.94  --prep_def_merge_prop_impl              false
% 1.99/0.94  --prep_def_merge_mbd                    true
% 1.99/0.94  --prep_def_merge_tr_red                 false
% 1.99/0.94  --prep_def_merge_tr_cl                  false
% 1.99/0.94  --smt_preprocessing                     true
% 1.99/0.94  --smt_ac_axioms                         fast
% 1.99/0.94  --preprocessed_out                      false
% 1.99/0.94  --preprocessed_stats                    false
% 1.99/0.94  
% 1.99/0.94  ------ Abstraction refinement Options
% 1.99/0.94  
% 1.99/0.94  --abstr_ref                             []
% 1.99/0.94  --abstr_ref_prep                        false
% 1.99/0.94  --abstr_ref_until_sat                   false
% 1.99/0.94  --abstr_ref_sig_restrict                funpre
% 1.99/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.94  --abstr_ref_under                       []
% 1.99/0.94  
% 1.99/0.94  ------ SAT Options
% 1.99/0.94  
% 1.99/0.94  --sat_mode                              false
% 1.99/0.94  --sat_fm_restart_options                ""
% 1.99/0.94  --sat_gr_def                            false
% 1.99/0.94  --sat_epr_types                         true
% 1.99/0.94  --sat_non_cyclic_types                  false
% 1.99/0.94  --sat_finite_models                     false
% 1.99/0.94  --sat_fm_lemmas                         false
% 1.99/0.94  --sat_fm_prep                           false
% 1.99/0.94  --sat_fm_uc_incr                        true
% 1.99/0.94  --sat_out_model                         small
% 1.99/0.94  --sat_out_clauses                       false
% 1.99/0.94  
% 1.99/0.94  ------ QBF Options
% 1.99/0.94  
% 1.99/0.94  --qbf_mode                              false
% 1.99/0.94  --qbf_elim_univ                         false
% 1.99/0.94  --qbf_dom_inst                          none
% 1.99/0.94  --qbf_dom_pre_inst                      false
% 1.99/0.94  --qbf_sk_in                             false
% 1.99/0.94  --qbf_pred_elim                         true
% 1.99/0.94  --qbf_split                             512
% 1.99/0.94  
% 1.99/0.94  ------ BMC1 Options
% 1.99/0.94  
% 1.99/0.94  --bmc1_incremental                      false
% 1.99/0.94  --bmc1_axioms                           reachable_all
% 1.99/0.94  --bmc1_min_bound                        0
% 1.99/0.94  --bmc1_max_bound                        -1
% 1.99/0.94  --bmc1_max_bound_default                -1
% 1.99/0.94  --bmc1_symbol_reachability              true
% 1.99/0.94  --bmc1_property_lemmas                  false
% 1.99/0.94  --bmc1_k_induction                      false
% 1.99/0.94  --bmc1_non_equiv_states                 false
% 1.99/0.94  --bmc1_deadlock                         false
% 1.99/0.94  --bmc1_ucm                              false
% 1.99/0.94  --bmc1_add_unsat_core                   none
% 1.99/0.94  --bmc1_unsat_core_children              false
% 1.99/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.94  --bmc1_out_stat                         full
% 1.99/0.94  --bmc1_ground_init                      false
% 1.99/0.94  --bmc1_pre_inst_next_state              false
% 1.99/0.94  --bmc1_pre_inst_state                   false
% 1.99/0.94  --bmc1_pre_inst_reach_state             false
% 1.99/0.94  --bmc1_out_unsat_core                   false
% 1.99/0.94  --bmc1_aig_witness_out                  false
% 1.99/0.94  --bmc1_verbose                          false
% 1.99/0.94  --bmc1_dump_clauses_tptp                false
% 1.99/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.94  --bmc1_dump_file                        -
% 1.99/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.94  --bmc1_ucm_extend_mode                  1
% 1.99/0.94  --bmc1_ucm_init_mode                    2
% 1.99/0.94  --bmc1_ucm_cone_mode                    none
% 1.99/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.94  --bmc1_ucm_relax_model                  4
% 1.99/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.94  --bmc1_ucm_layered_model                none
% 1.99/0.94  --bmc1_ucm_max_lemma_size               10
% 1.99/0.94  
% 1.99/0.94  ------ AIG Options
% 1.99/0.94  
% 1.99/0.94  --aig_mode                              false
% 1.99/0.94  
% 1.99/0.94  ------ Instantiation Options
% 1.99/0.94  
% 1.99/0.94  --instantiation_flag                    true
% 1.99/0.94  --inst_sos_flag                         false
% 1.99/0.94  --inst_sos_phase                        true
% 1.99/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.94  --inst_lit_sel_side                     num_symb
% 1.99/0.94  --inst_solver_per_active                1400
% 1.99/0.94  --inst_solver_calls_frac                1.
% 1.99/0.94  --inst_passive_queue_type               priority_queues
% 1.99/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.94  --inst_passive_queues_freq              [25;2]
% 1.99/0.94  --inst_dismatching                      true
% 1.99/0.94  --inst_eager_unprocessed_to_passive     true
% 1.99/0.94  --inst_prop_sim_given                   true
% 1.99/0.94  --inst_prop_sim_new                     false
% 1.99/0.94  --inst_subs_new                         false
% 1.99/0.94  --inst_eq_res_simp                      false
% 1.99/0.94  --inst_subs_given                       false
% 1.99/0.94  --inst_orphan_elimination               true
% 1.99/0.94  --inst_learning_loop_flag               true
% 1.99/0.94  --inst_learning_start                   3000
% 1.99/0.94  --inst_learning_factor                  2
% 1.99/0.94  --inst_start_prop_sim_after_learn       3
% 1.99/0.94  --inst_sel_renew                        solver
% 1.99/0.94  --inst_lit_activity_flag                true
% 1.99/0.94  --inst_restr_to_given                   false
% 1.99/0.94  --inst_activity_threshold               500
% 1.99/0.94  --inst_out_proof                        true
% 1.99/0.94  
% 1.99/0.94  ------ Resolution Options
% 1.99/0.94  
% 1.99/0.94  --resolution_flag                       true
% 1.99/0.94  --res_lit_sel                           adaptive
% 1.99/0.94  --res_lit_sel_side                      none
% 1.99/0.94  --res_ordering                          kbo
% 1.99/0.94  --res_to_prop_solver                    active
% 1.99/0.94  --res_prop_simpl_new                    false
% 1.99/0.94  --res_prop_simpl_given                  true
% 1.99/0.94  --res_passive_queue_type                priority_queues
% 1.99/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.94  --res_passive_queues_freq               [15;5]
% 1.99/0.94  --res_forward_subs                      full
% 1.99/0.94  --res_backward_subs                     full
% 1.99/0.94  --res_forward_subs_resolution           true
% 1.99/0.94  --res_backward_subs_resolution          true
% 1.99/0.94  --res_orphan_elimination                true
% 1.99/0.94  --res_time_limit                        2.
% 1.99/0.94  --res_out_proof                         true
% 1.99/0.94  
% 1.99/0.94  ------ Superposition Options
% 1.99/0.94  
% 1.99/0.94  --superposition_flag                    true
% 1.99/0.94  --sup_passive_queue_type                priority_queues
% 1.99/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.94  --demod_completeness_check              fast
% 1.99/0.94  --demod_use_ground                      true
% 1.99/0.94  --sup_to_prop_solver                    passive
% 1.99/0.94  --sup_prop_simpl_new                    true
% 1.99/0.94  --sup_prop_simpl_given                  true
% 1.99/0.94  --sup_fun_splitting                     false
% 1.99/0.94  --sup_smt_interval                      50000
% 1.99/0.94  
% 1.99/0.94  ------ Superposition Simplification Setup
% 1.99/0.94  
% 1.99/0.94  --sup_indices_passive                   []
% 1.99/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.94  --sup_full_bw                           [BwDemod]
% 1.99/0.94  --sup_immed_triv                        [TrivRules]
% 1.99/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.94  --sup_immed_bw_main                     []
% 1.99/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.94  
% 1.99/0.94  ------ Combination Options
% 1.99/0.94  
% 1.99/0.94  --comb_res_mult                         3
% 1.99/0.94  --comb_sup_mult                         2
% 1.99/0.94  --comb_inst_mult                        10
% 1.99/0.94  
% 1.99/0.94  ------ Debug Options
% 1.99/0.94  
% 1.99/0.94  --dbg_backtrace                         false
% 1.99/0.94  --dbg_dump_prop_clauses                 false
% 1.99/0.94  --dbg_dump_prop_clauses_file            -
% 1.99/0.94  --dbg_out_stat                          false
% 1.99/0.94  ------ Parsing...
% 1.99/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.94  
% 1.99/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.99/0.94  
% 1.99/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.94  
% 1.99/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.94  ------ Proving...
% 1.99/0.94  ------ Problem Properties 
% 1.99/0.94  
% 1.99/0.94  
% 1.99/0.94  clauses                                 22
% 1.99/0.94  conjectures                             9
% 1.99/0.94  EPR                                     11
% 1.99/0.94  Horn                                    17
% 1.99/0.94  unary                                   11
% 1.99/0.94  binary                                  5
% 1.99/0.94  lits                                    45
% 1.99/0.94  lits eq                                 8
% 1.99/0.94  fd_pure                                 0
% 1.99/0.94  fd_pseudo                               0
% 1.99/0.94  fd_cond                                 0
% 1.99/0.94  fd_pseudo_cond                          1
% 1.99/0.94  AC symbols                              0
% 1.99/0.94  
% 1.99/0.94  ------ Schedule dynamic 5 is on 
% 1.99/0.94  
% 1.99/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.94  
% 1.99/0.94  
% 1.99/0.94  ------ 
% 1.99/0.94  Current options:
% 1.99/0.94  ------ 
% 1.99/0.94  
% 1.99/0.94  ------ Input Options
% 1.99/0.94  
% 1.99/0.94  --out_options                           all
% 1.99/0.94  --tptp_safe_out                         true
% 1.99/0.94  --problem_path                          ""
% 1.99/0.94  --include_path                          ""
% 1.99/0.94  --clausifier                            res/vclausify_rel
% 1.99/0.94  --clausifier_options                    --mode clausify
% 1.99/0.94  --stdin                                 false
% 1.99/0.94  --stats_out                             all
% 1.99/0.94  
% 1.99/0.94  ------ General Options
% 1.99/0.94  
% 1.99/0.94  --fof                                   false
% 1.99/0.94  --time_out_real                         305.
% 1.99/0.94  --time_out_virtual                      -1.
% 1.99/0.94  --symbol_type_check                     false
% 1.99/0.94  --clausify_out                          false
% 1.99/0.94  --sig_cnt_out                           false
% 1.99/0.94  --trig_cnt_out                          false
% 1.99/0.94  --trig_cnt_out_tolerance                1.
% 1.99/0.94  --trig_cnt_out_sk_spl                   false
% 1.99/0.94  --abstr_cl_out                          false
% 1.99/0.94  
% 1.99/0.94  ------ Global Options
% 1.99/0.94  
% 1.99/0.94  --schedule                              default
% 1.99/0.94  --add_important_lit                     false
% 1.99/0.94  --prop_solver_per_cl                    1000
% 1.99/0.94  --min_unsat_core                        false
% 1.99/0.94  --soft_assumptions                      false
% 1.99/0.94  --soft_lemma_size                       3
% 1.99/0.94  --prop_impl_unit_size                   0
% 1.99/0.94  --prop_impl_unit                        []
% 1.99/0.94  --share_sel_clauses                     true
% 1.99/0.94  --reset_solvers                         false
% 1.99/0.94  --bc_imp_inh                            [conj_cone]
% 1.99/0.94  --conj_cone_tolerance                   3.
% 1.99/0.94  --extra_neg_conj                        none
% 1.99/0.94  --large_theory_mode                     true
% 1.99/0.94  --prolific_symb_bound                   200
% 1.99/0.94  --lt_threshold                          2000
% 1.99/0.94  --clause_weak_htbl                      true
% 1.99/0.94  --gc_record_bc_elim                     false
% 1.99/0.94  
% 1.99/0.94  ------ Preprocessing Options
% 1.99/0.94  
% 1.99/0.94  --preprocessing_flag                    true
% 1.99/0.94  --time_out_prep_mult                    0.1
% 1.99/0.94  --splitting_mode                        input
% 1.99/0.94  --splitting_grd                         true
% 1.99/0.94  --splitting_cvd                         false
% 1.99/0.94  --splitting_cvd_svl                     false
% 1.99/0.94  --splitting_nvd                         32
% 1.99/0.94  --sub_typing                            true
% 1.99/0.94  --prep_gs_sim                           true
% 1.99/0.94  --prep_unflatten                        true
% 1.99/0.94  --prep_res_sim                          true
% 1.99/0.94  --prep_upred                            true
% 1.99/0.94  --prep_sem_filter                       exhaustive
% 1.99/0.94  --prep_sem_filter_out                   false
% 1.99/0.94  --pred_elim                             true
% 1.99/0.94  --res_sim_input                         true
% 1.99/0.94  --eq_ax_congr_red                       true
% 1.99/0.94  --pure_diseq_elim                       true
% 1.99/0.94  --brand_transform                       false
% 1.99/0.94  --non_eq_to_eq                          false
% 1.99/0.94  --prep_def_merge                        true
% 1.99/0.94  --prep_def_merge_prop_impl              false
% 1.99/0.94  --prep_def_merge_mbd                    true
% 1.99/0.94  --prep_def_merge_tr_red                 false
% 1.99/0.94  --prep_def_merge_tr_cl                  false
% 1.99/0.94  --smt_preprocessing                     true
% 1.99/0.94  --smt_ac_axioms                         fast
% 1.99/0.94  --preprocessed_out                      false
% 1.99/0.94  --preprocessed_stats                    false
% 1.99/0.94  
% 1.99/0.94  ------ Abstraction refinement Options
% 1.99/0.94  
% 1.99/0.94  --abstr_ref                             []
% 1.99/0.94  --abstr_ref_prep                        false
% 1.99/0.94  --abstr_ref_until_sat                   false
% 1.99/0.94  --abstr_ref_sig_restrict                funpre
% 1.99/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.94  --abstr_ref_under                       []
% 1.99/0.94  
% 1.99/0.94  ------ SAT Options
% 1.99/0.94  
% 1.99/0.94  --sat_mode                              false
% 1.99/0.94  --sat_fm_restart_options                ""
% 1.99/0.94  --sat_gr_def                            false
% 1.99/0.94  --sat_epr_types                         true
% 1.99/0.94  --sat_non_cyclic_types                  false
% 1.99/0.94  --sat_finite_models                     false
% 1.99/0.94  --sat_fm_lemmas                         false
% 1.99/0.94  --sat_fm_prep                           false
% 1.99/0.94  --sat_fm_uc_incr                        true
% 1.99/0.94  --sat_out_model                         small
% 1.99/0.94  --sat_out_clauses                       false
% 1.99/0.94  
% 1.99/0.94  ------ QBF Options
% 1.99/0.94  
% 1.99/0.94  --qbf_mode                              false
% 1.99/0.94  --qbf_elim_univ                         false
% 1.99/0.94  --qbf_dom_inst                          none
% 1.99/0.94  --qbf_dom_pre_inst                      false
% 1.99/0.94  --qbf_sk_in                             false
% 1.99/0.94  --qbf_pred_elim                         true
% 1.99/0.94  --qbf_split                             512
% 1.99/0.94  
% 1.99/0.94  ------ BMC1 Options
% 1.99/0.94  
% 1.99/0.94  --bmc1_incremental                      false
% 1.99/0.94  --bmc1_axioms                           reachable_all
% 1.99/0.94  --bmc1_min_bound                        0
% 1.99/0.94  --bmc1_max_bound                        -1
% 1.99/0.94  --bmc1_max_bound_default                -1
% 1.99/0.94  --bmc1_symbol_reachability              true
% 1.99/0.94  --bmc1_property_lemmas                  false
% 1.99/0.94  --bmc1_k_induction                      false
% 1.99/0.94  --bmc1_non_equiv_states                 false
% 1.99/0.94  --bmc1_deadlock                         false
% 1.99/0.94  --bmc1_ucm                              false
% 1.99/0.94  --bmc1_add_unsat_core                   none
% 1.99/0.94  --bmc1_unsat_core_children              false
% 1.99/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.94  --bmc1_out_stat                         full
% 1.99/0.94  --bmc1_ground_init                      false
% 1.99/0.94  --bmc1_pre_inst_next_state              false
% 1.99/0.94  --bmc1_pre_inst_state                   false
% 1.99/0.94  --bmc1_pre_inst_reach_state             false
% 1.99/0.94  --bmc1_out_unsat_core                   false
% 1.99/0.94  --bmc1_aig_witness_out                  false
% 1.99/0.94  --bmc1_verbose                          false
% 1.99/0.94  --bmc1_dump_clauses_tptp                false
% 1.99/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.94  --bmc1_dump_file                        -
% 1.99/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.94  --bmc1_ucm_extend_mode                  1
% 1.99/0.94  --bmc1_ucm_init_mode                    2
% 1.99/0.94  --bmc1_ucm_cone_mode                    none
% 1.99/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.94  --bmc1_ucm_relax_model                  4
% 1.99/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.94  --bmc1_ucm_layered_model                none
% 1.99/0.94  --bmc1_ucm_max_lemma_size               10
% 1.99/0.94  
% 1.99/0.94  ------ AIG Options
% 1.99/0.94  
% 1.99/0.94  --aig_mode                              false
% 1.99/0.94  
% 1.99/0.94  ------ Instantiation Options
% 1.99/0.94  
% 1.99/0.94  --instantiation_flag                    true
% 1.99/0.94  --inst_sos_flag                         false
% 1.99/0.94  --inst_sos_phase                        true
% 1.99/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.94  --inst_lit_sel_side                     none
% 1.99/0.94  --inst_solver_per_active                1400
% 1.99/0.94  --inst_solver_calls_frac                1.
% 1.99/0.94  --inst_passive_queue_type               priority_queues
% 1.99/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.94  --inst_passive_queues_freq              [25;2]
% 1.99/0.94  --inst_dismatching                      true
% 1.99/0.94  --inst_eager_unprocessed_to_passive     true
% 1.99/0.94  --inst_prop_sim_given                   true
% 1.99/0.94  --inst_prop_sim_new                     false
% 1.99/0.94  --inst_subs_new                         false
% 1.99/0.94  --inst_eq_res_simp                      false
% 1.99/0.94  --inst_subs_given                       false
% 1.99/0.94  --inst_orphan_elimination               true
% 1.99/0.94  --inst_learning_loop_flag               true
% 1.99/0.94  --inst_learning_start                   3000
% 1.99/0.94  --inst_learning_factor                  2
% 1.99/0.94  --inst_start_prop_sim_after_learn       3
% 1.99/0.94  --inst_sel_renew                        solver
% 1.99/0.94  --inst_lit_activity_flag                true
% 1.99/0.94  --inst_restr_to_given                   false
% 1.99/0.94  --inst_activity_threshold               500
% 1.99/0.94  --inst_out_proof                        true
% 1.99/0.94  
% 1.99/0.94  ------ Resolution Options
% 1.99/0.94  
% 1.99/0.94  --resolution_flag                       false
% 1.99/0.94  --res_lit_sel                           adaptive
% 1.99/0.94  --res_lit_sel_side                      none
% 1.99/0.94  --res_ordering                          kbo
% 1.99/0.94  --res_to_prop_solver                    active
% 1.99/0.94  --res_prop_simpl_new                    false
% 1.99/0.94  --res_prop_simpl_given                  true
% 1.99/0.94  --res_passive_queue_type                priority_queues
% 1.99/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.94  --res_passive_queues_freq               [15;5]
% 1.99/0.94  --res_forward_subs                      full
% 1.99/0.94  --res_backward_subs                     full
% 1.99/0.94  --res_forward_subs_resolution           true
% 1.99/0.94  --res_backward_subs_resolution          true
% 1.99/0.94  --res_orphan_elimination                true
% 1.99/0.94  --res_time_limit                        2.
% 1.99/0.94  --res_out_proof                         true
% 1.99/0.94  
% 1.99/0.94  ------ Superposition Options
% 1.99/0.94  
% 1.99/0.94  --superposition_flag                    true
% 1.99/0.94  --sup_passive_queue_type                priority_queues
% 1.99/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.94  --demod_completeness_check              fast
% 1.99/0.94  --demod_use_ground                      true
% 1.99/0.94  --sup_to_prop_solver                    passive
% 1.99/0.94  --sup_prop_simpl_new                    true
% 1.99/0.94  --sup_prop_simpl_given                  true
% 1.99/0.94  --sup_fun_splitting                     false
% 1.99/0.94  --sup_smt_interval                      50000
% 1.99/0.94  
% 1.99/0.94  ------ Superposition Simplification Setup
% 1.99/0.94  
% 1.99/0.94  --sup_indices_passive                   []
% 1.99/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.94  --sup_full_bw                           [BwDemod]
% 1.99/0.94  --sup_immed_triv                        [TrivRules]
% 1.99/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.94  --sup_immed_bw_main                     []
% 1.99/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.94  
% 1.99/0.94  ------ Combination Options
% 1.99/0.94  
% 1.99/0.94  --comb_res_mult                         3
% 1.99/0.94  --comb_sup_mult                         2
% 1.99/0.94  --comb_inst_mult                        10
% 1.99/0.94  
% 1.99/0.94  ------ Debug Options
% 1.99/0.94  
% 1.99/0.94  --dbg_backtrace                         false
% 1.99/0.94  --dbg_dump_prop_clauses                 false
% 1.99/0.94  --dbg_dump_prop_clauses_file            -
% 1.99/0.94  --dbg_out_stat                          false
% 1.99/0.94  
% 1.99/0.94  
% 1.99/0.94  
% 1.99/0.94  
% 1.99/0.94  ------ Proving...
% 1.99/0.94  
% 1.99/0.94  
% 1.99/0.94  % SZS status Theorem for theBenchmark.p
% 1.99/0.94  
% 1.99/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/0.94  
% 1.99/0.94  fof(f4,axiom,(
% 1.99/0.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.99/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.94  
% 1.99/0.94  fof(f32,plain,(
% 1.99/0.94    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.94    inference(nnf_transformation,[],[f4])).
% 1.99/0.94  
% 1.99/0.94  fof(f33,plain,(
% 1.99/0.94    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/0.94    inference(flattening,[],[f32])).
% 1.99/0.94  
% 1.99/0.94  fof(f46,plain,(
% 1.99/0.94    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.99/0.94    inference(cnf_transformation,[],[f33])).
% 1.99/0.94  
% 1.99/0.94  fof(f63,plain,(
% 1.99/0.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.99/0.94    inference(equality_resolution,[],[f46])).
% 1.99/0.94  
% 1.99/0.94  fof(f47,plain,(
% 1.99/0.94    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.99/0.94    inference(cnf_transformation,[],[f33])).
% 1.99/0.94  
% 1.99/0.94  fof(f10,conjecture,(
% 1.99/0.94    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.99/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.94  
% 1.99/0.94  fof(f11,negated_conjecture,(
% 1.99/0.94    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.99/0.94    inference(negated_conjecture,[],[f10])).
% 1.99/0.94  
% 1.99/0.94  fof(f22,plain,(
% 1.99/0.94    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.99/0.94    inference(ennf_transformation,[],[f11])).
% 1.99/0.94  
% 1.99/0.94  fof(f23,plain,(
% 1.99/0.94    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.99/0.94    inference(flattening,[],[f22])).
% 1.99/0.94  
% 1.99/0.94  fof(f37,plain,(
% 1.99/0.94    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 1.99/0.94    introduced(choice_axiom,[])).
% 1.99/0.94  
% 1.99/0.94  fof(f36,plain,(
% 1.99/0.94    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 1.99/0.94    introduced(choice_axiom,[])).
% 1.99/0.94  
% 1.99/0.94  fof(f35,plain,(
% 1.99/0.94    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 1.99/0.94    introduced(choice_axiom,[])).
% 1.99/0.94  
% 1.99/0.94  fof(f34,plain,(
% 1.99/0.94    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 1.99/0.94    introduced(choice_axiom,[])).
% 1.99/0.94  
% 1.99/0.94  fof(f38,plain,(
% 1.99/0.94    (((k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 1.99/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f23,f37,f36,f35,f34])).
% 1.99/0.94  
% 1.99/0.94  fof(f56,plain,(
% 1.99/0.94    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 1.99/0.94    inference(cnf_transformation,[],[f38])).
% 1.99/0.94  
% 1.99/0.94  fof(f58,plain,(
% 1.99/0.94    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f8,axiom,(
% 1.99/0.95    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f18,plain,(
% 1.99/0.95    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.99/0.95    inference(ennf_transformation,[],[f8])).
% 1.99/0.95  
% 1.99/0.95  fof(f19,plain,(
% 1.99/0.95    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.99/0.95    inference(flattening,[],[f18])).
% 1.99/0.95  
% 1.99/0.95  fof(f51,plain,(
% 1.99/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.99/0.95    inference(cnf_transformation,[],[f19])).
% 1.99/0.95  
% 1.99/0.95  fof(f57,plain,(
% 1.99/0.95    v1_funct_1(sK6)),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f60,plain,(
% 1.99/0.95    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f7,axiom,(
% 1.99/0.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f16,plain,(
% 1.99/0.95    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.99/0.95    inference(ennf_transformation,[],[f7])).
% 1.99/0.95  
% 1.99/0.95  fof(f17,plain,(
% 1.99/0.95    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.99/0.95    inference(flattening,[],[f16])).
% 1.99/0.95  
% 1.99/0.95  fof(f50,plain,(
% 1.99/0.95    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.99/0.95    inference(cnf_transformation,[],[f17])).
% 1.99/0.95  
% 1.99/0.95  fof(f55,plain,(
% 1.99/0.95    v1_funct_2(sK5,sK3,sK4)),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f54,plain,(
% 1.99/0.95    v1_funct_1(sK5)),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f45,plain,(
% 1.99/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.99/0.95    inference(cnf_transformation,[],[f33])).
% 1.99/0.95  
% 1.99/0.95  fof(f64,plain,(
% 1.99/0.95    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.99/0.95    inference(equality_resolution,[],[f45])).
% 1.99/0.95  
% 1.99/0.95  fof(f3,axiom,(
% 1.99/0.95    v1_xboole_0(k1_xboole_0)),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f44,plain,(
% 1.99/0.95    v1_xboole_0(k1_xboole_0)),
% 1.99/0.95    inference(cnf_transformation,[],[f3])).
% 1.99/0.95  
% 1.99/0.95  fof(f53,plain,(
% 1.99/0.95    ~v1_xboole_0(sK4)),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f1,axiom,(
% 1.99/0.95    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f24,plain,(
% 1.99/0.95    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.99/0.95    inference(nnf_transformation,[],[f1])).
% 1.99/0.95  
% 1.99/0.95  fof(f25,plain,(
% 1.99/0.95    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.99/0.95    inference(rectify,[],[f24])).
% 1.99/0.95  
% 1.99/0.95  fof(f26,plain,(
% 1.99/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.99/0.95    introduced(choice_axiom,[])).
% 1.99/0.95  
% 1.99/0.95  fof(f27,plain,(
% 1.99/0.95    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.99/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 1.99/0.95  
% 1.99/0.95  fof(f39,plain,(
% 1.99/0.95    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.99/0.95    inference(cnf_transformation,[],[f27])).
% 1.99/0.95  
% 1.99/0.95  fof(f9,axiom,(
% 1.99/0.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1))))),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f20,plain,(
% 1.99/0.95    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.99/0.95    inference(ennf_transformation,[],[f9])).
% 1.99/0.95  
% 1.99/0.95  fof(f21,plain,(
% 1.99/0.95    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.99/0.95    inference(flattening,[],[f20])).
% 1.99/0.95  
% 1.99/0.95  fof(f52,plain,(
% 1.99/0.95    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.99/0.95    inference(cnf_transformation,[],[f21])).
% 1.99/0.95  
% 1.99/0.95  fof(f2,axiom,(
% 1.99/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f12,plain,(
% 1.99/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.99/0.95    inference(ennf_transformation,[],[f2])).
% 1.99/0.95  
% 1.99/0.95  fof(f28,plain,(
% 1.99/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.95    inference(nnf_transformation,[],[f12])).
% 1.99/0.95  
% 1.99/0.95  fof(f29,plain,(
% 1.99/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.95    inference(rectify,[],[f28])).
% 1.99/0.95  
% 1.99/0.95  fof(f30,plain,(
% 1.99/0.95    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.99/0.95    introduced(choice_axiom,[])).
% 1.99/0.95  
% 1.99/0.95  fof(f31,plain,(
% 1.99/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.99/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 1.99/0.95  
% 1.99/0.95  fof(f42,plain,(
% 1.99/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.99/0.95    inference(cnf_transformation,[],[f31])).
% 1.99/0.95  
% 1.99/0.95  fof(f5,axiom,(
% 1.99/0.95    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f13,plain,(
% 1.99/0.95    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.99/0.95    inference(ennf_transformation,[],[f5])).
% 1.99/0.95  
% 1.99/0.95  fof(f14,plain,(
% 1.99/0.95    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.99/0.95    inference(flattening,[],[f13])).
% 1.99/0.95  
% 1.99/0.95  fof(f48,plain,(
% 1.99/0.95    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.99/0.95    inference(cnf_transformation,[],[f14])).
% 1.99/0.95  
% 1.99/0.95  fof(f6,axiom,(
% 1.99/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.99/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.95  
% 1.99/0.95  fof(f15,plain,(
% 1.99/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/0.95    inference(ennf_transformation,[],[f6])).
% 1.99/0.95  
% 1.99/0.95  fof(f49,plain,(
% 1.99/0.95    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/0.95    inference(cnf_transformation,[],[f15])).
% 1.99/0.95  
% 1.99/0.95  fof(f62,plain,(
% 1.99/0.95    k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f61,plain,(
% 1.99/0.95    k1_xboole_0 != sK3),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  fof(f59,plain,(
% 1.99/0.95    m1_subset_1(sK7,sK3)),
% 1.99/0.95    inference(cnf_transformation,[],[f38])).
% 1.99/0.95  
% 1.99/0.95  cnf(c_670,plain,
% 1.99/0.95      ( X0 != X1 | X2 != X3 | k1_funct_1(X0,X2) = k1_funct_1(X1,X3) ),
% 1.99/0.95      theory(equality) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_3232,plain,
% 1.99/0.95      ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) != k5_relat_1(sK5,sK6)
% 1.99/0.95      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(k5_relat_1(sK5,sK6),sK7)
% 1.99/0.95      | sK7 != sK7 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_670]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_657,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1656,plain,
% 1.99/0.95      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != X0
% 1.99/0.95      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != X0 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_657]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_2709,plain,
% 1.99/0.95      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k1_funct_1(k5_relat_1(sK5,sK6),sK7)
% 1.99/0.95      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k5_relat_1(sK5,sK6),sK7) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1656]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_7,plain,
% 1.99/0.95      ( r1_tarski(X0,X0) ),
% 1.99/0.95      inference(cnf_transformation,[],[f63]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_2264,plain,
% 1.99/0.95      ( r1_tarski(sK7,sK7) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_7]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_6,plain,
% 1.99/0.95      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.99/0.95      inference(cnf_transformation,[],[f47]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1582,plain,
% 1.99/0.95      ( ~ r1_tarski(X0,sK7) | ~ r1_tarski(sK7,X0) | sK7 = X0 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_6]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_2263,plain,
% 1.99/0.95      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1582]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_20,negated_conjecture,
% 1.99/0.95      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 1.99/0.95      inference(cnf_transformation,[],[f56]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1045,plain,
% 1.99/0.95      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 1.99/0.95      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_18,negated_conjecture,
% 1.99/0.95      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 1.99/0.95      inference(cnf_transformation,[],[f58]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1047,plain,
% 1.99/0.95      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 1.99/0.95      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_12,plain,
% 1.99/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.99/0.95      | ~ v1_funct_1(X3)
% 1.99/0.95      | ~ v1_funct_1(X0)
% 1.99/0.95      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.99/0.95      inference(cnf_transformation,[],[f51]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1050,plain,
% 1.99/0.95      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 1.99/0.95      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 1.99/0.95      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.99/0.95      | v1_funct_1(X5) != iProver_top
% 1.99/0.95      | v1_funct_1(X4) != iProver_top ),
% 1.99/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1751,plain,
% 1.99/0.95      ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
% 1.99/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.99/0.95      | v1_funct_1(X2) != iProver_top
% 1.99/0.95      | v1_funct_1(sK6) != iProver_top ),
% 1.99/0.95      inference(superposition,[status(thm)],[c_1047,c_1050]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_19,negated_conjecture,
% 1.99/0.95      ( v1_funct_1(sK6) ),
% 1.99/0.95      inference(cnf_transformation,[],[f57]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_28,plain,
% 1.99/0.95      ( v1_funct_1(sK6) = iProver_top ),
% 1.99/0.95      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_2140,plain,
% 1.99/0.95      ( v1_funct_1(X2) != iProver_top
% 1.99/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.99/0.95      | k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6) ),
% 1.99/0.95      inference(global_propositional_subsumption,
% 1.99/0.95                [status(thm)],
% 1.99/0.95                [c_1751,c_28]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_2141,plain,
% 1.99/0.95      ( k1_partfun1(X0,X1,sK4,sK2,X2,sK6) = k5_relat_1(X2,sK6)
% 1.99/0.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.99/0.95      | v1_funct_1(X2) != iProver_top ),
% 1.99/0.95      inference(renaming,[status(thm)],[c_2140]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_2150,plain,
% 1.99/0.95      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
% 1.99/0.95      | v1_funct_1(sK5) != iProver_top ),
% 1.99/0.95      inference(superposition,[status(thm)],[c_1045,c_2141]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_16,negated_conjecture,
% 1.99/0.95      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 1.99/0.95      inference(cnf_transformation,[],[f60]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1049,plain,
% 1.99/0.95      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 1.99/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_11,plain,
% 1.99/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/0.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 1.99/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.95      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 1.99/0.95      | ~ v1_funct_1(X3)
% 1.99/0.95      | ~ v1_funct_1(X0)
% 1.99/0.95      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 1.99/0.95      | k1_xboole_0 = X2 ),
% 1.99/0.95      inference(cnf_transformation,[],[f50]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_21,negated_conjecture,
% 1.99/0.95      ( v1_funct_2(sK5,sK3,sK4) ),
% 1.99/0.95      inference(cnf_transformation,[],[f55]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_363,plain,
% 1.99/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 1.99/0.95      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 1.99/0.95      | ~ v1_funct_1(X3)
% 1.99/0.95      | ~ v1_funct_1(X0)
% 1.99/0.95      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 1.99/0.95      | sK4 != X2
% 1.99/0.95      | sK3 != X1
% 1.99/0.95      | sK5 != X0
% 1.99/0.95      | k1_xboole_0 = X2 ),
% 1.99/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_364,plain,
% 1.99/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 1.99/0.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 1.99/0.95      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 1.99/0.95      | ~ v1_funct_1(X0)
% 1.99/0.95      | ~ v1_funct_1(sK5)
% 1.99/0.95      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(unflattening,[status(thm)],[c_363]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_22,negated_conjecture,
% 1.99/0.95      ( v1_funct_1(sK5) ),
% 1.99/0.95      inference(cnf_transformation,[],[f54]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_368,plain,
% 1.99/0.95      ( ~ v1_funct_1(X0)
% 1.99/0.95      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 1.99/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 1.99/0.95      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(global_propositional_subsumption,
% 1.99/0.95                [status(thm)],
% 1.99/0.95                [c_364,c_22,c_20]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_369,plain,
% 1.99/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 1.99/0.95      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 1.99/0.95      | ~ v1_funct_1(X0)
% 1.99/0.95      | k1_partfun1(sK3,sK4,sK4,X1,sK5,X0) = k8_funct_2(sK3,sK4,X1,sK5,X0)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(renaming,[status(thm)],[c_368]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1041,plain,
% 1.99/0.95      ( k1_partfun1(sK3,sK4,sK4,X0,sK5,X1) = k8_funct_2(sK3,sK4,X0,sK5,X1)
% 1.99/0.95      | k1_xboole_0 = sK4
% 1.99/0.95      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 1.99/0.95      | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 1.99/0.95      | v1_funct_1(X1) != iProver_top ),
% 1.99/0.95      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1482,plain,
% 1.99/0.95      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 1.99/0.95      | sK4 = k1_xboole_0
% 1.99/0.95      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 1.99/0.95      | v1_funct_1(sK6) != iProver_top ),
% 1.99/0.95      inference(superposition,[status(thm)],[c_1049,c_1041]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_8,plain,
% 1.99/0.95      ( r1_tarski(X0,X0) ),
% 1.99/0.95      inference(cnf_transformation,[],[f64]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_48,plain,
% 1.99/0.95      ( r1_tarski(sK4,sK4) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_8]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_52,plain,
% 1.99/0.95      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_6]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_5,plain,
% 1.99/0.95      ( v1_xboole_0(k1_xboole_0) ),
% 1.99/0.95      inference(cnf_transformation,[],[f44]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_23,negated_conjecture,
% 1.99/0.95      ( ~ v1_xboole_0(sK4) ),
% 1.99/0.95      inference(cnf_transformation,[],[f53]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_322,plain,
% 1.99/0.95      ( sK4 != k1_xboole_0 ),
% 1.99/0.95      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1208,plain,
% 1.99/0.95      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0)))
% 1.99/0.95      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,sK6))
% 1.99/0.95      | ~ v1_funct_1(sK6)
% 1.99/0.95      | k1_partfun1(sK3,sK4,sK4,X0,sK5,sK6) = k8_funct_2(sK3,sK4,X0,sK5,sK6)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_369]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1426,plain,
% 1.99/0.95      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 1.99/0.95      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
% 1.99/0.95      | ~ v1_funct_1(sK6)
% 1.99/0.95      | k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1208]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1431,plain,
% 1.99/0.95      ( X0 != X1 | X0 = k1_xboole_0 | k1_xboole_0 != X1 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_657]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1432,plain,
% 1.99/0.95      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1431]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1589,plain,
% 1.99/0.95      ( k1_partfun1(sK3,sK4,sK4,sK2,sK5,sK6) = k8_funct_2(sK3,sK4,sK2,sK5,sK6) ),
% 1.99/0.95      inference(global_propositional_subsumption,
% 1.99/0.95                [status(thm)],
% 1.99/0.95                [c_1482,c_19,c_18,c_16,c_48,c_52,c_322,c_1426,c_1432]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_2153,plain,
% 1.99/0.95      ( k8_funct_2(sK3,sK4,sK2,sK5,sK6) = k5_relat_1(sK5,sK6)
% 1.99/0.95      | v1_funct_1(sK5) != iProver_top ),
% 1.99/0.95      inference(demodulation,[status(thm)],[c_2150,c_1589]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1,plain,
% 1.99/0.95      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.99/0.95      inference(cnf_transformation,[],[f39]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1218,plain,
% 1.99/0.95      ( ~ r2_hidden(X0,k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1862,plain,
% 1.99/0.95      ( ~ r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0)
% 1.99/0.95      | ~ v1_xboole_0(k1_xboole_0) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1218]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1310,plain,
% 1.99/0.95      ( ~ r2_hidden(X0,sK3) | ~ v1_xboole_0(sK3) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1742,plain,
% 1.99/0.95      ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3) | ~ v1_xboole_0(sK3) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1310]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_13,plain,
% 1.99/0.95      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.95      | ~ r2_hidden(X3,X1)
% 1.99/0.95      | ~ v1_funct_1(X4)
% 1.99/0.95      | ~ v1_funct_1(X0)
% 1.99/0.95      | ~ v1_relat_1(X4)
% 1.99/0.95      | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 1.99/0.95      | k1_xboole_0 = X2 ),
% 1.99/0.95      inference(cnf_transformation,[],[f52]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_336,plain,
% 1.99/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.95      | ~ r2_hidden(X3,X1)
% 1.99/0.95      | ~ v1_funct_1(X4)
% 1.99/0.95      | ~ v1_funct_1(X0)
% 1.99/0.95      | ~ v1_relat_1(X4)
% 1.99/0.95      | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
% 1.99/0.95      | sK4 != X2
% 1.99/0.95      | sK3 != X1
% 1.99/0.95      | sK5 != X0
% 1.99/0.95      | k1_xboole_0 = X2 ),
% 1.99/0.95      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_337,plain,
% 1.99/0.95      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 1.99/0.95      | ~ r2_hidden(X0,sK3)
% 1.99/0.95      | ~ v1_funct_1(X1)
% 1.99/0.95      | ~ v1_funct_1(sK5)
% 1.99/0.95      | ~ v1_relat_1(X1)
% 1.99/0.95      | k1_funct_1(X1,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,X1),X0)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(unflattening,[status(thm)],[c_336]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_341,plain,
% 1.99/0.95      ( ~ v1_funct_1(X1)
% 1.99/0.95      | ~ r2_hidden(X0,sK3)
% 1.99/0.95      | ~ v1_relat_1(X1)
% 1.99/0.95      | k1_funct_1(X1,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,X1),X0)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(global_propositional_subsumption,
% 1.99/0.95                [status(thm)],
% 1.99/0.95                [c_337,c_22,c_20]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_342,plain,
% 1.99/0.95      ( ~ r2_hidden(X0,sK3)
% 1.99/0.95      | ~ v1_funct_1(X1)
% 1.99/0.95      | ~ v1_relat_1(X1)
% 1.99/0.95      | k1_funct_1(X1,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,X1),X0)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(renaming,[status(thm)],[c_341]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1196,plain,
% 1.99/0.95      ( ~ r2_hidden(X0,sK3)
% 1.99/0.95      | ~ v1_funct_1(sK6)
% 1.99/0.95      | ~ v1_relat_1(sK6)
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,X0)) = k1_funct_1(k5_relat_1(sK5,sK6),X0)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_342]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1538,plain,
% 1.99/0.95      ( ~ r2_hidden(sK7,sK3)
% 1.99/0.95      | ~ v1_funct_1(sK6)
% 1.99/0.95      | ~ v1_relat_1(sK6)
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(k5_relat_1(sK5,sK6),sK7)
% 1.99/0.95      | k1_xboole_0 = sK4 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1196]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_3,plain,
% 1.99/0.95      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 1.99/0.95      inference(cnf_transformation,[],[f42]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1505,plain,
% 1.99/0.95      ( r1_tarski(k1_xboole_0,sK3)
% 1.99/0.95      | r2_hidden(sK1(k1_xboole_0,sK3),k1_xboole_0) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_3]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_656,plain,( X0 = X0 ),theory(equality) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1398,plain,
% 1.99/0.95      ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_656]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1262,plain,
% 1.99/0.95      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != X0
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != X0
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_657]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1397,plain,
% 1.99/0.95      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
% 1.99/0.95      | k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_1262]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1346,plain,
% 1.99/0.95      ( r1_tarski(sK3,k1_xboole_0)
% 1.99/0.95      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_3]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1259,plain,
% 1.99/0.95      ( ~ r1_tarski(sK3,k1_xboole_0)
% 1.99/0.95      | ~ r1_tarski(k1_xboole_0,sK3)
% 1.99/0.95      | k1_xboole_0 = sK3 ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_6]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_9,plain,
% 1.99/0.95      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.99/0.95      inference(cnf_transformation,[],[f48]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1244,plain,
% 1.99/0.95      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_9]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_10,plain,
% 1.99/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/0.95      | v1_relat_1(X0) ),
% 1.99/0.95      inference(cnf_transformation,[],[f49]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_1221,plain,
% 1.99/0.95      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 1.99/0.95      | v1_relat_1(sK6) ),
% 1.99/0.95      inference(instantiation,[status(thm)],[c_10]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_14,negated_conjecture,
% 1.99/0.95      ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 1.99/0.95      inference(cnf_transformation,[],[f62]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_15,negated_conjecture,
% 1.99/0.95      ( k1_xboole_0 != sK3 ),
% 1.99/0.95      inference(cnf_transformation,[],[f61]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_17,negated_conjecture,
% 1.99/0.95      ( m1_subset_1(sK7,sK3) ),
% 1.99/0.95      inference(cnf_transformation,[],[f59]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(c_25,plain,
% 1.99/0.95      ( v1_funct_1(sK5) = iProver_top ),
% 1.99/0.95      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.99/0.95  
% 1.99/0.95  cnf(contradiction,plain,
% 1.99/0.95      ( $false ),
% 1.99/0.95      inference(minisat,
% 1.99/0.95                [status(thm)],
% 1.99/0.95                [c_3232,c_2709,c_2264,c_2263,c_2153,c_1862,c_1742,c_1538,
% 1.99/0.95                 c_1505,c_1432,c_1398,c_1397,c_1346,c_1259,c_1244,c_1221,
% 1.99/0.95                 c_322,c_5,c_52,c_48,c_14,c_15,c_17,c_18,c_19,c_25]) ).
% 1.99/0.95  
% 1.99/0.95  
% 1.99/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/0.95  
% 1.99/0.95  ------                               Statistics
% 1.99/0.95  
% 1.99/0.95  ------ General
% 1.99/0.95  
% 1.99/0.95  abstr_ref_over_cycles:                  0
% 1.99/0.95  abstr_ref_under_cycles:                 0
% 1.99/0.95  gc_basic_clause_elim:                   0
% 1.99/0.95  forced_gc_time:                         0
% 1.99/0.95  parsing_time:                           0.011
% 1.99/0.95  unif_index_cands_time:                  0.
% 1.99/0.95  unif_index_add_time:                    0.
% 1.99/0.95  orderings_time:                         0.
% 1.99/0.95  out_proof_time:                         0.014
% 1.99/0.95  total_time:                             0.132
% 1.99/0.95  num_of_symbols:                         55
% 1.99/0.95  num_of_terms:                           2695
% 1.99/0.95  
% 1.99/0.95  ------ Preprocessing
% 1.99/0.95  
% 1.99/0.95  num_of_splits:                          0
% 1.99/0.95  num_of_split_atoms:                     0
% 1.99/0.95  num_of_reused_defs:                     0
% 1.99/0.95  num_eq_ax_congr_red:                    27
% 1.99/0.95  num_of_sem_filtered_clauses:            1
% 1.99/0.95  num_of_subtypes:                        0
% 1.99/0.95  monotx_restored_types:                  0
% 1.99/0.95  sat_num_of_epr_types:                   0
% 1.99/0.95  sat_num_of_non_cyclic_types:            0
% 1.99/0.95  sat_guarded_non_collapsed_types:        0
% 1.99/0.95  num_pure_diseq_elim:                    0
% 1.99/0.95  simp_replaced_by:                       0
% 1.99/0.95  res_preprocessed:                       120
% 1.99/0.95  prep_upred:                             0
% 1.99/0.95  prep_unflattend:                        17
% 1.99/0.95  smt_new_axioms:                         0
% 1.99/0.95  pred_elim_cands:                        6
% 1.99/0.95  pred_elim:                              1
% 1.99/0.95  pred_elim_cl:                           1
% 1.99/0.95  pred_elim_cycles:                       6
% 1.99/0.95  merged_defs:                            0
% 1.99/0.95  merged_defs_ncl:                        0
% 1.99/0.95  bin_hyper_res:                          0
% 1.99/0.95  prep_cycles:                            4
% 1.99/0.95  pred_elim_time:                         0.006
% 1.99/0.95  splitting_time:                         0.
% 1.99/0.95  sem_filter_time:                        0.
% 1.99/0.95  monotx_time:                            0.001
% 1.99/0.95  subtype_inf_time:                       0.
% 1.99/0.95  
% 1.99/0.95  ------ Problem properties
% 1.99/0.95  
% 1.99/0.95  clauses:                                22
% 1.99/0.95  conjectures:                            9
% 1.99/0.95  epr:                                    11
% 1.99/0.95  horn:                                   17
% 1.99/0.95  ground:                                 10
% 1.99/0.95  unary:                                  11
% 1.99/0.95  binary:                                 5
% 1.99/0.95  lits:                                   45
% 1.99/0.95  lits_eq:                                8
% 1.99/0.95  fd_pure:                                0
% 1.99/0.95  fd_pseudo:                              0
% 1.99/0.95  fd_cond:                                0
% 1.99/0.95  fd_pseudo_cond:                         1
% 1.99/0.95  ac_symbols:                             0
% 1.99/0.95  
% 1.99/0.95  ------ Propositional Solver
% 1.99/0.95  
% 1.99/0.95  prop_solver_calls:                      28
% 1.99/0.95  prop_fast_solver_calls:                 781
% 1.99/0.95  smt_solver_calls:                       0
% 1.99/0.95  smt_fast_solver_calls:                  0
% 1.99/0.95  prop_num_of_clauses:                    1166
% 1.99/0.95  prop_preprocess_simplified:             4165
% 1.99/0.95  prop_fo_subsumed:                       20
% 1.99/0.95  prop_solver_time:                       0.
% 1.99/0.95  smt_solver_time:                        0.
% 1.99/0.95  smt_fast_solver_time:                   0.
% 1.99/0.95  prop_fast_solver_time:                  0.
% 1.99/0.95  prop_unsat_core_time:                   0.
% 1.99/0.95  
% 1.99/0.95  ------ QBF
% 1.99/0.95  
% 1.99/0.95  qbf_q_res:                              0
% 1.99/0.95  qbf_num_tautologies:                    0
% 1.99/0.95  qbf_prep_cycles:                        0
% 1.99/0.95  
% 1.99/0.95  ------ BMC1
% 1.99/0.95  
% 1.99/0.95  bmc1_current_bound:                     -1
% 1.99/0.95  bmc1_last_solved_bound:                 -1
% 1.99/0.95  bmc1_unsat_core_size:                   -1
% 1.99/0.95  bmc1_unsat_core_parents_size:           -1
% 1.99/0.95  bmc1_merge_next_fun:                    0
% 1.99/0.95  bmc1_unsat_core_clauses_time:           0.
% 1.99/0.95  
% 1.99/0.95  ------ Instantiation
% 1.99/0.95  
% 1.99/0.95  inst_num_of_clauses:                    349
% 1.99/0.95  inst_num_in_passive:                    139
% 1.99/0.95  inst_num_in_active:                     174
% 1.99/0.95  inst_num_in_unprocessed:                35
% 1.99/0.95  inst_num_of_loops:                      253
% 1.99/0.95  inst_num_of_learning_restarts:          0
% 1.99/0.95  inst_num_moves_active_passive:          75
% 1.99/0.95  inst_lit_activity:                      0
% 1.99/0.95  inst_lit_activity_moves:                0
% 1.99/0.95  inst_num_tautologies:                   0
% 1.99/0.95  inst_num_prop_implied:                  0
% 1.99/0.95  inst_num_existing_simplified:           0
% 1.99/0.95  inst_num_eq_res_simplified:             0
% 1.99/0.95  inst_num_child_elim:                    0
% 1.99/0.95  inst_num_of_dismatching_blockings:      43
% 1.99/0.95  inst_num_of_non_proper_insts:           340
% 1.99/0.95  inst_num_of_duplicates:                 0
% 1.99/0.95  inst_inst_num_from_inst_to_res:         0
% 1.99/0.95  inst_dismatching_checking_time:         0.
% 1.99/0.95  
% 1.99/0.95  ------ Resolution
% 1.99/0.95  
% 1.99/0.95  res_num_of_clauses:                     0
% 1.99/0.95  res_num_in_passive:                     0
% 1.99/0.95  res_num_in_active:                      0
% 1.99/0.95  res_num_of_loops:                       124
% 1.99/0.95  res_forward_subset_subsumed:            27
% 1.99/0.95  res_backward_subset_subsumed:           0
% 1.99/0.95  res_forward_subsumed:                   0
% 1.99/0.95  res_backward_subsumed:                  0
% 1.99/0.95  res_forward_subsumption_resolution:     0
% 1.99/0.95  res_backward_subsumption_resolution:    0
% 1.99/0.95  res_clause_to_clause_subsumption:       110
% 1.99/0.95  res_orphan_elimination:                 0
% 1.99/0.95  res_tautology_del:                      34
% 1.99/0.95  res_num_eq_res_simplified:              0
% 1.99/0.95  res_num_sel_changes:                    0
% 1.99/0.95  res_moves_from_active_to_pass:          0
% 1.99/0.95  
% 1.99/0.95  ------ Superposition
% 1.99/0.95  
% 1.99/0.95  sup_time_total:                         0.
% 1.99/0.95  sup_time_generating:                    0.
% 1.99/0.95  sup_time_sim_full:                      0.
% 1.99/0.95  sup_time_sim_immed:                     0.
% 1.99/0.95  
% 1.99/0.95  sup_num_of_clauses:                     58
% 1.99/0.95  sup_num_in_active:                      46
% 1.99/0.95  sup_num_in_passive:                     12
% 1.99/0.95  sup_num_of_loops:                       50
% 1.99/0.95  sup_fw_superposition:                   29
% 1.99/0.95  sup_bw_superposition:                   15
% 1.99/0.95  sup_immediate_simplified:               2
% 1.99/0.95  sup_given_eliminated:                   0
% 1.99/0.95  comparisons_done:                       0
% 1.99/0.95  comparisons_avoided:                    2
% 1.99/0.95  
% 1.99/0.95  ------ Simplifications
% 1.99/0.95  
% 1.99/0.95  
% 1.99/0.95  sim_fw_subset_subsumed:                 0
% 1.99/0.95  sim_bw_subset_subsumed:                 2
% 1.99/0.95  sim_fw_subsumed:                        1
% 1.99/0.95  sim_bw_subsumed:                        0
% 1.99/0.95  sim_fw_subsumption_res:                 0
% 1.99/0.95  sim_bw_subsumption_res:                 0
% 1.99/0.95  sim_tautology_del:                      4
% 1.99/0.95  sim_eq_tautology_del:                   2
% 1.99/0.95  sim_eq_res_simp:                        0
% 1.99/0.95  sim_fw_demodulated:                     1
% 1.99/0.95  sim_bw_demodulated:                     2
% 1.99/0.95  sim_light_normalised:                   0
% 1.99/0.95  sim_joinable_taut:                      0
% 1.99/0.95  sim_joinable_simp:                      0
% 1.99/0.95  sim_ac_normalised:                      0
% 1.99/0.95  sim_smt_subsumption:                    0
% 1.99/0.95  
%------------------------------------------------------------------------------
