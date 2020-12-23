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
% DateTime   : Thu Dec  3 12:09:39 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 512 expanded)
%              Number of clauses        :   85 ( 140 expanded)
%              Number of leaves         :   15 ( 179 expanded)
%              Depth                    :   20
%              Number of atoms          :  491 (4210 expanded)
%              Number of equality atoms :  194 (1092 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f25,plain,(
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

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f22,plain,
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

fof(f26,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f25,f24,f23,f22])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f29,plain,(
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

fof(f33,plain,(
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

fof(f36,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f31,plain,(
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

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_619,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_934,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_621,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_932,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_283,plain,
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
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_284,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_288,plain,
    ( ~ v1_funct_1(X1)
    | ~ r2_hidden(X0,sK1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_15,c_13])).

cnf(c_289,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_288])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X1)
    | X3 != X0
    | k1_funct_1(k5_relat_1(sK3,X2),X3) = k1_funct_1(X2,k1_funct_1(sK3,X3))
    | sK2 = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_289])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,sK1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | v1_xboole_0(sK1)
    | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
    | sK2 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | ~ v1_funct_1(X1_50)
    | ~ v1_relat_1(X1_50)
    | v1_xboole_0(sK1)
    | sK2 = k1_xboole_0
    | k1_funct_1(k5_relat_1(sK3,X1_50),X0_50) = k1_funct_1(X1_50,k1_funct_1(sK3,X0_50)) ),
    inference(subtyping,[status(esa)],[c_405])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0_50,sK1)
    | ~ v1_funct_1(X1_50)
    | ~ v1_relat_1(X1_50)
    | k1_funct_1(k5_relat_1(sK3,X1_50),X0_50) = k1_funct_1(X1_50,k1_funct_1(sK3,X0_50))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_614])).

cnf(c_940,plain,
    ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
    | m1_subset_1(X1_50,sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_16,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_41,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_623,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_630,plain,
    ( v1_xboole_0(sK1)
    | sP0_iProver_split
    | sK2 = k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_614])).

cnf(c_687,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_688,plain,
    ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
    | m1_subset_1(X1_50,sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_627,plain,
    ( ~ v1_xboole_0(X0_51)
    | ~ v1_xboole_0(X1_51)
    | X1_51 = X0_51 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1050,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_1051,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_639,plain,
    ( ~ v1_xboole_0(X0_51)
    | v1_xboole_0(X1_51)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_1057,plain,
    ( v1_xboole_0(X0_51)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0_51 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1059,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_1626,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X1_50,sK1) != iProver_top
    | k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_16,c_0,c_41,c_623,c_687,c_688,c_1051,c_1059])).

cnf(c_1627,plain,
    ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
    | m1_subset_1(X1_50,sK1) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_1626])).

cnf(c_1636,plain,
    ( k1_funct_1(X0_50,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,X0_50),sK5)
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_932,c_1627])).

cnf(c_1682,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_934,c_1636])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_622,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_931,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_310,plain,
    ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X2)
    | k1_partfun1(X0,X1,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,X4)
    | sK2 != X1
    | sK1 != X0
    | sK3 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_311,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_315,plain,
    ( ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_15,c_13])).

cnf(c_316,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
    | ~ v1_funct_1(X1)
    | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
    | k1_xboole_0 = sK2 ),
    inference(renaming,[status(thm)],[c_315])).

cnf(c_615,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_xboole_0 = sK2
    | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50) ),
    inference(subtyping,[status(esa)],[c_316])).

cnf(c_938,plain,
    ( k1_xboole_0 = sK2
    | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_633,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_665,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_684,plain,
    ( k1_xboole_0 = sK2
    | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_638,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1207,plain,
    ( X0_51 != X1_51
    | X0_51 = k1_xboole_0
    | k1_xboole_0 != X1_51 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1208,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_1526,plain,
    ( k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_938,c_16,c_0,c_665,c_684,c_1059,c_1208])).

cnf(c_1536,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_1526])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_620,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_933,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_618,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_935,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_625,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X1_50)
    | ~ v1_funct_1(X0_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_930,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_1304,plain,
    ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_930])).

cnf(c_18,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1451,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1304,c_18])).

cnf(c_1452,plain,
    ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_1451])).

cnf(c_1458,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_933,c_1452])).

cnf(c_1096,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0_51,X1_51,sK2,sK0,X0_50,sK4) = k5_relat_1(X0_50,sK4) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1184,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_1471,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1458,c_15,c_13,c_12,c_11,c_1184])).

cnf(c_1537,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1536,c_1471])).

cnf(c_21,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1582,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1537,c_21,c_22])).

cnf(c_7,negated_conjecture,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_624,negated_conjecture,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1585,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_1582,c_624])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1044,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_1045,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1682,c_1585,c_1045,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:39:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.45/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.45/0.94  
% 1.45/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.45/0.94  
% 1.45/0.94  ------  iProver source info
% 1.45/0.94  
% 1.45/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.45/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.45/0.94  git: non_committed_changes: false
% 1.45/0.94  git: last_make_outside_of_git: false
% 1.45/0.94  
% 1.45/0.94  ------ 
% 1.45/0.94  
% 1.45/0.94  ------ Input Options
% 1.45/0.94  
% 1.45/0.94  --out_options                           all
% 1.45/0.94  --tptp_safe_out                         true
% 1.45/0.94  --problem_path                          ""
% 1.45/0.94  --include_path                          ""
% 1.45/0.94  --clausifier                            res/vclausify_rel
% 1.45/0.94  --clausifier_options                    --mode clausify
% 1.45/0.94  --stdin                                 false
% 1.45/0.94  --stats_out                             all
% 1.45/0.94  
% 1.45/0.94  ------ General Options
% 1.45/0.94  
% 1.45/0.94  --fof                                   false
% 1.45/0.94  --time_out_real                         305.
% 1.45/0.94  --time_out_virtual                      -1.
% 1.45/0.94  --symbol_type_check                     false
% 1.45/0.94  --clausify_out                          false
% 1.45/0.94  --sig_cnt_out                           false
% 1.45/0.94  --trig_cnt_out                          false
% 1.45/0.94  --trig_cnt_out_tolerance                1.
% 1.45/0.94  --trig_cnt_out_sk_spl                   false
% 1.45/0.94  --abstr_cl_out                          false
% 1.45/0.94  
% 1.45/0.94  ------ Global Options
% 1.45/0.94  
% 1.45/0.94  --schedule                              default
% 1.45/0.94  --add_important_lit                     false
% 1.45/0.94  --prop_solver_per_cl                    1000
% 1.45/0.94  --min_unsat_core                        false
% 1.45/0.94  --soft_assumptions                      false
% 1.45/0.94  --soft_lemma_size                       3
% 1.45/0.94  --prop_impl_unit_size                   0
% 1.45/0.94  --prop_impl_unit                        []
% 1.45/0.94  --share_sel_clauses                     true
% 1.45/0.94  --reset_solvers                         false
% 1.45/0.94  --bc_imp_inh                            [conj_cone]
% 1.45/0.94  --conj_cone_tolerance                   3.
% 1.45/0.94  --extra_neg_conj                        none
% 1.45/0.94  --large_theory_mode                     true
% 1.45/0.94  --prolific_symb_bound                   200
% 1.45/0.94  --lt_threshold                          2000
% 1.45/0.94  --clause_weak_htbl                      true
% 1.45/0.94  --gc_record_bc_elim                     false
% 1.45/0.94  
% 1.45/0.94  ------ Preprocessing Options
% 1.45/0.94  
% 1.45/0.94  --preprocessing_flag                    true
% 1.45/0.94  --time_out_prep_mult                    0.1
% 1.45/0.94  --splitting_mode                        input
% 1.45/0.94  --splitting_grd                         true
% 1.45/0.94  --splitting_cvd                         false
% 1.45/0.94  --splitting_cvd_svl                     false
% 1.45/0.94  --splitting_nvd                         32
% 1.45/0.94  --sub_typing                            true
% 1.45/0.94  --prep_gs_sim                           true
% 1.45/0.94  --prep_unflatten                        true
% 1.45/0.94  --prep_res_sim                          true
% 1.45/0.94  --prep_upred                            true
% 1.45/0.94  --prep_sem_filter                       exhaustive
% 1.45/0.94  --prep_sem_filter_out                   false
% 1.45/0.94  --pred_elim                             true
% 1.45/0.94  --res_sim_input                         true
% 1.45/0.94  --eq_ax_congr_red                       true
% 1.45/0.94  --pure_diseq_elim                       true
% 1.45/0.94  --brand_transform                       false
% 1.45/0.94  --non_eq_to_eq                          false
% 1.45/0.94  --prep_def_merge                        true
% 1.45/0.94  --prep_def_merge_prop_impl              false
% 1.45/0.94  --prep_def_merge_mbd                    true
% 1.45/0.94  --prep_def_merge_tr_red                 false
% 1.45/0.94  --prep_def_merge_tr_cl                  false
% 1.45/0.94  --smt_preprocessing                     true
% 1.45/0.94  --smt_ac_axioms                         fast
% 1.45/0.94  --preprocessed_out                      false
% 1.45/0.94  --preprocessed_stats                    false
% 1.45/0.94  
% 1.45/0.94  ------ Abstraction refinement Options
% 1.45/0.94  
% 1.45/0.94  --abstr_ref                             []
% 1.45/0.94  --abstr_ref_prep                        false
% 1.45/0.94  --abstr_ref_until_sat                   false
% 1.45/0.94  --abstr_ref_sig_restrict                funpre
% 1.45/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/0.94  --abstr_ref_under                       []
% 1.45/0.94  
% 1.45/0.94  ------ SAT Options
% 1.45/0.94  
% 1.45/0.94  --sat_mode                              false
% 1.45/0.94  --sat_fm_restart_options                ""
% 1.45/0.94  --sat_gr_def                            false
% 1.45/0.94  --sat_epr_types                         true
% 1.45/0.94  --sat_non_cyclic_types                  false
% 1.45/0.94  --sat_finite_models                     false
% 1.45/0.94  --sat_fm_lemmas                         false
% 1.45/0.94  --sat_fm_prep                           false
% 1.45/0.94  --sat_fm_uc_incr                        true
% 1.45/0.94  --sat_out_model                         small
% 1.45/0.94  --sat_out_clauses                       false
% 1.45/0.94  
% 1.45/0.94  ------ QBF Options
% 1.45/0.94  
% 1.45/0.94  --qbf_mode                              false
% 1.45/0.94  --qbf_elim_univ                         false
% 1.45/0.94  --qbf_dom_inst                          none
% 1.45/0.94  --qbf_dom_pre_inst                      false
% 1.45/0.94  --qbf_sk_in                             false
% 1.45/0.94  --qbf_pred_elim                         true
% 1.45/0.94  --qbf_split                             512
% 1.45/0.94  
% 1.45/0.94  ------ BMC1 Options
% 1.45/0.94  
% 1.45/0.94  --bmc1_incremental                      false
% 1.45/0.94  --bmc1_axioms                           reachable_all
% 1.45/0.94  --bmc1_min_bound                        0
% 1.45/0.94  --bmc1_max_bound                        -1
% 1.45/0.94  --bmc1_max_bound_default                -1
% 1.45/0.94  --bmc1_symbol_reachability              true
% 1.45/0.94  --bmc1_property_lemmas                  false
% 1.45/0.94  --bmc1_k_induction                      false
% 1.45/0.94  --bmc1_non_equiv_states                 false
% 1.45/0.94  --bmc1_deadlock                         false
% 1.45/0.94  --bmc1_ucm                              false
% 1.45/0.94  --bmc1_add_unsat_core                   none
% 1.45/0.94  --bmc1_unsat_core_children              false
% 1.45/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/0.94  --bmc1_out_stat                         full
% 1.45/0.94  --bmc1_ground_init                      false
% 1.45/0.94  --bmc1_pre_inst_next_state              false
% 1.45/0.94  --bmc1_pre_inst_state                   false
% 1.45/0.94  --bmc1_pre_inst_reach_state             false
% 1.45/0.94  --bmc1_out_unsat_core                   false
% 1.45/0.94  --bmc1_aig_witness_out                  false
% 1.45/0.94  --bmc1_verbose                          false
% 1.45/0.94  --bmc1_dump_clauses_tptp                false
% 1.45/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.45/0.94  --bmc1_dump_file                        -
% 1.45/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.45/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.45/0.94  --bmc1_ucm_extend_mode                  1
% 1.45/0.94  --bmc1_ucm_init_mode                    2
% 1.45/0.94  --bmc1_ucm_cone_mode                    none
% 1.45/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.45/0.94  --bmc1_ucm_relax_model                  4
% 1.45/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.45/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/0.94  --bmc1_ucm_layered_model                none
% 1.45/0.94  --bmc1_ucm_max_lemma_size               10
% 1.45/0.94  
% 1.45/0.94  ------ AIG Options
% 1.45/0.94  
% 1.45/0.94  --aig_mode                              false
% 1.45/0.94  
% 1.45/0.94  ------ Instantiation Options
% 1.45/0.94  
% 1.45/0.94  --instantiation_flag                    true
% 1.45/0.94  --inst_sos_flag                         false
% 1.45/0.94  --inst_sos_phase                        true
% 1.45/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/0.94  --inst_lit_sel_side                     num_symb
% 1.45/0.94  --inst_solver_per_active                1400
% 1.45/0.94  --inst_solver_calls_frac                1.
% 1.45/0.94  --inst_passive_queue_type               priority_queues
% 1.45/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/0.94  --inst_passive_queues_freq              [25;2]
% 1.45/0.94  --inst_dismatching                      true
% 1.45/0.94  --inst_eager_unprocessed_to_passive     true
% 1.45/0.94  --inst_prop_sim_given                   true
% 1.45/0.94  --inst_prop_sim_new                     false
% 1.45/0.94  --inst_subs_new                         false
% 1.45/0.94  --inst_eq_res_simp                      false
% 1.45/0.94  --inst_subs_given                       false
% 1.45/0.94  --inst_orphan_elimination               true
% 1.45/0.94  --inst_learning_loop_flag               true
% 1.45/0.94  --inst_learning_start                   3000
% 1.45/0.94  --inst_learning_factor                  2
% 1.45/0.94  --inst_start_prop_sim_after_learn       3
% 1.45/0.94  --inst_sel_renew                        solver
% 1.45/0.94  --inst_lit_activity_flag                true
% 1.45/0.94  --inst_restr_to_given                   false
% 1.45/0.94  --inst_activity_threshold               500
% 1.45/0.94  --inst_out_proof                        true
% 1.45/0.94  
% 1.45/0.94  ------ Resolution Options
% 1.45/0.94  
% 1.45/0.94  --resolution_flag                       true
% 1.45/0.94  --res_lit_sel                           adaptive
% 1.45/0.94  --res_lit_sel_side                      none
% 1.45/0.94  --res_ordering                          kbo
% 1.45/0.94  --res_to_prop_solver                    active
% 1.45/0.94  --res_prop_simpl_new                    false
% 1.45/0.94  --res_prop_simpl_given                  true
% 1.45/0.94  --res_passive_queue_type                priority_queues
% 1.45/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/0.94  --res_passive_queues_freq               [15;5]
% 1.45/0.94  --res_forward_subs                      full
% 1.45/0.94  --res_backward_subs                     full
% 1.45/0.94  --res_forward_subs_resolution           true
% 1.45/0.94  --res_backward_subs_resolution          true
% 1.45/0.94  --res_orphan_elimination                true
% 1.45/0.94  --res_time_limit                        2.
% 1.45/0.94  --res_out_proof                         true
% 1.45/0.94  
% 1.45/0.94  ------ Superposition Options
% 1.45/0.94  
% 1.45/0.94  --superposition_flag                    true
% 1.45/0.94  --sup_passive_queue_type                priority_queues
% 1.45/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.45/0.94  --demod_completeness_check              fast
% 1.45/0.94  --demod_use_ground                      true
% 1.45/0.94  --sup_to_prop_solver                    passive
% 1.45/0.94  --sup_prop_simpl_new                    true
% 1.45/0.94  --sup_prop_simpl_given                  true
% 1.45/0.94  --sup_fun_splitting                     false
% 1.45/0.94  --sup_smt_interval                      50000
% 1.45/0.94  
% 1.45/0.94  ------ Superposition Simplification Setup
% 1.45/0.94  
% 1.45/0.94  --sup_indices_passive                   []
% 1.45/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.94  --sup_full_bw                           [BwDemod]
% 1.45/0.94  --sup_immed_triv                        [TrivRules]
% 1.45/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.94  --sup_immed_bw_main                     []
% 1.45/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.94  
% 1.45/0.94  ------ Combination Options
% 1.45/0.94  
% 1.45/0.94  --comb_res_mult                         3
% 1.45/0.94  --comb_sup_mult                         2
% 1.45/0.94  --comb_inst_mult                        10
% 1.45/0.94  
% 1.45/0.94  ------ Debug Options
% 1.45/0.94  
% 1.45/0.94  --dbg_backtrace                         false
% 1.45/0.94  --dbg_dump_prop_clauses                 false
% 1.45/0.94  --dbg_dump_prop_clauses_file            -
% 1.45/0.94  --dbg_out_stat                          false
% 1.45/0.94  ------ Parsing...
% 1.45/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.45/0.94  
% 1.45/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.45/0.94  
% 1.45/0.94  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.45/0.94  
% 1.45/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.45/0.94  ------ Proving...
% 1.45/0.94  ------ Problem Properties 
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  clauses                                 16
% 1.45/0.94  conjectures                             9
% 1.45/0.94  EPR                                     8
% 1.45/0.94  Horn                                    14
% 1.45/0.94  unary                                   10
% 1.45/0.94  binary                                  1
% 1.45/0.94  lits                                    33
% 1.45/0.94  lits eq                                 8
% 1.45/0.94  fd_pure                                 0
% 1.45/0.94  fd_pseudo                               0
% 1.45/0.94  fd_cond                                 0
% 1.45/0.94  fd_pseudo_cond                          1
% 1.45/0.94  AC symbols                              0
% 1.45/0.94  
% 1.45/0.94  ------ Schedule dynamic 5 is on 
% 1.45/0.94  
% 1.45/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  ------ 
% 1.45/0.94  Current options:
% 1.45/0.94  ------ 
% 1.45/0.94  
% 1.45/0.94  ------ Input Options
% 1.45/0.94  
% 1.45/0.94  --out_options                           all
% 1.45/0.94  --tptp_safe_out                         true
% 1.45/0.94  --problem_path                          ""
% 1.45/0.94  --include_path                          ""
% 1.45/0.94  --clausifier                            res/vclausify_rel
% 1.45/0.94  --clausifier_options                    --mode clausify
% 1.45/0.94  --stdin                                 false
% 1.45/0.94  --stats_out                             all
% 1.45/0.94  
% 1.45/0.94  ------ General Options
% 1.45/0.94  
% 1.45/0.94  --fof                                   false
% 1.45/0.94  --time_out_real                         305.
% 1.45/0.94  --time_out_virtual                      -1.
% 1.45/0.94  --symbol_type_check                     false
% 1.45/0.94  --clausify_out                          false
% 1.45/0.94  --sig_cnt_out                           false
% 1.45/0.94  --trig_cnt_out                          false
% 1.45/0.94  --trig_cnt_out_tolerance                1.
% 1.45/0.94  --trig_cnt_out_sk_spl                   false
% 1.45/0.94  --abstr_cl_out                          false
% 1.45/0.94  
% 1.45/0.94  ------ Global Options
% 1.45/0.94  
% 1.45/0.94  --schedule                              default
% 1.45/0.94  --add_important_lit                     false
% 1.45/0.94  --prop_solver_per_cl                    1000
% 1.45/0.94  --min_unsat_core                        false
% 1.45/0.94  --soft_assumptions                      false
% 1.45/0.94  --soft_lemma_size                       3
% 1.45/0.94  --prop_impl_unit_size                   0
% 1.45/0.94  --prop_impl_unit                        []
% 1.45/0.94  --share_sel_clauses                     true
% 1.45/0.94  --reset_solvers                         false
% 1.45/0.94  --bc_imp_inh                            [conj_cone]
% 1.45/0.94  --conj_cone_tolerance                   3.
% 1.45/0.94  --extra_neg_conj                        none
% 1.45/0.94  --large_theory_mode                     true
% 1.45/0.94  --prolific_symb_bound                   200
% 1.45/0.94  --lt_threshold                          2000
% 1.45/0.94  --clause_weak_htbl                      true
% 1.45/0.94  --gc_record_bc_elim                     false
% 1.45/0.94  
% 1.45/0.94  ------ Preprocessing Options
% 1.45/0.94  
% 1.45/0.94  --preprocessing_flag                    true
% 1.45/0.94  --time_out_prep_mult                    0.1
% 1.45/0.94  --splitting_mode                        input
% 1.45/0.94  --splitting_grd                         true
% 1.45/0.94  --splitting_cvd                         false
% 1.45/0.94  --splitting_cvd_svl                     false
% 1.45/0.94  --splitting_nvd                         32
% 1.45/0.94  --sub_typing                            true
% 1.45/0.94  --prep_gs_sim                           true
% 1.45/0.94  --prep_unflatten                        true
% 1.45/0.94  --prep_res_sim                          true
% 1.45/0.94  --prep_upred                            true
% 1.45/0.94  --prep_sem_filter                       exhaustive
% 1.45/0.94  --prep_sem_filter_out                   false
% 1.45/0.94  --pred_elim                             true
% 1.45/0.94  --res_sim_input                         true
% 1.45/0.94  --eq_ax_congr_red                       true
% 1.45/0.94  --pure_diseq_elim                       true
% 1.45/0.94  --brand_transform                       false
% 1.45/0.94  --non_eq_to_eq                          false
% 1.45/0.94  --prep_def_merge                        true
% 1.45/0.94  --prep_def_merge_prop_impl              false
% 1.45/0.94  --prep_def_merge_mbd                    true
% 1.45/0.94  --prep_def_merge_tr_red                 false
% 1.45/0.94  --prep_def_merge_tr_cl                  false
% 1.45/0.94  --smt_preprocessing                     true
% 1.45/0.94  --smt_ac_axioms                         fast
% 1.45/0.94  --preprocessed_out                      false
% 1.45/0.94  --preprocessed_stats                    false
% 1.45/0.94  
% 1.45/0.94  ------ Abstraction refinement Options
% 1.45/0.94  
% 1.45/0.94  --abstr_ref                             []
% 1.45/0.94  --abstr_ref_prep                        false
% 1.45/0.94  --abstr_ref_until_sat                   false
% 1.45/0.94  --abstr_ref_sig_restrict                funpre
% 1.45/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.45/0.94  --abstr_ref_under                       []
% 1.45/0.94  
% 1.45/0.94  ------ SAT Options
% 1.45/0.94  
% 1.45/0.94  --sat_mode                              false
% 1.45/0.94  --sat_fm_restart_options                ""
% 1.45/0.94  --sat_gr_def                            false
% 1.45/0.94  --sat_epr_types                         true
% 1.45/0.94  --sat_non_cyclic_types                  false
% 1.45/0.94  --sat_finite_models                     false
% 1.45/0.94  --sat_fm_lemmas                         false
% 1.45/0.94  --sat_fm_prep                           false
% 1.45/0.94  --sat_fm_uc_incr                        true
% 1.45/0.94  --sat_out_model                         small
% 1.45/0.94  --sat_out_clauses                       false
% 1.45/0.94  
% 1.45/0.94  ------ QBF Options
% 1.45/0.94  
% 1.45/0.94  --qbf_mode                              false
% 1.45/0.94  --qbf_elim_univ                         false
% 1.45/0.94  --qbf_dom_inst                          none
% 1.45/0.94  --qbf_dom_pre_inst                      false
% 1.45/0.94  --qbf_sk_in                             false
% 1.45/0.94  --qbf_pred_elim                         true
% 1.45/0.94  --qbf_split                             512
% 1.45/0.94  
% 1.45/0.94  ------ BMC1 Options
% 1.45/0.94  
% 1.45/0.94  --bmc1_incremental                      false
% 1.45/0.94  --bmc1_axioms                           reachable_all
% 1.45/0.94  --bmc1_min_bound                        0
% 1.45/0.94  --bmc1_max_bound                        -1
% 1.45/0.94  --bmc1_max_bound_default                -1
% 1.45/0.94  --bmc1_symbol_reachability              true
% 1.45/0.94  --bmc1_property_lemmas                  false
% 1.45/0.94  --bmc1_k_induction                      false
% 1.45/0.94  --bmc1_non_equiv_states                 false
% 1.45/0.94  --bmc1_deadlock                         false
% 1.45/0.94  --bmc1_ucm                              false
% 1.45/0.94  --bmc1_add_unsat_core                   none
% 1.45/0.94  --bmc1_unsat_core_children              false
% 1.45/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.45/0.94  --bmc1_out_stat                         full
% 1.45/0.94  --bmc1_ground_init                      false
% 1.45/0.94  --bmc1_pre_inst_next_state              false
% 1.45/0.94  --bmc1_pre_inst_state                   false
% 1.45/0.94  --bmc1_pre_inst_reach_state             false
% 1.45/0.94  --bmc1_out_unsat_core                   false
% 1.45/0.94  --bmc1_aig_witness_out                  false
% 1.45/0.94  --bmc1_verbose                          false
% 1.45/0.94  --bmc1_dump_clauses_tptp                false
% 1.45/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.45/0.94  --bmc1_dump_file                        -
% 1.45/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.45/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.45/0.94  --bmc1_ucm_extend_mode                  1
% 1.45/0.94  --bmc1_ucm_init_mode                    2
% 1.45/0.94  --bmc1_ucm_cone_mode                    none
% 1.45/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.45/0.94  --bmc1_ucm_relax_model                  4
% 1.45/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.45/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.45/0.94  --bmc1_ucm_layered_model                none
% 1.45/0.94  --bmc1_ucm_max_lemma_size               10
% 1.45/0.94  
% 1.45/0.94  ------ AIG Options
% 1.45/0.94  
% 1.45/0.94  --aig_mode                              false
% 1.45/0.94  
% 1.45/0.94  ------ Instantiation Options
% 1.45/0.94  
% 1.45/0.94  --instantiation_flag                    true
% 1.45/0.94  --inst_sos_flag                         false
% 1.45/0.94  --inst_sos_phase                        true
% 1.45/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.45/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.45/0.94  --inst_lit_sel_side                     none
% 1.45/0.94  --inst_solver_per_active                1400
% 1.45/0.94  --inst_solver_calls_frac                1.
% 1.45/0.94  --inst_passive_queue_type               priority_queues
% 1.45/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.45/0.94  --inst_passive_queues_freq              [25;2]
% 1.45/0.94  --inst_dismatching                      true
% 1.45/0.94  --inst_eager_unprocessed_to_passive     true
% 1.45/0.94  --inst_prop_sim_given                   true
% 1.45/0.94  --inst_prop_sim_new                     false
% 1.45/0.94  --inst_subs_new                         false
% 1.45/0.94  --inst_eq_res_simp                      false
% 1.45/0.94  --inst_subs_given                       false
% 1.45/0.94  --inst_orphan_elimination               true
% 1.45/0.94  --inst_learning_loop_flag               true
% 1.45/0.94  --inst_learning_start                   3000
% 1.45/0.94  --inst_learning_factor                  2
% 1.45/0.94  --inst_start_prop_sim_after_learn       3
% 1.45/0.94  --inst_sel_renew                        solver
% 1.45/0.94  --inst_lit_activity_flag                true
% 1.45/0.94  --inst_restr_to_given                   false
% 1.45/0.94  --inst_activity_threshold               500
% 1.45/0.94  --inst_out_proof                        true
% 1.45/0.94  
% 1.45/0.94  ------ Resolution Options
% 1.45/0.94  
% 1.45/0.94  --resolution_flag                       false
% 1.45/0.94  --res_lit_sel                           adaptive
% 1.45/0.94  --res_lit_sel_side                      none
% 1.45/0.94  --res_ordering                          kbo
% 1.45/0.94  --res_to_prop_solver                    active
% 1.45/0.94  --res_prop_simpl_new                    false
% 1.45/0.94  --res_prop_simpl_given                  true
% 1.45/0.94  --res_passive_queue_type                priority_queues
% 1.45/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.45/0.94  --res_passive_queues_freq               [15;5]
% 1.45/0.94  --res_forward_subs                      full
% 1.45/0.94  --res_backward_subs                     full
% 1.45/0.94  --res_forward_subs_resolution           true
% 1.45/0.94  --res_backward_subs_resolution          true
% 1.45/0.94  --res_orphan_elimination                true
% 1.45/0.94  --res_time_limit                        2.
% 1.45/0.94  --res_out_proof                         true
% 1.45/0.94  
% 1.45/0.94  ------ Superposition Options
% 1.45/0.94  
% 1.45/0.94  --superposition_flag                    true
% 1.45/0.94  --sup_passive_queue_type                priority_queues
% 1.45/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.45/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.45/0.94  --demod_completeness_check              fast
% 1.45/0.94  --demod_use_ground                      true
% 1.45/0.94  --sup_to_prop_solver                    passive
% 1.45/0.94  --sup_prop_simpl_new                    true
% 1.45/0.94  --sup_prop_simpl_given                  true
% 1.45/0.94  --sup_fun_splitting                     false
% 1.45/0.94  --sup_smt_interval                      50000
% 1.45/0.94  
% 1.45/0.94  ------ Superposition Simplification Setup
% 1.45/0.94  
% 1.45/0.94  --sup_indices_passive                   []
% 1.45/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.45/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.45/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.94  --sup_full_bw                           [BwDemod]
% 1.45/0.94  --sup_immed_triv                        [TrivRules]
% 1.45/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.45/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.94  --sup_immed_bw_main                     []
% 1.45/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.45/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.45/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.45/0.94  
% 1.45/0.94  ------ Combination Options
% 1.45/0.94  
% 1.45/0.94  --comb_res_mult                         3
% 1.45/0.94  --comb_sup_mult                         2
% 1.45/0.94  --comb_inst_mult                        10
% 1.45/0.94  
% 1.45/0.94  ------ Debug Options
% 1.45/0.94  
% 1.45/0.94  --dbg_backtrace                         false
% 1.45/0.94  --dbg_dump_prop_clauses                 false
% 1.45/0.94  --dbg_dump_prop_clauses_file            -
% 1.45/0.94  --dbg_out_stat                          false
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  ------ Proving...
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  % SZS status Theorem for theBenchmark.p
% 1.45/0.94  
% 1.45/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 1.45/0.94  
% 1.45/0.94  fof(f8,conjecture,(
% 1.45/0.94    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f9,negated_conjecture,(
% 1.45/0.94    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 1.45/0.94    inference(negated_conjecture,[],[f8])).
% 1.45/0.94  
% 1.45/0.94  fof(f20,plain,(
% 1.45/0.94    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.45/0.94    inference(ennf_transformation,[],[f9])).
% 1.45/0.94  
% 1.45/0.94  fof(f21,plain,(
% 1.45/0.94    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.45/0.94    inference(flattening,[],[f20])).
% 1.45/0.94  
% 1.45/0.94  fof(f25,plain,(
% 1.45/0.94    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 1.45/0.94    introduced(choice_axiom,[])).
% 1.45/0.94  
% 1.45/0.94  fof(f24,plain,(
% 1.45/0.94    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 1.45/0.94    introduced(choice_axiom,[])).
% 1.45/0.94  
% 1.45/0.94  fof(f23,plain,(
% 1.45/0.94    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 1.45/0.94    introduced(choice_axiom,[])).
% 1.45/0.94  
% 1.45/0.94  fof(f22,plain,(
% 1.45/0.94    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 1.45/0.94    introduced(choice_axiom,[])).
% 1.45/0.94  
% 1.45/0.94  fof(f26,plain,(
% 1.45/0.94    (((k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 1.45/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f21,f25,f24,f23,f22])).
% 1.45/0.94  
% 1.45/0.94  fof(f38,plain,(
% 1.45/0.94    v1_funct_1(sK4)),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f40,plain,(
% 1.45/0.94    m1_subset_1(sK5,sK1)),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f3,axiom,(
% 1.45/0.94    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f11,plain,(
% 1.45/0.94    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.45/0.94    inference(ennf_transformation,[],[f3])).
% 1.45/0.94  
% 1.45/0.94  fof(f12,plain,(
% 1.45/0.94    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.45/0.94    inference(flattening,[],[f11])).
% 1.45/0.94  
% 1.45/0.94  fof(f29,plain,(
% 1.45/0.94    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.45/0.94    inference(cnf_transformation,[],[f12])).
% 1.45/0.94  
% 1.45/0.94  fof(f7,axiom,(
% 1.45/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1))))),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f18,plain,(
% 1.45/0.94    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.45/0.94    inference(ennf_transformation,[],[f7])).
% 1.45/0.94  
% 1.45/0.94  fof(f19,plain,(
% 1.45/0.94    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.45/0.94    inference(flattening,[],[f18])).
% 1.45/0.94  
% 1.45/0.94  fof(f33,plain,(
% 1.45/0.94    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.45/0.94    inference(cnf_transformation,[],[f19])).
% 1.45/0.94  
% 1.45/0.94  fof(f36,plain,(
% 1.45/0.94    v1_funct_2(sK3,sK1,sK2)),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f35,plain,(
% 1.45/0.94    v1_funct_1(sK3)),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f37,plain,(
% 1.45/0.94    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f34,plain,(
% 1.45/0.94    ~v1_xboole_0(sK2)),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f1,axiom,(
% 1.45/0.94    v1_xboole_0(k1_xboole_0)),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f27,plain,(
% 1.45/0.94    v1_xboole_0(k1_xboole_0)),
% 1.45/0.94    inference(cnf_transformation,[],[f1])).
% 1.45/0.94  
% 1.45/0.94  fof(f42,plain,(
% 1.45/0.94    k1_xboole_0 != sK1),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f2,axiom,(
% 1.45/0.94    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f10,plain,(
% 1.45/0.94    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.45/0.94    inference(ennf_transformation,[],[f2])).
% 1.45/0.94  
% 1.45/0.94  fof(f28,plain,(
% 1.45/0.94    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.45/0.94    inference(cnf_transformation,[],[f10])).
% 1.45/0.94  
% 1.45/0.94  fof(f41,plain,(
% 1.45/0.94    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f5,axiom,(
% 1.45/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f14,plain,(
% 1.45/0.94    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.45/0.94    inference(ennf_transformation,[],[f5])).
% 1.45/0.94  
% 1.45/0.94  fof(f15,plain,(
% 1.45/0.94    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.45/0.94    inference(flattening,[],[f14])).
% 1.45/0.94  
% 1.45/0.94  fof(f31,plain,(
% 1.45/0.94    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.45/0.94    inference(cnf_transformation,[],[f15])).
% 1.45/0.94  
% 1.45/0.94  fof(f39,plain,(
% 1.45/0.94    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f6,axiom,(
% 1.45/0.94    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f16,plain,(
% 1.45/0.94    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.45/0.94    inference(ennf_transformation,[],[f6])).
% 1.45/0.94  
% 1.45/0.94  fof(f17,plain,(
% 1.45/0.94    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.45/0.94    inference(flattening,[],[f16])).
% 1.45/0.94  
% 1.45/0.94  fof(f32,plain,(
% 1.45/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.45/0.94    inference(cnf_transformation,[],[f17])).
% 1.45/0.94  
% 1.45/0.94  fof(f43,plain,(
% 1.45/0.94    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 1.45/0.94    inference(cnf_transformation,[],[f26])).
% 1.45/0.94  
% 1.45/0.94  fof(f4,axiom,(
% 1.45/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.45/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.45/0.94  
% 1.45/0.94  fof(f13,plain,(
% 1.45/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.94    inference(ennf_transformation,[],[f4])).
% 1.45/0.94  
% 1.45/0.94  fof(f30,plain,(
% 1.45/0.94    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.94    inference(cnf_transformation,[],[f13])).
% 1.45/0.94  
% 1.45/0.94  cnf(c_12,negated_conjecture,
% 1.45/0.94      ( v1_funct_1(sK4) ),
% 1.45/0.94      inference(cnf_transformation,[],[f38]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_619,negated_conjecture,
% 1.45/0.94      ( v1_funct_1(sK4) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_12]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_934,plain,
% 1.45/0.94      ( v1_funct_1(sK4) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_10,negated_conjecture,
% 1.45/0.94      ( m1_subset_1(sK5,sK1) ),
% 1.45/0.94      inference(cnf_transformation,[],[f40]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_621,negated_conjecture,
% 1.45/0.94      ( m1_subset_1(sK5,sK1) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_10]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_932,plain,
% 1.45/0.94      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_2,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.45/0.94      inference(cnf_transformation,[],[f29]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_6,plain,
% 1.45/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.94      | ~ r2_hidden(X3,X1)
% 1.45/0.94      | ~ v1_funct_1(X4)
% 1.45/0.94      | ~ v1_funct_1(X0)
% 1.45/0.94      | ~ v1_relat_1(X4)
% 1.45/0.94      | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 1.45/0.94      | k1_xboole_0 = X2 ),
% 1.45/0.94      inference(cnf_transformation,[],[f33]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_14,negated_conjecture,
% 1.45/0.94      ( v1_funct_2(sK3,sK1,sK2) ),
% 1.45/0.94      inference(cnf_transformation,[],[f36]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_283,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.94      | ~ r2_hidden(X3,X1)
% 1.45/0.94      | ~ v1_funct_1(X4)
% 1.45/0.94      | ~ v1_funct_1(X0)
% 1.45/0.94      | ~ v1_relat_1(X4)
% 1.45/0.94      | k1_funct_1(X4,k1_funct_1(X0,X3)) = k1_funct_1(k5_relat_1(X0,X4),X3)
% 1.45/0.94      | sK2 != X2
% 1.45/0.94      | sK1 != X1
% 1.45/0.94      | sK3 != X0
% 1.45/0.94      | k1_xboole_0 = X2 ),
% 1.45/0.94      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_284,plain,
% 1.45/0.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.45/0.94      | ~ r2_hidden(X0,sK1)
% 1.45/0.94      | ~ v1_funct_1(X1)
% 1.45/0.94      | ~ v1_funct_1(sK3)
% 1.45/0.94      | ~ v1_relat_1(X1)
% 1.45/0.94      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.45/0.94      | k1_xboole_0 = sK2 ),
% 1.45/0.94      inference(unflattening,[status(thm)],[c_283]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_15,negated_conjecture,
% 1.45/0.94      ( v1_funct_1(sK3) ),
% 1.45/0.94      inference(cnf_transformation,[],[f35]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_13,negated_conjecture,
% 1.45/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.45/0.94      inference(cnf_transformation,[],[f37]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_288,plain,
% 1.45/0.94      ( ~ v1_funct_1(X1)
% 1.45/0.94      | ~ r2_hidden(X0,sK1)
% 1.45/0.94      | ~ v1_relat_1(X1)
% 1.45/0.94      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.45/0.94      | k1_xboole_0 = sK2 ),
% 1.45/0.94      inference(global_propositional_subsumption,
% 1.45/0.94                [status(thm)],
% 1.45/0.94                [c_284,c_15,c_13]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_289,plain,
% 1.45/0.94      ( ~ r2_hidden(X0,sK1)
% 1.45/0.94      | ~ v1_funct_1(X1)
% 1.45/0.94      | ~ v1_relat_1(X1)
% 1.45/0.94      | k1_funct_1(X1,k1_funct_1(sK3,X0)) = k1_funct_1(k5_relat_1(sK3,X1),X0)
% 1.45/0.94      | k1_xboole_0 = sK2 ),
% 1.45/0.94      inference(renaming,[status(thm)],[c_288]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_404,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0,X1)
% 1.45/0.94      | ~ v1_funct_1(X2)
% 1.45/0.94      | ~ v1_relat_1(X2)
% 1.45/0.94      | v1_xboole_0(X1)
% 1.45/0.94      | X3 != X0
% 1.45/0.94      | k1_funct_1(k5_relat_1(sK3,X2),X3) = k1_funct_1(X2,k1_funct_1(sK3,X3))
% 1.45/0.94      | sK2 = k1_xboole_0
% 1.45/0.94      | sK1 != X1 ),
% 1.45/0.94      inference(resolution_lifted,[status(thm)],[c_2,c_289]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_405,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0,sK1)
% 1.45/0.94      | ~ v1_funct_1(X1)
% 1.45/0.94      | ~ v1_relat_1(X1)
% 1.45/0.94      | v1_xboole_0(sK1)
% 1.45/0.94      | k1_funct_1(k5_relat_1(sK3,X1),X0) = k1_funct_1(X1,k1_funct_1(sK3,X0))
% 1.45/0.94      | sK2 = k1_xboole_0 ),
% 1.45/0.94      inference(unflattening,[status(thm)],[c_404]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_614,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0_50,sK1)
% 1.45/0.94      | ~ v1_funct_1(X1_50)
% 1.45/0.94      | ~ v1_relat_1(X1_50)
% 1.45/0.94      | v1_xboole_0(sK1)
% 1.45/0.94      | sK2 = k1_xboole_0
% 1.45/0.94      | k1_funct_1(k5_relat_1(sK3,X1_50),X0_50) = k1_funct_1(X1_50,k1_funct_1(sK3,X0_50)) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_405]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_629,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0_50,sK1)
% 1.45/0.94      | ~ v1_funct_1(X1_50)
% 1.45/0.94      | ~ v1_relat_1(X1_50)
% 1.45/0.94      | k1_funct_1(k5_relat_1(sK3,X1_50),X0_50) = k1_funct_1(X1_50,k1_funct_1(sK3,X0_50))
% 1.45/0.94      | ~ sP0_iProver_split ),
% 1.45/0.94      inference(splitting,
% 1.45/0.94                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.45/0.94                [c_614]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_940,plain,
% 1.45/0.94      ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
% 1.45/0.94      | m1_subset_1(X1_50,sK1) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | v1_relat_1(X0_50) != iProver_top
% 1.45/0.94      | sP0_iProver_split != iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_16,negated_conjecture,
% 1.45/0.94      ( ~ v1_xboole_0(sK2) ),
% 1.45/0.94      inference(cnf_transformation,[],[f34]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_0,plain,
% 1.45/0.94      ( v1_xboole_0(k1_xboole_0) ),
% 1.45/0.94      inference(cnf_transformation,[],[f27]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_41,plain,
% 1.45/0.94      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_8,negated_conjecture,
% 1.45/0.94      ( k1_xboole_0 != sK1 ),
% 1.45/0.94      inference(cnf_transformation,[],[f42]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_623,negated_conjecture,
% 1.45/0.94      ( k1_xboole_0 != sK1 ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_8]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_630,plain,
% 1.45/0.94      ( v1_xboole_0(sK1) | sP0_iProver_split | sK2 = k1_xboole_0 ),
% 1.45/0.94      inference(splitting,
% 1.45/0.94                [splitting(split),new_symbols(definition,[])],
% 1.45/0.94                [c_614]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_687,plain,
% 1.45/0.94      ( sK2 = k1_xboole_0
% 1.45/0.94      | v1_xboole_0(sK1) = iProver_top
% 1.45/0.94      | sP0_iProver_split = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_688,plain,
% 1.45/0.94      ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
% 1.45/0.94      | m1_subset_1(X1_50,sK1) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | v1_relat_1(X0_50) != iProver_top
% 1.45/0.94      | sP0_iProver_split != iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1,plain,
% 1.45/0.94      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 1.45/0.94      inference(cnf_transformation,[],[f28]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_627,plain,
% 1.45/0.94      ( ~ v1_xboole_0(X0_51) | ~ v1_xboole_0(X1_51) | X1_51 = X0_51 ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_1]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1050,plain,
% 1.45/0.94      ( ~ v1_xboole_0(sK1)
% 1.45/0.94      | ~ v1_xboole_0(k1_xboole_0)
% 1.45/0.94      | k1_xboole_0 = sK1 ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_627]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1051,plain,
% 1.45/0.94      ( k1_xboole_0 = sK1
% 1.45/0.94      | v1_xboole_0(sK1) != iProver_top
% 1.45/0.94      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_639,plain,
% 1.45/0.94      ( ~ v1_xboole_0(X0_51) | v1_xboole_0(X1_51) | X1_51 != X0_51 ),
% 1.45/0.94      theory(equality) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1057,plain,
% 1.45/0.94      ( v1_xboole_0(X0_51)
% 1.45/0.94      | ~ v1_xboole_0(k1_xboole_0)
% 1.45/0.94      | X0_51 != k1_xboole_0 ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_639]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1059,plain,
% 1.45/0.94      ( v1_xboole_0(sK2)
% 1.45/0.94      | ~ v1_xboole_0(k1_xboole_0)
% 1.45/0.94      | sK2 != k1_xboole_0 ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_1057]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1626,plain,
% 1.45/0.94      ( v1_relat_1(X0_50) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | m1_subset_1(X1_50,sK1) != iProver_top
% 1.45/0.94      | k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50)) ),
% 1.45/0.94      inference(global_propositional_subsumption,
% 1.45/0.94                [status(thm)],
% 1.45/0.94                [c_940,c_16,c_0,c_41,c_623,c_687,c_688,c_1051,c_1059]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1627,plain,
% 1.45/0.94      ( k1_funct_1(k5_relat_1(sK3,X0_50),X1_50) = k1_funct_1(X0_50,k1_funct_1(sK3,X1_50))
% 1.45/0.94      | m1_subset_1(X1_50,sK1) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | v1_relat_1(X0_50) != iProver_top ),
% 1.45/0.94      inference(renaming,[status(thm)],[c_1626]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1636,plain,
% 1.45/0.94      ( k1_funct_1(X0_50,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,X0_50),sK5)
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | v1_relat_1(X0_50) != iProver_top ),
% 1.45/0.94      inference(superposition,[status(thm)],[c_932,c_1627]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1682,plain,
% 1.45/0.94      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 1.45/0.94      | v1_relat_1(sK4) != iProver_top ),
% 1.45/0.94      inference(superposition,[status(thm)],[c_934,c_1636]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_9,negated_conjecture,
% 1.45/0.94      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 1.45/0.94      inference(cnf_transformation,[],[f41]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_622,negated_conjecture,
% 1.45/0.94      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_9]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_931,plain,
% 1.45/0.94      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_4,plain,
% 1.45/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 1.45/0.94      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X3,X4))
% 1.45/0.94      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 1.45/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.94      | ~ v1_funct_1(X4)
% 1.45/0.94      | ~ v1_funct_1(X0)
% 1.45/0.94      | k1_partfun1(X1,X2,X2,X3,X0,X4) = k8_funct_2(X1,X2,X3,X0,X4)
% 1.45/0.94      | k1_xboole_0 = X2 ),
% 1.45/0.94      inference(cnf_transformation,[],[f31]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_310,plain,
% 1.45/0.94      ( ~ r1_tarski(k2_relset_1(X0,X1,X2),k1_relset_1(X1,X3,X4))
% 1.45/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.45/0.94      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 1.45/0.94      | ~ v1_funct_1(X4)
% 1.45/0.94      | ~ v1_funct_1(X2)
% 1.45/0.94      | k1_partfun1(X0,X1,X1,X3,X2,X4) = k8_funct_2(X0,X1,X3,X2,X4)
% 1.45/0.94      | sK2 != X1
% 1.45/0.94      | sK1 != X0
% 1.45/0.94      | sK3 != X2
% 1.45/0.94      | k1_xboole_0 = X1 ),
% 1.45/0.94      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_311,plain,
% 1.45/0.94      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.45/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.45/0.94      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.45/0.94      | ~ v1_funct_1(X1)
% 1.45/0.94      | ~ v1_funct_1(sK3)
% 1.45/0.94      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.45/0.94      | k1_xboole_0 = sK2 ),
% 1.45/0.94      inference(unflattening,[status(thm)],[c_310]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_315,plain,
% 1.45/0.94      ( ~ v1_funct_1(X1)
% 1.45/0.94      | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.45/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.45/0.94      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.45/0.94      | k1_xboole_0 = sK2 ),
% 1.45/0.94      inference(global_propositional_subsumption,
% 1.45/0.94                [status(thm)],
% 1.45/0.94                [c_311,c_15,c_13]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_316,plain,
% 1.45/0.94      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
% 1.45/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
% 1.45/0.94      | ~ v1_funct_1(X1)
% 1.45/0.94      | k1_partfun1(sK1,sK2,sK2,X0,sK3,X1) = k8_funct_2(sK1,sK2,X0,sK3,X1)
% 1.45/0.94      | k1_xboole_0 = sK2 ),
% 1.45/0.94      inference(renaming,[status(thm)],[c_315]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_615,plain,
% 1.45/0.94      ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50))
% 1.45/0.94      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51)))
% 1.45/0.94      | ~ v1_funct_1(X0_50)
% 1.45/0.94      | k1_xboole_0 = sK2
% 1.45/0.94      | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_316]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_938,plain,
% 1.45/0.94      ( k1_xboole_0 = sK2
% 1.45/0.94      | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
% 1.45/0.94      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50)) != iProver_top
% 1.45/0.94      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_633,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_665,plain,
% 1.45/0.94      ( sK2 = sK2 ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_633]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_684,plain,
% 1.45/0.94      ( k1_xboole_0 = sK2
% 1.45/0.94      | k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
% 1.45/0.94      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50)) != iProver_top
% 1.45/0.94      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_638,plain,
% 1.45/0.94      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 1.45/0.94      theory(equality) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1207,plain,
% 1.45/0.94      ( X0_51 != X1_51 | X0_51 = k1_xboole_0 | k1_xboole_0 != X1_51 ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_638]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1208,plain,
% 1.45/0.94      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_1207]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1526,plain,
% 1.45/0.94      ( k1_partfun1(sK1,sK2,sK2,X0_51,sK3,X0_50) = k8_funct_2(sK1,sK2,X0_51,sK3,X0_50)
% 1.45/0.94      | r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0_51,X0_50)) != iProver_top
% 1.45/0.94      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK2,X0_51))) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top ),
% 1.45/0.94      inference(global_propositional_subsumption,
% 1.45/0.94                [status(thm)],
% 1.45/0.94                [c_938,c_16,c_0,c_665,c_684,c_1059,c_1208]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1536,plain,
% 1.45/0.94      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
% 1.45/0.94      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 1.45/0.94      | v1_funct_1(sK4) != iProver_top ),
% 1.45/0.94      inference(superposition,[status(thm)],[c_931,c_1526]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_11,negated_conjecture,
% 1.45/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 1.45/0.94      inference(cnf_transformation,[],[f39]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_620,negated_conjecture,
% 1.45/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_11]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_933,plain,
% 1.45/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_618,negated_conjecture,
% 1.45/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_13]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_935,plain,
% 1.45/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_5,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.94      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 1.45/0.94      | ~ v1_funct_1(X3)
% 1.45/0.94      | ~ v1_funct_1(X0)
% 1.45/0.94      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 1.45/0.94      inference(cnf_transformation,[],[f32]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_625,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 1.45/0.94      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 1.45/0.94      | ~ v1_funct_1(X1_50)
% 1.45/0.94      | ~ v1_funct_1(X0_50)
% 1.45/0.94      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_5]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_930,plain,
% 1.45/0.94      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 1.45/0.94      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 1.45/0.94      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | v1_funct_1(X1_50) != iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1304,plain,
% 1.45/0.94      ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
% 1.45/0.94      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | v1_funct_1(sK3) != iProver_top ),
% 1.45/0.94      inference(superposition,[status(thm)],[c_935,c_930]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_18,plain,
% 1.45/0.94      ( v1_funct_1(sK3) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1451,plain,
% 1.45/0.94      ( v1_funct_1(X0_50) != iProver_top
% 1.45/0.94      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.45/0.94      | k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50) ),
% 1.45/0.94      inference(global_propositional_subsumption,
% 1.45/0.94                [status(thm)],
% 1.45/0.94                [c_1304,c_18]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1452,plain,
% 1.45/0.94      ( k1_partfun1(sK1,sK2,X0_51,X1_51,sK3,X0_50) = k5_relat_1(sK3,X0_50)
% 1.45/0.94      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 1.45/0.94      | v1_funct_1(X0_50) != iProver_top ),
% 1.45/0.94      inference(renaming,[status(thm)],[c_1451]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1458,plain,
% 1.45/0.94      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 1.45/0.94      | v1_funct_1(sK4) != iProver_top ),
% 1.45/0.94      inference(superposition,[status(thm)],[c_933,c_1452]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1096,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 1.45/0.94      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.45/0.94      | ~ v1_funct_1(X0_50)
% 1.45/0.94      | ~ v1_funct_1(sK4)
% 1.45/0.94      | k1_partfun1(X0_51,X1_51,sK2,sK0,X0_50,sK4) = k5_relat_1(X0_50,sK4) ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_625]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1184,plain,
% 1.45/0.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.45/0.94      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.45/0.94      | ~ v1_funct_1(sK3)
% 1.45/0.94      | ~ v1_funct_1(sK4)
% 1.45/0.94      | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_1096]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1471,plain,
% 1.45/0.94      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.45/0.94      inference(global_propositional_subsumption,
% 1.45/0.94                [status(thm)],
% 1.45/0.94                [c_1458,c_15,c_13,c_12,c_11,c_1184]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1537,plain,
% 1.45/0.94      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 1.45/0.94      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 1.45/0.94      | v1_funct_1(sK4) != iProver_top ),
% 1.45/0.94      inference(light_normalisation,[status(thm)],[c_1536,c_1471]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_21,plain,
% 1.45/0.94      ( v1_funct_1(sK4) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_22,plain,
% 1.45/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1582,plain,
% 1.45/0.94      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 1.45/0.94      inference(global_propositional_subsumption,
% 1.45/0.94                [status(thm)],
% 1.45/0.94                [c_1537,c_21,c_22]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_7,negated_conjecture,
% 1.45/0.94      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 1.45/0.94      inference(cnf_transformation,[],[f43]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_624,negated_conjecture,
% 1.45/0.94      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_7]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1585,plain,
% 1.45/0.94      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 1.45/0.94      inference(demodulation,[status(thm)],[c_1582,c_624]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_3,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.45/0.94      | v1_relat_1(X0) ),
% 1.45/0.94      inference(cnf_transformation,[],[f30]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_626,plain,
% 1.45/0.94      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 1.45/0.94      | v1_relat_1(X0_50) ),
% 1.45/0.94      inference(subtyping,[status(esa)],[c_3]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1044,plain,
% 1.45/0.94      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 1.45/0.94      | v1_relat_1(sK4) ),
% 1.45/0.94      inference(instantiation,[status(thm)],[c_626]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(c_1045,plain,
% 1.45/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 1.45/0.94      | v1_relat_1(sK4) = iProver_top ),
% 1.45/0.94      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 1.45/0.94  
% 1.45/0.94  cnf(contradiction,plain,
% 1.45/0.94      ( $false ),
% 1.45/0.94      inference(minisat,[status(thm)],[c_1682,c_1585,c_1045,c_22]) ).
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 1.45/0.94  
% 1.45/0.94  ------                               Statistics
% 1.45/0.94  
% 1.45/0.94  ------ General
% 1.45/0.94  
% 1.45/0.94  abstr_ref_over_cycles:                  0
% 1.45/0.94  abstr_ref_under_cycles:                 0
% 1.45/0.94  gc_basic_clause_elim:                   0
% 1.45/0.94  forced_gc_time:                         0
% 1.45/0.94  parsing_time:                           0.008
% 1.45/0.94  unif_index_cands_time:                  0.
% 1.45/0.94  unif_index_add_time:                    0.
% 1.45/0.94  orderings_time:                         0.
% 1.45/0.94  out_proof_time:                         0.011
% 1.45/0.94  total_time:                             0.087
% 1.45/0.94  num_of_symbols:                         59
% 1.45/0.94  num_of_terms:                           1732
% 1.45/0.94  
% 1.45/0.94  ------ Preprocessing
% 1.45/0.94  
% 1.45/0.94  num_of_splits:                          1
% 1.45/0.94  num_of_split_atoms:                     1
% 1.45/0.94  num_of_reused_defs:                     0
% 1.45/0.94  num_eq_ax_congr_red:                    19
% 1.45/0.94  num_of_sem_filtered_clauses:            1
% 1.45/0.94  num_of_subtypes:                        5
% 1.45/0.94  monotx_restored_types:                  0
% 1.45/0.94  sat_num_of_epr_types:                   0
% 1.45/0.94  sat_num_of_non_cyclic_types:            0
% 1.45/0.94  sat_guarded_non_collapsed_types:        1
% 1.45/0.94  num_pure_diseq_elim:                    0
% 1.45/0.94  simp_replaced_by:                       0
% 1.45/0.94  res_preprocessed:                       103
% 1.45/0.94  prep_upred:                             0
% 1.45/0.94  prep_unflattend:                        14
% 1.45/0.94  smt_new_axioms:                         0
% 1.45/0.94  pred_elim_cands:                        5
% 1.45/0.94  pred_elim:                              2
% 1.45/0.94  pred_elim_cl:                           2
% 1.45/0.94  pred_elim_cycles:                       10
% 1.45/0.94  merged_defs:                            0
% 1.45/0.94  merged_defs_ncl:                        0
% 1.45/0.94  bin_hyper_res:                          0
% 1.45/0.94  prep_cycles:                            4
% 1.45/0.94  pred_elim_time:                         0.008
% 1.45/0.94  splitting_time:                         0.
% 1.45/0.94  sem_filter_time:                        0.
% 1.45/0.94  monotx_time:                            0.
% 1.45/0.94  subtype_inf_time:                       0.
% 1.45/0.94  
% 1.45/0.94  ------ Problem properties
% 1.45/0.94  
% 1.45/0.94  clauses:                                16
% 1.45/0.94  conjectures:                            9
% 1.45/0.94  epr:                                    8
% 1.45/0.94  horn:                                   14
% 1.45/0.94  ground:                                 11
% 1.45/0.94  unary:                                  10
% 1.45/0.94  binary:                                 1
% 1.45/0.94  lits:                                   33
% 1.45/0.94  lits_eq:                                8
% 1.45/0.94  fd_pure:                                0
% 1.45/0.94  fd_pseudo:                              0
% 1.45/0.94  fd_cond:                                0
% 1.45/0.94  fd_pseudo_cond:                         1
% 1.45/0.94  ac_symbols:                             0
% 1.45/0.94  
% 1.45/0.94  ------ Propositional Solver
% 1.45/0.94  
% 1.45/0.94  prop_solver_calls:                      26
% 1.45/0.94  prop_fast_solver_calls:                 653
% 1.45/0.94  smt_solver_calls:                       0
% 1.45/0.94  smt_fast_solver_calls:                  0
% 1.45/0.94  prop_num_of_clauses:                    444
% 1.45/0.94  prop_preprocess_simplified:             2461
% 1.45/0.94  prop_fo_subsumed:                       14
% 1.45/0.94  prop_solver_time:                       0.
% 1.45/0.94  smt_solver_time:                        0.
% 1.45/0.94  smt_fast_solver_time:                   0.
% 1.45/0.94  prop_fast_solver_time:                  0.
% 1.45/0.94  prop_unsat_core_time:                   0.
% 1.45/0.94  
% 1.45/0.94  ------ QBF
% 1.45/0.94  
% 1.45/0.94  qbf_q_res:                              0
% 1.45/0.94  qbf_num_tautologies:                    0
% 1.45/0.94  qbf_prep_cycles:                        0
% 1.45/0.94  
% 1.45/0.94  ------ BMC1
% 1.45/0.94  
% 1.45/0.94  bmc1_current_bound:                     -1
% 1.45/0.94  bmc1_last_solved_bound:                 -1
% 1.45/0.94  bmc1_unsat_core_size:                   -1
% 1.45/0.94  bmc1_unsat_core_parents_size:           -1
% 1.45/0.94  bmc1_merge_next_fun:                    0
% 1.45/0.94  bmc1_unsat_core_clauses_time:           0.
% 1.45/0.94  
% 1.45/0.94  ------ Instantiation
% 1.45/0.94  
% 1.45/0.94  inst_num_of_clauses:                    155
% 1.45/0.94  inst_num_in_passive:                    18
% 1.45/0.94  inst_num_in_active:                     134
% 1.45/0.94  inst_num_in_unprocessed:                3
% 1.45/0.94  inst_num_of_loops:                      140
% 1.45/0.94  inst_num_of_learning_restarts:          0
% 1.45/0.94  inst_num_moves_active_passive:          3
% 1.45/0.94  inst_lit_activity:                      0
% 1.45/0.94  inst_lit_activity_moves:                0
% 1.45/0.94  inst_num_tautologies:                   0
% 1.45/0.94  inst_num_prop_implied:                  0
% 1.45/0.94  inst_num_existing_simplified:           0
% 1.45/0.94  inst_num_eq_res_simplified:             0
% 1.45/0.94  inst_num_child_elim:                    0
% 1.45/0.94  inst_num_of_dismatching_blockings:      16
% 1.45/0.94  inst_num_of_non_proper_insts:           137
% 1.45/0.94  inst_num_of_duplicates:                 0
% 1.45/0.94  inst_inst_num_from_inst_to_res:         0
% 1.45/0.94  inst_dismatching_checking_time:         0.
% 1.45/0.94  
% 1.45/0.94  ------ Resolution
% 1.45/0.94  
% 1.45/0.94  res_num_of_clauses:                     0
% 1.45/0.94  res_num_in_passive:                     0
% 1.45/0.94  res_num_in_active:                      0
% 1.45/0.94  res_num_of_loops:                       107
% 1.45/0.94  res_forward_subset_subsumed:            31
% 1.45/0.94  res_backward_subset_subsumed:           0
% 1.45/0.94  res_forward_subsumed:                   0
% 1.45/0.94  res_backward_subsumed:                  0
% 1.45/0.94  res_forward_subsumption_resolution:     0
% 1.45/0.94  res_backward_subsumption_resolution:    0
% 1.45/0.94  res_clause_to_clause_subsumption:       61
% 1.45/0.94  res_orphan_elimination:                 0
% 1.45/0.94  res_tautology_del:                      20
% 1.45/0.94  res_num_eq_res_simplified:              0
% 1.45/0.94  res_num_sel_changes:                    0
% 1.45/0.94  res_moves_from_active_to_pass:          0
% 1.45/0.94  
% 1.45/0.94  ------ Superposition
% 1.45/0.94  
% 1.45/0.94  sup_time_total:                         0.
% 1.45/0.94  sup_time_generating:                    0.
% 1.45/0.94  sup_time_sim_full:                      0.
% 1.45/0.94  sup_time_sim_immed:                     0.
% 1.45/0.94  
% 1.45/0.94  sup_num_of_clauses:                     29
% 1.45/0.94  sup_num_in_active:                      26
% 1.45/0.94  sup_num_in_passive:                     3
% 1.45/0.94  sup_num_of_loops:                       26
% 1.45/0.94  sup_fw_superposition:                   14
% 1.45/0.94  sup_bw_superposition:                   0
% 1.45/0.94  sup_immediate_simplified:               1
% 1.45/0.94  sup_given_eliminated:                   0
% 1.45/0.94  comparisons_done:                       0
% 1.45/0.94  comparisons_avoided:                    0
% 1.45/0.94  
% 1.45/0.94  ------ Simplifications
% 1.45/0.94  
% 1.45/0.94  
% 1.45/0.94  sim_fw_subset_subsumed:                 0
% 1.45/0.94  sim_bw_subset_subsumed:                 0
% 1.45/0.94  sim_fw_subsumed:                        0
% 1.45/0.94  sim_bw_subsumed:                        0
% 1.45/0.94  sim_fw_subsumption_res:                 0
% 1.45/0.94  sim_bw_subsumption_res:                 0
% 1.45/0.94  sim_tautology_del:                      0
% 1.45/0.94  sim_eq_tautology_del:                   1
% 1.45/0.94  sim_eq_res_simp:                        0
% 1.45/0.94  sim_fw_demodulated:                     0
% 1.45/0.94  sim_bw_demodulated:                     1
% 1.45/0.94  sim_light_normalised:                   1
% 1.45/0.94  sim_joinable_taut:                      0
% 1.45/0.94  sim_joinable_simp:                      0
% 1.45/0.94  sim_ac_normalised:                      0
% 1.45/0.94  sim_smt_subsumption:                    0
% 1.45/0.94  
%------------------------------------------------------------------------------
