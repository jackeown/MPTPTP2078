%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:49 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 441 expanded)
%              Number of clauses        :   98 ( 127 expanded)
%              Number of leaves         :   24 ( 145 expanded)
%              Depth                    :   16
%              Number of atoms          :  562 (3144 expanded)
%              Number of equality atoms :  225 ( 841 expanded)
%              Maximal formula depth    :   17 (   4 average)
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
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK8) != k7_partfun1(X0,X4,k1_funct_1(X3,sK8))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK8,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK7),X5) != k7_partfun1(X0,sK7,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK7))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK6,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK6,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK6),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK6,X1,X2)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
                  ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,X3,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK4
                  & r1_tarski(k2_relset_1(sK4,sK5,X3),k1_relset_1(sK5,sK3,X4))
                  & m1_subset_1(X5,sK4) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X3,sK4,sK5)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8))
    & k1_xboole_0 != sK4
    & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))
    & m1_subset_1(sK8,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f48,f62,f61,f60,f59])).

fof(f98,plain,(
    m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f55])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f95,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f94,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f39])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f96,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) ),
    inference(cnf_transformation,[],[f63])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2964,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2980,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4915,plain,
    ( r2_hidden(sK8,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2964,c_2980])).

cnf(c_44,plain,
    ( m1_subset_1(sK8,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_5,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3241,plain,
    ( r2_hidden(sK2(sK4),sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3242,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(sK2(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3241])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3416,plain,
    ( ~ r2_hidden(sK2(sK4),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3417,plain,
    ( r2_hidden(sK2(sK4),sK4) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3416])).

cnf(c_3612,plain,
    ( ~ m1_subset_1(X0,sK4)
    | r2_hidden(X0,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_4887,plain,
    ( ~ m1_subset_1(sK8,sK4)
    | r2_hidden(sK8,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3612])).

cnf(c_4888,plain,
    ( m1_subset_1(sK8,sK4) != iProver_top
    | r2_hidden(sK8,sK4) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4887])).

cnf(c_5208,plain,
    ( r2_hidden(sK8,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4915,c_44,c_29,c_3242,c_3417,c_4888])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2961,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2967,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5460,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2961,c_2967])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2975,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4838,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2961,c_2975])).

cnf(c_5464,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5460,c_4838])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_38,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_40,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2157,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3251,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2157])).

cnf(c_3252,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3251])).

cnf(c_3254,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3252])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2989,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2983,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2976,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3866,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_2976])).

cnf(c_6358,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2989,c_3866])).

cnf(c_8793,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5464,c_38,c_40,c_3254,c_6358])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2973,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6332,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2961,c_2973])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_13])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_509,plain,
    ( r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_15])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_509])).

cnf(c_2956,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_6637,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6332,c_2956])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_39,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_7645,plain,
    ( r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6637,c_39])).

cnf(c_7646,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7645])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2963,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_16,c_26])).

cnf(c_486,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_15])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_486])).

cnf(c_2957,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_3880,plain,
    ( k7_partfun1(sK3,sK7,X0) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2963,c_2957])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_42,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4315,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | k7_partfun1(sK3,sK7,X0) = k1_funct_1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3880,c_42])).

cnf(c_4316,plain,
    ( k7_partfun1(sK3,sK7,X0) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4315])).

cnf(c_7657,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,X0)) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
    | r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7646,c_4316])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2974,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4819,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2961,c_2974])).

cnf(c_30,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2965,plain,
    ( r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5016,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_relset_1(sK5,sK3,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4819,c_2965])).

cnf(c_4837,plain,
    ( k1_relset_1(sK5,sK3,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2963,c_2975])).

cnf(c_5108,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5016,c_4837])).

cnf(c_8515,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,X0)) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7657,c_5108])).

cnf(c_8797,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,X0)) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8793,c_8515])).

cnf(c_12369,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) = k1_funct_1(sK7,k1_funct_1(sK6,sK8)) ),
    inference(superposition,[status(thm)],[c_5208,c_8797])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f91])).

cnf(c_2966,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4667,plain,
    ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2965,c_2966])).

cnf(c_41,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2155,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2184,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2155])).

cnf(c_2156,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3292,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_3293,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3292])).

cnf(c_5989,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK6,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4667,c_38,c_39,c_40,c_41,c_42,c_43,c_29,c_2184,c_3293])).

cnf(c_5990,plain,
    ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5989])).

cnf(c_5997,plain,
    ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) = k1_funct_1(sK7,k1_funct_1(sK6,sK8)) ),
    inference(superposition,[status(thm)],[c_2964,c_5990])).

cnf(c_28,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_5999,plain,
    ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) ),
    inference(demodulation,[status(thm)],[c_5997,c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12369,c_5999])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.35/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.03  
% 3.35/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.35/1.03  
% 3.35/1.03  ------  iProver source info
% 3.35/1.03  
% 3.35/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.35/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.35/1.03  git: non_committed_changes: false
% 3.35/1.03  git: last_make_outside_of_git: false
% 3.35/1.03  
% 3.35/1.03  ------ 
% 3.35/1.03  
% 3.35/1.03  ------ Input Options
% 3.35/1.03  
% 3.35/1.03  --out_options                           all
% 3.35/1.03  --tptp_safe_out                         true
% 3.35/1.03  --problem_path                          ""
% 3.35/1.03  --include_path                          ""
% 3.35/1.03  --clausifier                            res/vclausify_rel
% 3.35/1.03  --clausifier_options                    --mode clausify
% 3.35/1.03  --stdin                                 false
% 3.35/1.03  --stats_out                             all
% 3.35/1.03  
% 3.35/1.03  ------ General Options
% 3.35/1.03  
% 3.35/1.03  --fof                                   false
% 3.35/1.03  --time_out_real                         305.
% 3.35/1.03  --time_out_virtual                      -1.
% 3.35/1.03  --symbol_type_check                     false
% 3.35/1.03  --clausify_out                          false
% 3.35/1.03  --sig_cnt_out                           false
% 3.81/1.03  --trig_cnt_out                          false
% 3.81/1.03  --trig_cnt_out_tolerance                1.
% 3.81/1.03  --trig_cnt_out_sk_spl                   false
% 3.81/1.03  --abstr_cl_out                          false
% 3.81/1.03  
% 3.81/1.03  ------ Global Options
% 3.81/1.03  
% 3.81/1.03  --schedule                              default
% 3.81/1.03  --add_important_lit                     false
% 3.81/1.03  --prop_solver_per_cl                    1000
% 3.81/1.03  --min_unsat_core                        false
% 3.81/1.03  --soft_assumptions                      false
% 3.81/1.03  --soft_lemma_size                       3
% 3.81/1.03  --prop_impl_unit_size                   0
% 3.81/1.03  --prop_impl_unit                        []
% 3.81/1.03  --share_sel_clauses                     true
% 3.81/1.03  --reset_solvers                         false
% 3.81/1.03  --bc_imp_inh                            [conj_cone]
% 3.81/1.03  --conj_cone_tolerance                   3.
% 3.81/1.03  --extra_neg_conj                        none
% 3.81/1.03  --large_theory_mode                     true
% 3.81/1.03  --prolific_symb_bound                   200
% 3.81/1.03  --lt_threshold                          2000
% 3.81/1.03  --clause_weak_htbl                      true
% 3.81/1.03  --gc_record_bc_elim                     false
% 3.81/1.03  
% 3.81/1.03  ------ Preprocessing Options
% 3.81/1.03  
% 3.81/1.03  --preprocessing_flag                    true
% 3.81/1.03  --time_out_prep_mult                    0.1
% 3.81/1.03  --splitting_mode                        input
% 3.81/1.03  --splitting_grd                         true
% 3.81/1.03  --splitting_cvd                         false
% 3.81/1.03  --splitting_cvd_svl                     false
% 3.81/1.03  --splitting_nvd                         32
% 3.81/1.03  --sub_typing                            true
% 3.81/1.03  --prep_gs_sim                           true
% 3.81/1.03  --prep_unflatten                        true
% 3.81/1.03  --prep_res_sim                          true
% 3.81/1.03  --prep_upred                            true
% 3.81/1.03  --prep_sem_filter                       exhaustive
% 3.81/1.03  --prep_sem_filter_out                   false
% 3.81/1.03  --pred_elim                             true
% 3.81/1.03  --res_sim_input                         true
% 3.81/1.03  --eq_ax_congr_red                       true
% 3.81/1.03  --pure_diseq_elim                       true
% 3.81/1.03  --brand_transform                       false
% 3.81/1.03  --non_eq_to_eq                          false
% 3.81/1.03  --prep_def_merge                        true
% 3.81/1.03  --prep_def_merge_prop_impl              false
% 3.81/1.03  --prep_def_merge_mbd                    true
% 3.81/1.03  --prep_def_merge_tr_red                 false
% 3.81/1.03  --prep_def_merge_tr_cl                  false
% 3.81/1.03  --smt_preprocessing                     true
% 3.81/1.03  --smt_ac_axioms                         fast
% 3.81/1.03  --preprocessed_out                      false
% 3.81/1.03  --preprocessed_stats                    false
% 3.81/1.03  
% 3.81/1.03  ------ Abstraction refinement Options
% 3.81/1.03  
% 3.81/1.03  --abstr_ref                             []
% 3.81/1.03  --abstr_ref_prep                        false
% 3.81/1.03  --abstr_ref_until_sat                   false
% 3.81/1.03  --abstr_ref_sig_restrict                funpre
% 3.81/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.03  --abstr_ref_under                       []
% 3.81/1.03  
% 3.81/1.03  ------ SAT Options
% 3.81/1.03  
% 3.81/1.03  --sat_mode                              false
% 3.81/1.03  --sat_fm_restart_options                ""
% 3.81/1.03  --sat_gr_def                            false
% 3.81/1.03  --sat_epr_types                         true
% 3.81/1.03  --sat_non_cyclic_types                  false
% 3.81/1.03  --sat_finite_models                     false
% 3.81/1.03  --sat_fm_lemmas                         false
% 3.81/1.03  --sat_fm_prep                           false
% 3.81/1.03  --sat_fm_uc_incr                        true
% 3.81/1.03  --sat_out_model                         small
% 3.81/1.03  --sat_out_clauses                       false
% 3.81/1.03  
% 3.81/1.03  ------ QBF Options
% 3.81/1.03  
% 3.81/1.03  --qbf_mode                              false
% 3.81/1.03  --qbf_elim_univ                         false
% 3.81/1.03  --qbf_dom_inst                          none
% 3.81/1.03  --qbf_dom_pre_inst                      false
% 3.81/1.03  --qbf_sk_in                             false
% 3.81/1.03  --qbf_pred_elim                         true
% 3.81/1.03  --qbf_split                             512
% 3.81/1.03  
% 3.81/1.03  ------ BMC1 Options
% 3.81/1.03  
% 3.81/1.03  --bmc1_incremental                      false
% 3.81/1.03  --bmc1_axioms                           reachable_all
% 3.81/1.03  --bmc1_min_bound                        0
% 3.81/1.03  --bmc1_max_bound                        -1
% 3.81/1.03  --bmc1_max_bound_default                -1
% 3.81/1.03  --bmc1_symbol_reachability              true
% 3.81/1.03  --bmc1_property_lemmas                  false
% 3.81/1.03  --bmc1_k_induction                      false
% 3.81/1.03  --bmc1_non_equiv_states                 false
% 3.81/1.03  --bmc1_deadlock                         false
% 3.81/1.03  --bmc1_ucm                              false
% 3.81/1.03  --bmc1_add_unsat_core                   none
% 3.81/1.03  --bmc1_unsat_core_children              false
% 3.81/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.03  --bmc1_out_stat                         full
% 3.81/1.03  --bmc1_ground_init                      false
% 3.81/1.03  --bmc1_pre_inst_next_state              false
% 3.81/1.03  --bmc1_pre_inst_state                   false
% 3.81/1.03  --bmc1_pre_inst_reach_state             false
% 3.81/1.03  --bmc1_out_unsat_core                   false
% 3.81/1.03  --bmc1_aig_witness_out                  false
% 3.81/1.03  --bmc1_verbose                          false
% 3.81/1.03  --bmc1_dump_clauses_tptp                false
% 3.81/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.03  --bmc1_dump_file                        -
% 3.81/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.03  --bmc1_ucm_extend_mode                  1
% 3.81/1.03  --bmc1_ucm_init_mode                    2
% 3.81/1.03  --bmc1_ucm_cone_mode                    none
% 3.81/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.03  --bmc1_ucm_relax_model                  4
% 3.81/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.03  --bmc1_ucm_layered_model                none
% 3.81/1.03  --bmc1_ucm_max_lemma_size               10
% 3.81/1.03  
% 3.81/1.03  ------ AIG Options
% 3.81/1.03  
% 3.81/1.03  --aig_mode                              false
% 3.81/1.03  
% 3.81/1.03  ------ Instantiation Options
% 3.81/1.03  
% 3.81/1.03  --instantiation_flag                    true
% 3.81/1.03  --inst_sos_flag                         false
% 3.81/1.03  --inst_sos_phase                        true
% 3.81/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.03  --inst_lit_sel_side                     num_symb
% 3.81/1.03  --inst_solver_per_active                1400
% 3.81/1.03  --inst_solver_calls_frac                1.
% 3.81/1.03  --inst_passive_queue_type               priority_queues
% 3.81/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.03  --inst_passive_queues_freq              [25;2]
% 3.81/1.03  --inst_dismatching                      true
% 3.81/1.03  --inst_eager_unprocessed_to_passive     true
% 3.81/1.03  --inst_prop_sim_given                   true
% 3.81/1.03  --inst_prop_sim_new                     false
% 3.81/1.03  --inst_subs_new                         false
% 3.81/1.03  --inst_eq_res_simp                      false
% 3.81/1.03  --inst_subs_given                       false
% 3.81/1.03  --inst_orphan_elimination               true
% 3.81/1.03  --inst_learning_loop_flag               true
% 3.81/1.03  --inst_learning_start                   3000
% 3.81/1.03  --inst_learning_factor                  2
% 3.81/1.03  --inst_start_prop_sim_after_learn       3
% 3.81/1.03  --inst_sel_renew                        solver
% 3.81/1.03  --inst_lit_activity_flag                true
% 3.81/1.03  --inst_restr_to_given                   false
% 3.81/1.03  --inst_activity_threshold               500
% 3.81/1.03  --inst_out_proof                        true
% 3.81/1.03  
% 3.81/1.03  ------ Resolution Options
% 3.81/1.03  
% 3.81/1.03  --resolution_flag                       true
% 3.81/1.03  --res_lit_sel                           adaptive
% 3.81/1.03  --res_lit_sel_side                      none
% 3.81/1.03  --res_ordering                          kbo
% 3.81/1.03  --res_to_prop_solver                    active
% 3.81/1.03  --res_prop_simpl_new                    false
% 3.81/1.03  --res_prop_simpl_given                  true
% 3.81/1.03  --res_passive_queue_type                priority_queues
% 3.81/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.03  --res_passive_queues_freq               [15;5]
% 3.81/1.03  --res_forward_subs                      full
% 3.81/1.03  --res_backward_subs                     full
% 3.81/1.03  --res_forward_subs_resolution           true
% 3.81/1.03  --res_backward_subs_resolution          true
% 3.81/1.03  --res_orphan_elimination                true
% 3.81/1.03  --res_time_limit                        2.
% 3.81/1.03  --res_out_proof                         true
% 3.81/1.03  
% 3.81/1.03  ------ Superposition Options
% 3.81/1.03  
% 3.81/1.03  --superposition_flag                    true
% 3.81/1.03  --sup_passive_queue_type                priority_queues
% 3.81/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.03  --demod_completeness_check              fast
% 3.81/1.03  --demod_use_ground                      true
% 3.81/1.03  --sup_to_prop_solver                    passive
% 3.81/1.03  --sup_prop_simpl_new                    true
% 3.81/1.03  --sup_prop_simpl_given                  true
% 3.81/1.03  --sup_fun_splitting                     false
% 3.81/1.03  --sup_smt_interval                      50000
% 3.81/1.03  
% 3.81/1.03  ------ Superposition Simplification Setup
% 3.81/1.03  
% 3.81/1.03  --sup_indices_passive                   []
% 3.81/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.03  --sup_full_bw                           [BwDemod]
% 3.81/1.03  --sup_immed_triv                        [TrivRules]
% 3.81/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.03  --sup_immed_bw_main                     []
% 3.81/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.03  
% 3.81/1.03  ------ Combination Options
% 3.81/1.03  
% 3.81/1.03  --comb_res_mult                         3
% 3.81/1.03  --comb_sup_mult                         2
% 3.81/1.03  --comb_inst_mult                        10
% 3.81/1.03  
% 3.81/1.03  ------ Debug Options
% 3.81/1.03  
% 3.81/1.03  --dbg_backtrace                         false
% 3.81/1.03  --dbg_dump_prop_clauses                 false
% 3.81/1.03  --dbg_dump_prop_clauses_file            -
% 3.81/1.03  --dbg_out_stat                          false
% 3.81/1.03  ------ Parsing...
% 3.81/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.03  
% 3.81/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.81/1.03  
% 3.81/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.03  
% 3.81/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.03  ------ Proving...
% 3.81/1.03  ------ Problem Properties 
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  clauses                                 36
% 3.81/1.03  conjectures                             10
% 3.81/1.03  EPR                                     12
% 3.81/1.03  Horn                                    26
% 3.81/1.03  unary                                   12
% 3.81/1.03  binary                                  10
% 3.81/1.03  lits                                    86
% 3.81/1.03  lits eq                                 17
% 3.81/1.03  fd_pure                                 0
% 3.81/1.03  fd_pseudo                               0
% 3.81/1.03  fd_cond                                 5
% 3.81/1.03  fd_pseudo_cond                          0
% 3.81/1.03  AC symbols                              0
% 3.81/1.03  
% 3.81/1.03  ------ Schedule dynamic 5 is on 
% 3.81/1.03  
% 3.81/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  ------ 
% 3.81/1.03  Current options:
% 3.81/1.03  ------ 
% 3.81/1.03  
% 3.81/1.03  ------ Input Options
% 3.81/1.03  
% 3.81/1.03  --out_options                           all
% 3.81/1.03  --tptp_safe_out                         true
% 3.81/1.03  --problem_path                          ""
% 3.81/1.03  --include_path                          ""
% 3.81/1.03  --clausifier                            res/vclausify_rel
% 3.81/1.03  --clausifier_options                    --mode clausify
% 3.81/1.03  --stdin                                 false
% 3.81/1.03  --stats_out                             all
% 3.81/1.03  
% 3.81/1.03  ------ General Options
% 3.81/1.03  
% 3.81/1.03  --fof                                   false
% 3.81/1.03  --time_out_real                         305.
% 3.81/1.03  --time_out_virtual                      -1.
% 3.81/1.03  --symbol_type_check                     false
% 3.81/1.03  --clausify_out                          false
% 3.81/1.03  --sig_cnt_out                           false
% 3.81/1.03  --trig_cnt_out                          false
% 3.81/1.03  --trig_cnt_out_tolerance                1.
% 3.81/1.03  --trig_cnt_out_sk_spl                   false
% 3.81/1.03  --abstr_cl_out                          false
% 3.81/1.03  
% 3.81/1.03  ------ Global Options
% 3.81/1.03  
% 3.81/1.03  --schedule                              default
% 3.81/1.03  --add_important_lit                     false
% 3.81/1.03  --prop_solver_per_cl                    1000
% 3.81/1.03  --min_unsat_core                        false
% 3.81/1.03  --soft_assumptions                      false
% 3.81/1.03  --soft_lemma_size                       3
% 3.81/1.03  --prop_impl_unit_size                   0
% 3.81/1.03  --prop_impl_unit                        []
% 3.81/1.03  --share_sel_clauses                     true
% 3.81/1.03  --reset_solvers                         false
% 3.81/1.03  --bc_imp_inh                            [conj_cone]
% 3.81/1.03  --conj_cone_tolerance                   3.
% 3.81/1.03  --extra_neg_conj                        none
% 3.81/1.03  --large_theory_mode                     true
% 3.81/1.03  --prolific_symb_bound                   200
% 3.81/1.03  --lt_threshold                          2000
% 3.81/1.03  --clause_weak_htbl                      true
% 3.81/1.03  --gc_record_bc_elim                     false
% 3.81/1.03  
% 3.81/1.03  ------ Preprocessing Options
% 3.81/1.03  
% 3.81/1.03  --preprocessing_flag                    true
% 3.81/1.03  --time_out_prep_mult                    0.1
% 3.81/1.03  --splitting_mode                        input
% 3.81/1.03  --splitting_grd                         true
% 3.81/1.03  --splitting_cvd                         false
% 3.81/1.03  --splitting_cvd_svl                     false
% 3.81/1.03  --splitting_nvd                         32
% 3.81/1.03  --sub_typing                            true
% 3.81/1.03  --prep_gs_sim                           true
% 3.81/1.03  --prep_unflatten                        true
% 3.81/1.03  --prep_res_sim                          true
% 3.81/1.03  --prep_upred                            true
% 3.81/1.03  --prep_sem_filter                       exhaustive
% 3.81/1.03  --prep_sem_filter_out                   false
% 3.81/1.03  --pred_elim                             true
% 3.81/1.03  --res_sim_input                         true
% 3.81/1.03  --eq_ax_congr_red                       true
% 3.81/1.03  --pure_diseq_elim                       true
% 3.81/1.03  --brand_transform                       false
% 3.81/1.03  --non_eq_to_eq                          false
% 3.81/1.03  --prep_def_merge                        true
% 3.81/1.03  --prep_def_merge_prop_impl              false
% 3.81/1.03  --prep_def_merge_mbd                    true
% 3.81/1.03  --prep_def_merge_tr_red                 false
% 3.81/1.03  --prep_def_merge_tr_cl                  false
% 3.81/1.03  --smt_preprocessing                     true
% 3.81/1.03  --smt_ac_axioms                         fast
% 3.81/1.03  --preprocessed_out                      false
% 3.81/1.03  --preprocessed_stats                    false
% 3.81/1.03  
% 3.81/1.03  ------ Abstraction refinement Options
% 3.81/1.03  
% 3.81/1.03  --abstr_ref                             []
% 3.81/1.03  --abstr_ref_prep                        false
% 3.81/1.03  --abstr_ref_until_sat                   false
% 3.81/1.03  --abstr_ref_sig_restrict                funpre
% 3.81/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.03  --abstr_ref_under                       []
% 3.81/1.03  
% 3.81/1.03  ------ SAT Options
% 3.81/1.03  
% 3.81/1.03  --sat_mode                              false
% 3.81/1.03  --sat_fm_restart_options                ""
% 3.81/1.03  --sat_gr_def                            false
% 3.81/1.03  --sat_epr_types                         true
% 3.81/1.03  --sat_non_cyclic_types                  false
% 3.81/1.03  --sat_finite_models                     false
% 3.81/1.03  --sat_fm_lemmas                         false
% 3.81/1.03  --sat_fm_prep                           false
% 3.81/1.03  --sat_fm_uc_incr                        true
% 3.81/1.03  --sat_out_model                         small
% 3.81/1.03  --sat_out_clauses                       false
% 3.81/1.03  
% 3.81/1.03  ------ QBF Options
% 3.81/1.03  
% 3.81/1.03  --qbf_mode                              false
% 3.81/1.03  --qbf_elim_univ                         false
% 3.81/1.03  --qbf_dom_inst                          none
% 3.81/1.03  --qbf_dom_pre_inst                      false
% 3.81/1.03  --qbf_sk_in                             false
% 3.81/1.03  --qbf_pred_elim                         true
% 3.81/1.03  --qbf_split                             512
% 3.81/1.03  
% 3.81/1.03  ------ BMC1 Options
% 3.81/1.03  
% 3.81/1.03  --bmc1_incremental                      false
% 3.81/1.03  --bmc1_axioms                           reachable_all
% 3.81/1.03  --bmc1_min_bound                        0
% 3.81/1.03  --bmc1_max_bound                        -1
% 3.81/1.03  --bmc1_max_bound_default                -1
% 3.81/1.03  --bmc1_symbol_reachability              true
% 3.81/1.03  --bmc1_property_lemmas                  false
% 3.81/1.03  --bmc1_k_induction                      false
% 3.81/1.03  --bmc1_non_equiv_states                 false
% 3.81/1.03  --bmc1_deadlock                         false
% 3.81/1.03  --bmc1_ucm                              false
% 3.81/1.03  --bmc1_add_unsat_core                   none
% 3.81/1.03  --bmc1_unsat_core_children              false
% 3.81/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.03  --bmc1_out_stat                         full
% 3.81/1.03  --bmc1_ground_init                      false
% 3.81/1.03  --bmc1_pre_inst_next_state              false
% 3.81/1.03  --bmc1_pre_inst_state                   false
% 3.81/1.03  --bmc1_pre_inst_reach_state             false
% 3.81/1.03  --bmc1_out_unsat_core                   false
% 3.81/1.03  --bmc1_aig_witness_out                  false
% 3.81/1.03  --bmc1_verbose                          false
% 3.81/1.03  --bmc1_dump_clauses_tptp                false
% 3.81/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.03  --bmc1_dump_file                        -
% 3.81/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.03  --bmc1_ucm_extend_mode                  1
% 3.81/1.03  --bmc1_ucm_init_mode                    2
% 3.81/1.03  --bmc1_ucm_cone_mode                    none
% 3.81/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.03  --bmc1_ucm_relax_model                  4
% 3.81/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.03  --bmc1_ucm_layered_model                none
% 3.81/1.03  --bmc1_ucm_max_lemma_size               10
% 3.81/1.03  
% 3.81/1.03  ------ AIG Options
% 3.81/1.03  
% 3.81/1.03  --aig_mode                              false
% 3.81/1.03  
% 3.81/1.03  ------ Instantiation Options
% 3.81/1.03  
% 3.81/1.03  --instantiation_flag                    true
% 3.81/1.03  --inst_sos_flag                         false
% 3.81/1.03  --inst_sos_phase                        true
% 3.81/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.03  --inst_lit_sel_side                     none
% 3.81/1.03  --inst_solver_per_active                1400
% 3.81/1.03  --inst_solver_calls_frac                1.
% 3.81/1.03  --inst_passive_queue_type               priority_queues
% 3.81/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.03  --inst_passive_queues_freq              [25;2]
% 3.81/1.03  --inst_dismatching                      true
% 3.81/1.03  --inst_eager_unprocessed_to_passive     true
% 3.81/1.03  --inst_prop_sim_given                   true
% 3.81/1.03  --inst_prop_sim_new                     false
% 3.81/1.03  --inst_subs_new                         false
% 3.81/1.03  --inst_eq_res_simp                      false
% 3.81/1.03  --inst_subs_given                       false
% 3.81/1.03  --inst_orphan_elimination               true
% 3.81/1.03  --inst_learning_loop_flag               true
% 3.81/1.03  --inst_learning_start                   3000
% 3.81/1.03  --inst_learning_factor                  2
% 3.81/1.03  --inst_start_prop_sim_after_learn       3
% 3.81/1.03  --inst_sel_renew                        solver
% 3.81/1.03  --inst_lit_activity_flag                true
% 3.81/1.03  --inst_restr_to_given                   false
% 3.81/1.03  --inst_activity_threshold               500
% 3.81/1.03  --inst_out_proof                        true
% 3.81/1.03  
% 3.81/1.03  ------ Resolution Options
% 3.81/1.03  
% 3.81/1.03  --resolution_flag                       false
% 3.81/1.03  --res_lit_sel                           adaptive
% 3.81/1.03  --res_lit_sel_side                      none
% 3.81/1.03  --res_ordering                          kbo
% 3.81/1.03  --res_to_prop_solver                    active
% 3.81/1.03  --res_prop_simpl_new                    false
% 3.81/1.03  --res_prop_simpl_given                  true
% 3.81/1.03  --res_passive_queue_type                priority_queues
% 3.81/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.03  --res_passive_queues_freq               [15;5]
% 3.81/1.03  --res_forward_subs                      full
% 3.81/1.03  --res_backward_subs                     full
% 3.81/1.03  --res_forward_subs_resolution           true
% 3.81/1.03  --res_backward_subs_resolution          true
% 3.81/1.03  --res_orphan_elimination                true
% 3.81/1.03  --res_time_limit                        2.
% 3.81/1.03  --res_out_proof                         true
% 3.81/1.03  
% 3.81/1.03  ------ Superposition Options
% 3.81/1.03  
% 3.81/1.03  --superposition_flag                    true
% 3.81/1.03  --sup_passive_queue_type                priority_queues
% 3.81/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.03  --demod_completeness_check              fast
% 3.81/1.03  --demod_use_ground                      true
% 3.81/1.03  --sup_to_prop_solver                    passive
% 3.81/1.03  --sup_prop_simpl_new                    true
% 3.81/1.03  --sup_prop_simpl_given                  true
% 3.81/1.03  --sup_fun_splitting                     false
% 3.81/1.03  --sup_smt_interval                      50000
% 3.81/1.03  
% 3.81/1.03  ------ Superposition Simplification Setup
% 3.81/1.03  
% 3.81/1.03  --sup_indices_passive                   []
% 3.81/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.03  --sup_full_bw                           [BwDemod]
% 3.81/1.03  --sup_immed_triv                        [TrivRules]
% 3.81/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.03  --sup_immed_bw_main                     []
% 3.81/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/1.03  
% 3.81/1.03  ------ Combination Options
% 3.81/1.03  
% 3.81/1.03  --comb_res_mult                         3
% 3.81/1.03  --comb_sup_mult                         2
% 3.81/1.03  --comb_inst_mult                        10
% 3.81/1.03  
% 3.81/1.03  ------ Debug Options
% 3.81/1.03  
% 3.81/1.03  --dbg_backtrace                         false
% 3.81/1.03  --dbg_dump_prop_clauses                 false
% 3.81/1.03  --dbg_dump_prop_clauses_file            -
% 3.81/1.03  --dbg_out_stat                          false
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  ------ Proving...
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  % SZS status Theorem for theBenchmark.p
% 3.81/1.03  
% 3.81/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.03  
% 3.81/1.03  fof(f20,conjecture,(
% 3.81/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f21,negated_conjecture,(
% 3.81/1.03    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.81/1.03    inference(negated_conjecture,[],[f20])).
% 3.81/1.03  
% 3.81/1.03  fof(f47,plain,(
% 3.81/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.81/1.03    inference(ennf_transformation,[],[f21])).
% 3.81/1.03  
% 3.81/1.03  fof(f48,plain,(
% 3.81/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.81/1.03    inference(flattening,[],[f47])).
% 3.81/1.03  
% 3.81/1.03  fof(f62,plain,(
% 3.81/1.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK8) != k7_partfun1(X0,X4,k1_funct_1(X3,sK8)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK8,X1))) )),
% 3.81/1.03    introduced(choice_axiom,[])).
% 3.81/1.03  
% 3.81/1.03  fof(f61,plain,(
% 3.81/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK7),X5) != k7_partfun1(X0,sK7,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK7)) & m1_subset_1(X5,X1)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK7))) )),
% 3.81/1.03    introduced(choice_axiom,[])).
% 3.81/1.03  
% 3.81/1.03  fof(f60,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK6,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK6,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK6),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK6,X1,X2) & v1_funct_1(sK6))) )),
% 3.81/1.03    introduced(choice_axiom,[])).
% 3.81/1.03  
% 3.81/1.03  fof(f59,plain,(
% 3.81/1.03    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK4,sK5,sK3,X3,X4),X5) != k7_partfun1(sK3,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,X3),k1_relset_1(sK5,sK3,X4)) & m1_subset_1(X5,sK4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) & ~v1_xboole_0(sK5))),
% 3.81/1.03    introduced(choice_axiom,[])).
% 3.81/1.03  
% 3.81/1.03  fof(f63,plain,(
% 3.81/1.03    (((k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) & k1_xboole_0 != sK4 & r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) & m1_subset_1(sK8,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)) & ~v1_xboole_0(sK5)),
% 3.81/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f48,f62,f61,f60,f59])).
% 3.81/1.03  
% 3.81/1.03  fof(f98,plain,(
% 3.81/1.03    m1_subset_1(sK8,sK4)),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f7,axiom,(
% 3.81/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f28,plain,(
% 3.81/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.81/1.03    inference(ennf_transformation,[],[f7])).
% 3.81/1.03  
% 3.81/1.03  fof(f29,plain,(
% 3.81/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.81/1.03    inference(flattening,[],[f28])).
% 3.81/1.03  
% 3.81/1.03  fof(f73,plain,(
% 3.81/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f29])).
% 3.81/1.03  
% 3.81/1.03  fof(f100,plain,(
% 3.81/1.03    k1_xboole_0 != sK4),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f3,axiom,(
% 3.81/1.03    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f25,plain,(
% 3.81/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.81/1.03    inference(ennf_transformation,[],[f3])).
% 3.81/1.03  
% 3.81/1.03  fof(f55,plain,(
% 3.81/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.81/1.03    introduced(choice_axiom,[])).
% 3.81/1.03  
% 3.81/1.03  fof(f56,plain,(
% 3.81/1.03    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.81/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f55])).
% 3.81/1.03  
% 3.81/1.03  fof(f69,plain,(
% 3.81/1.03    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.81/1.03    inference(cnf_transformation,[],[f56])).
% 3.81/1.03  
% 3.81/1.03  fof(f1,axiom,(
% 3.81/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f49,plain,(
% 3.81/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.81/1.03    inference(nnf_transformation,[],[f1])).
% 3.81/1.03  
% 3.81/1.03  fof(f50,plain,(
% 3.81/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.81/1.03    inference(rectify,[],[f49])).
% 3.81/1.03  
% 3.81/1.03  fof(f51,plain,(
% 3.81/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.81/1.03    introduced(choice_axiom,[])).
% 3.81/1.03  
% 3.81/1.03  fof(f52,plain,(
% 3.81/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.81/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.81/1.03  
% 3.81/1.03  fof(f64,plain,(
% 3.81/1.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f52])).
% 3.81/1.03  
% 3.81/1.03  fof(f95,plain,(
% 3.81/1.03    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f17,axiom,(
% 3.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f41,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.03    inference(ennf_transformation,[],[f17])).
% 3.81/1.03  
% 3.81/1.03  fof(f42,plain,(
% 3.81/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.03    inference(flattening,[],[f41])).
% 3.81/1.03  
% 3.81/1.03  fof(f58,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.03    inference(nnf_transformation,[],[f42])).
% 3.81/1.03  
% 3.81/1.03  fof(f84,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.03    inference(cnf_transformation,[],[f58])).
% 3.81/1.03  
% 3.81/1.03  fof(f14,axiom,(
% 3.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f37,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.03    inference(ennf_transformation,[],[f14])).
% 3.81/1.03  
% 3.81/1.03  fof(f81,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.03    inference(cnf_transformation,[],[f37])).
% 3.81/1.03  
% 3.81/1.03  fof(f92,plain,(
% 3.81/1.03    ~v1_xboole_0(sK5)),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f94,plain,(
% 3.81/1.03    v1_funct_2(sK6,sK4,sK5)),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f65,plain,(
% 3.81/1.03    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f52])).
% 3.81/1.03  
% 3.81/1.03  fof(f4,axiom,(
% 3.81/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f70,plain,(
% 3.81/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f4])).
% 3.81/1.03  
% 3.81/1.03  fof(f11,axiom,(
% 3.81/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f34,plain,(
% 3.81/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.81/1.03    inference(ennf_transformation,[],[f11])).
% 3.81/1.03  
% 3.81/1.03  fof(f78,plain,(
% 3.81/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f34])).
% 3.81/1.03  
% 3.81/1.03  fof(f16,axiom,(
% 3.81/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f39,plain,(
% 3.81/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.81/1.03    inference(ennf_transformation,[],[f16])).
% 3.81/1.03  
% 3.81/1.03  fof(f40,plain,(
% 3.81/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.81/1.03    inference(flattening,[],[f39])).
% 3.81/1.03  
% 3.81/1.03  fof(f83,plain,(
% 3.81/1.03    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.81/1.03    inference(cnf_transformation,[],[f40])).
% 3.81/1.03  
% 3.81/1.03  fof(f13,axiom,(
% 3.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f23,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.81/1.03    inference(pure_predicate_removal,[],[f13])).
% 3.81/1.03  
% 3.81/1.03  fof(f36,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.03    inference(ennf_transformation,[],[f23])).
% 3.81/1.03  
% 3.81/1.03  fof(f80,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.03    inference(cnf_transformation,[],[f36])).
% 3.81/1.03  
% 3.81/1.03  fof(f10,axiom,(
% 3.81/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f32,plain,(
% 3.81/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.81/1.03    inference(ennf_transformation,[],[f10])).
% 3.81/1.03  
% 3.81/1.03  fof(f33,plain,(
% 3.81/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.81/1.03    inference(flattening,[],[f32])).
% 3.81/1.03  
% 3.81/1.03  fof(f77,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f33])).
% 3.81/1.03  
% 3.81/1.03  fof(f12,axiom,(
% 3.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f35,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.03    inference(ennf_transformation,[],[f12])).
% 3.81/1.03  
% 3.81/1.03  fof(f79,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.03    inference(cnf_transformation,[],[f35])).
% 3.81/1.03  
% 3.81/1.03  fof(f93,plain,(
% 3.81/1.03    v1_funct_1(sK6)),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f97,plain,(
% 3.81/1.03    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f18,axiom,(
% 3.81/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f43,plain,(
% 3.81/1.03    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.81/1.03    inference(ennf_transformation,[],[f18])).
% 3.81/1.03  
% 3.81/1.03  fof(f44,plain,(
% 3.81/1.03    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.81/1.03    inference(flattening,[],[f43])).
% 3.81/1.03  
% 3.81/1.03  fof(f90,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f44])).
% 3.81/1.03  
% 3.81/1.03  fof(f96,plain,(
% 3.81/1.03    v1_funct_1(sK7)),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f15,axiom,(
% 3.81/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f38,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/1.03    inference(ennf_transformation,[],[f15])).
% 3.81/1.03  
% 3.81/1.03  fof(f82,plain,(
% 3.81/1.03    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/1.03    inference(cnf_transformation,[],[f38])).
% 3.81/1.03  
% 3.81/1.03  fof(f99,plain,(
% 3.81/1.03    r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7))),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  fof(f19,axiom,(
% 3.81/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.81/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.03  
% 3.81/1.03  fof(f45,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.81/1.03    inference(ennf_transformation,[],[f19])).
% 3.81/1.03  
% 3.81/1.03  fof(f46,plain,(
% 3.81/1.03    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.81/1.03    inference(flattening,[],[f45])).
% 3.81/1.03  
% 3.81/1.03  fof(f91,plain,(
% 3.81/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.81/1.03    inference(cnf_transformation,[],[f46])).
% 3.81/1.03  
% 3.81/1.03  fof(f101,plain,(
% 3.81/1.03    k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8))),
% 3.81/1.03    inference(cnf_transformation,[],[f63])).
% 3.81/1.03  
% 3.81/1.03  cnf(c_31,negated_conjecture,
% 3.81/1.03      ( m1_subset_1(sK8,sK4) ),
% 3.81/1.03      inference(cnf_transformation,[],[f98]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2964,plain,
% 3.81/1.03      ( m1_subset_1(sK8,sK4) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_9,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.81/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2980,plain,
% 3.81/1.03      ( m1_subset_1(X0,X1) != iProver_top
% 3.81/1.03      | r2_hidden(X0,X1) = iProver_top
% 3.81/1.03      | v1_xboole_0(X1) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4915,plain,
% 3.81/1.03      ( r2_hidden(sK8,sK4) = iProver_top
% 3.81/1.03      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2964,c_2980]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_44,plain,
% 3.81/1.03      ( m1_subset_1(sK8,sK4) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_29,negated_conjecture,
% 3.81/1.03      ( k1_xboole_0 != sK4 ),
% 3.81/1.03      inference(cnf_transformation,[],[f100]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5,plain,
% 3.81/1.03      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.81/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3241,plain,
% 3.81/1.03      ( r2_hidden(sK2(sK4),sK4) | k1_xboole_0 = sK4 ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_5]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3242,plain,
% 3.81/1.03      ( k1_xboole_0 = sK4 | r2_hidden(sK2(sK4),sK4) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_3241]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_1,plain,
% 3.81/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.81/1.03      inference(cnf_transformation,[],[f64]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3416,plain,
% 3.81/1.03      ( ~ r2_hidden(sK2(sK4),sK4) | ~ v1_xboole_0(sK4) ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_1]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3417,plain,
% 3.81/1.03      ( r2_hidden(sK2(sK4),sK4) != iProver_top
% 3.81/1.03      | v1_xboole_0(sK4) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_3416]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3612,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,sK4) | r2_hidden(X0,sK4) | v1_xboole_0(sK4) ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4887,plain,
% 3.81/1.03      ( ~ m1_subset_1(sK8,sK4) | r2_hidden(sK8,sK4) | v1_xboole_0(sK4) ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_3612]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4888,plain,
% 3.81/1.03      ( m1_subset_1(sK8,sK4) != iProver_top
% 3.81/1.03      | r2_hidden(sK8,sK4) = iProver_top
% 3.81/1.03      | v1_xboole_0(sK4) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_4887]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5208,plain,
% 3.81/1.03      ( r2_hidden(sK8,sK4) = iProver_top ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_4915,c_44,c_29,c_3242,c_3417,c_4888]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_34,negated_conjecture,
% 3.81/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.81/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2961,plain,
% 3.81/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_25,plain,
% 3.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.81/1.03      | k1_xboole_0 = X2 ),
% 3.81/1.03      inference(cnf_transformation,[],[f84]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2967,plain,
% 3.81/1.03      ( k1_relset_1(X0,X1,X2) = X0
% 3.81/1.03      | k1_xboole_0 = X1
% 3.81/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.81/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5460,plain,
% 3.81/1.03      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 3.81/1.03      | sK5 = k1_xboole_0
% 3.81/1.03      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2961,c_2967]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_17,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.81/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2975,plain,
% 3.81/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.81/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4838,plain,
% 3.81/1.03      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2961,c_2975]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5464,plain,
% 3.81/1.03      ( k1_relat_1(sK6) = sK4
% 3.81/1.03      | sK5 = k1_xboole_0
% 3.81/1.03      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 3.81/1.03      inference(demodulation,[status(thm)],[c_5460,c_4838]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_37,negated_conjecture,
% 3.81/1.03      ( ~ v1_xboole_0(sK5) ),
% 3.81/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_38,plain,
% 3.81/1.03      ( v1_xboole_0(sK5) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_35,negated_conjecture,
% 3.81/1.03      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.81/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_40,plain,
% 3.81/1.03      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2157,plain,
% 3.81/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.81/1.03      theory(equality) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3251,plain,
% 3.81/1.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_2157]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3252,plain,
% 3.81/1.03      ( sK5 != X0
% 3.81/1.03      | v1_xboole_0(X0) != iProver_top
% 3.81/1.03      | v1_xboole_0(sK5) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_3251]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3254,plain,
% 3.81/1.03      ( sK5 != k1_xboole_0
% 3.81/1.03      | v1_xboole_0(sK5) = iProver_top
% 3.81/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_3252]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_0,plain,
% 3.81/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.81/1.03      inference(cnf_transformation,[],[f65]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2989,plain,
% 3.81/1.03      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.81/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_6,plain,
% 3.81/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.81/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2983,plain,
% 3.81/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_14,plain,
% 3.81/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.81/1.03      inference(cnf_transformation,[],[f78]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2976,plain,
% 3.81/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.81/1.03      | r2_hidden(X1,X0) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3866,plain,
% 3.81/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2983,c_2976]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_6358,plain,
% 3.81/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2989,c_3866]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_8793,plain,
% 3.81/1.03      ( k1_relat_1(sK6) = sK4 ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_5464,c_38,c_40,c_3254,c_6358]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_19,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.81/1.03      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.81/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2973,plain,
% 3.81/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.81/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.81/1.03      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_6332,plain,
% 3.81/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) = iProver_top
% 3.81/1.03      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2961,c_2973]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_16,plain,
% 3.81/1.03      ( v5_relat_1(X0,X1)
% 3.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.81/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_13,plain,
% 3.81/1.03      ( ~ v5_relat_1(X0,X1)
% 3.81/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.81/1.03      | r2_hidden(k1_funct_1(X0,X2),X1)
% 3.81/1.03      | ~ v1_relat_1(X0)
% 3.81/1.03      | ~ v1_funct_1(X0) ),
% 3.81/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_505,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.81/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.81/1.03      | ~ v1_relat_1(X0)
% 3.81/1.03      | ~ v1_funct_1(X0) ),
% 3.81/1.03      inference(resolution,[status(thm)],[c_16,c_13]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_15,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | v1_relat_1(X0) ),
% 3.81/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_509,plain,
% 3.81/1.03      ( r2_hidden(k1_funct_1(X0,X3),X2)
% 3.81/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | ~ v1_funct_1(X0) ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_505,c_15]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_510,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.81/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.81/1.03      | ~ v1_funct_1(X0) ),
% 3.81/1.03      inference(renaming,[status(thm)],[c_509]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2956,plain,
% 3.81/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.81/1.03      | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
% 3.81/1.03      | r2_hidden(k1_funct_1(X0,X3),X2) = iProver_top
% 3.81/1.03      | v1_funct_1(X0) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_6637,plain,
% 3.81/1.03      ( r1_tarski(k2_relat_1(sK6),X0) != iProver_top
% 3.81/1.03      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 3.81/1.03      | r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top
% 3.81/1.03      | v1_funct_1(sK6) != iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_6332,c_2956]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_36,negated_conjecture,
% 3.81/1.03      ( v1_funct_1(sK6) ),
% 3.81/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_39,plain,
% 3.81/1.03      ( v1_funct_1(sK6) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_7645,plain,
% 3.81/1.03      ( r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top
% 3.81/1.03      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 3.81/1.03      | r1_tarski(k2_relat_1(sK6),X0) != iProver_top ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_6637,c_39]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_7646,plain,
% 3.81/1.03      ( r1_tarski(k2_relat_1(sK6),X0) != iProver_top
% 3.81/1.03      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 3.81/1.03      | r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top ),
% 3.81/1.03      inference(renaming,[status(thm)],[c_7645]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_32,negated_conjecture,
% 3.81/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.81/1.03      inference(cnf_transformation,[],[f97]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2963,plain,
% 3.81/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_26,plain,
% 3.81/1.03      ( ~ v5_relat_1(X0,X1)
% 3.81/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.81/1.03      | ~ v1_relat_1(X0)
% 3.81/1.03      | ~ v1_funct_1(X0)
% 3.81/1.03      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.81/1.03      inference(cnf_transformation,[],[f90]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_482,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.81/1.03      | ~ v1_relat_1(X0)
% 3.81/1.03      | ~ v1_funct_1(X0)
% 3.81/1.03      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.81/1.03      inference(resolution,[status(thm)],[c_16,c_26]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_486,plain,
% 3.81/1.03      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 3.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | ~ v1_funct_1(X0)
% 3.81/1.03      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_482,c_15]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_487,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.81/1.03      | ~ v1_funct_1(X0)
% 3.81/1.03      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.81/1.03      inference(renaming,[status(thm)],[c_486]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2957,plain,
% 3.81/1.03      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.81/1.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.81/1.03      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.81/1.03      | v1_funct_1(X1) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3880,plain,
% 3.81/1.03      ( k7_partfun1(sK3,sK7,X0) = k1_funct_1(sK7,X0)
% 3.81/1.03      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.81/1.03      | v1_funct_1(sK7) != iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2963,c_2957]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_33,negated_conjecture,
% 3.81/1.03      ( v1_funct_1(sK7) ),
% 3.81/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_42,plain,
% 3.81/1.03      ( v1_funct_1(sK7) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4315,plain,
% 3.81/1.03      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.81/1.03      | k7_partfun1(sK3,sK7,X0) = k1_funct_1(sK7,X0) ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_3880,c_42]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4316,plain,
% 3.81/1.03      ( k7_partfun1(sK3,sK7,X0) = k1_funct_1(sK7,X0)
% 3.81/1.03      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.81/1.03      inference(renaming,[status(thm)],[c_4315]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_7657,plain,
% 3.81/1.03      ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,X0)) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
% 3.81/1.03      | r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) != iProver_top
% 3.81/1.03      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_7646,c_4316]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_18,plain,
% 3.81/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.81/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2974,plain,
% 3.81/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.81/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4819,plain,
% 3.81/1.03      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2961,c_2974]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_30,negated_conjecture,
% 3.81/1.03      ( r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) ),
% 3.81/1.03      inference(cnf_transformation,[],[f99]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2965,plain,
% 3.81/1.03      ( r1_tarski(k2_relset_1(sK4,sK5,sK6),k1_relset_1(sK5,sK3,sK7)) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5016,plain,
% 3.81/1.03      ( r1_tarski(k2_relat_1(sK6),k1_relset_1(sK5,sK3,sK7)) = iProver_top ),
% 3.81/1.03      inference(demodulation,[status(thm)],[c_4819,c_2965]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4837,plain,
% 3.81/1.03      ( k1_relset_1(sK5,sK3,sK7) = k1_relat_1(sK7) ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2963,c_2975]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5108,plain,
% 3.81/1.03      ( r1_tarski(k2_relat_1(sK6),k1_relat_1(sK7)) = iProver_top ),
% 3.81/1.03      inference(light_normalisation,[status(thm)],[c_5016,c_4837]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_8515,plain,
% 3.81/1.03      ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,X0)) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
% 3.81/1.03      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_7657,c_5108]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_8797,plain,
% 3.81/1.03      ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,X0)) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
% 3.81/1.03      | r2_hidden(X0,sK4) != iProver_top ),
% 3.81/1.03      inference(demodulation,[status(thm)],[c_8793,c_8515]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_12369,plain,
% 3.81/1.03      ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) = k1_funct_1(sK7,k1_funct_1(sK6,sK8)) ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_5208,c_8797]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_27,plain,
% 3.81/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.81/1.03      | ~ m1_subset_1(X3,X1)
% 3.81/1.03      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.81/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/1.03      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.81/1.03      | ~ v1_funct_1(X4)
% 3.81/1.03      | ~ v1_funct_1(X0)
% 3.81/1.03      | v1_xboole_0(X2)
% 3.81/1.03      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.81/1.03      | k1_xboole_0 = X1 ),
% 3.81/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2966,plain,
% 3.81/1.03      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.81/1.03      | k1_xboole_0 = X0
% 3.81/1.03      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.81/1.03      | m1_subset_1(X5,X0) != iProver_top
% 3.81/1.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.81/1.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.81/1.03      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.81/1.03      | v1_funct_1(X4) != iProver_top
% 3.81/1.03      | v1_funct_1(X3) != iProver_top
% 3.81/1.03      | v1_xboole_0(X1) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_4667,plain,
% 3.81/1.03      ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
% 3.81/1.03      | sK4 = k1_xboole_0
% 3.81/1.03      | v1_funct_2(sK6,sK4,sK5) != iProver_top
% 3.81/1.03      | m1_subset_1(X0,sK4) != iProver_top
% 3.81/1.03      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.81/1.03      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.81/1.03      | v1_funct_1(sK7) != iProver_top
% 3.81/1.03      | v1_funct_1(sK6) != iProver_top
% 3.81/1.03      | v1_xboole_0(sK5) = iProver_top ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2965,c_2966]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_41,plain,
% 3.81/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_43,plain,
% 3.81/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.81/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2155,plain,( X0 = X0 ),theory(equality) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2184,plain,
% 3.81/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_2155]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_2156,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3292,plain,
% 3.81/1.03      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_2156]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_3293,plain,
% 3.81/1.03      ( sK4 != k1_xboole_0
% 3.81/1.03      | k1_xboole_0 = sK4
% 3.81/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.81/1.03      inference(instantiation,[status(thm)],[c_3292]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5989,plain,
% 3.81/1.03      ( m1_subset_1(X0,sK4) != iProver_top
% 3.81/1.03      | k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK6,X0)) ),
% 3.81/1.03      inference(global_propositional_subsumption,
% 3.81/1.03                [status(thm)],
% 3.81/1.03                [c_4667,c_38,c_39,c_40,c_41,c_42,c_43,c_29,c_2184,c_3293]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5990,plain,
% 3.81/1.03      ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),X0) = k1_funct_1(sK7,k1_funct_1(sK6,X0))
% 3.81/1.03      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.81/1.03      inference(renaming,[status(thm)],[c_5989]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5997,plain,
% 3.81/1.03      ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) = k1_funct_1(sK7,k1_funct_1(sK6,sK8)) ),
% 3.81/1.03      inference(superposition,[status(thm)],[c_2964,c_5990]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_28,negated_conjecture,
% 3.81/1.03      ( k1_funct_1(k8_funct_2(sK4,sK5,sK3,sK6,sK7),sK8) != k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) ),
% 3.81/1.03      inference(cnf_transformation,[],[f101]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(c_5999,plain,
% 3.81/1.03      ( k7_partfun1(sK3,sK7,k1_funct_1(sK6,sK8)) != k1_funct_1(sK7,k1_funct_1(sK6,sK8)) ),
% 3.81/1.03      inference(demodulation,[status(thm)],[c_5997,c_28]) ).
% 3.81/1.03  
% 3.81/1.03  cnf(contradiction,plain,
% 3.81/1.03      ( $false ),
% 3.81/1.03      inference(minisat,[status(thm)],[c_12369,c_5999]) ).
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.03  
% 3.81/1.03  ------                               Statistics
% 3.81/1.03  
% 3.81/1.03  ------ General
% 3.81/1.03  
% 3.81/1.03  abstr_ref_over_cycles:                  0
% 3.81/1.03  abstr_ref_under_cycles:                 0
% 3.81/1.03  gc_basic_clause_elim:                   0
% 3.81/1.03  forced_gc_time:                         0
% 3.81/1.03  parsing_time:                           0.014
% 3.81/1.03  unif_index_cands_time:                  0.
% 3.81/1.03  unif_index_add_time:                    0.
% 3.81/1.03  orderings_time:                         0.
% 3.81/1.03  out_proof_time:                         0.012
% 3.81/1.03  total_time:                             0.391
% 3.81/1.03  num_of_symbols:                         59
% 3.81/1.03  num_of_terms:                           11088
% 3.81/1.03  
% 3.81/1.03  ------ Preprocessing
% 3.81/1.03  
% 3.81/1.03  num_of_splits:                          0
% 3.81/1.03  num_of_split_atoms:                     0
% 3.81/1.03  num_of_reused_defs:                     0
% 3.81/1.03  num_eq_ax_congr_red:                    27
% 3.81/1.03  num_of_sem_filtered_clauses:            1
% 3.81/1.03  num_of_subtypes:                        0
% 3.81/1.03  monotx_restored_types:                  0
% 3.81/1.03  sat_num_of_epr_types:                   0
% 3.81/1.03  sat_num_of_non_cyclic_types:            0
% 3.81/1.03  sat_guarded_non_collapsed_types:        0
% 3.81/1.03  num_pure_diseq_elim:                    0
% 3.81/1.03  simp_replaced_by:                       0
% 3.81/1.03  res_preprocessed:                       177
% 3.81/1.03  prep_upred:                             0
% 3.81/1.03  prep_unflattend:                        124
% 3.81/1.03  smt_new_axioms:                         0
% 3.81/1.03  pred_elim_cands:                        7
% 3.81/1.03  pred_elim:                              2
% 3.81/1.03  pred_elim_cl:                           2
% 3.81/1.03  pred_elim_cycles:                       10
% 3.81/1.03  merged_defs:                            8
% 3.81/1.03  merged_defs_ncl:                        0
% 3.81/1.03  bin_hyper_res:                          8
% 3.81/1.03  prep_cycles:                            4
% 3.81/1.03  pred_elim_time:                         0.05
% 3.81/1.03  splitting_time:                         0.
% 3.81/1.03  sem_filter_time:                        0.
% 3.81/1.03  monotx_time:                            0.001
% 3.81/1.03  subtype_inf_time:                       0.
% 3.81/1.03  
% 3.81/1.03  ------ Problem properties
% 3.81/1.03  
% 3.81/1.03  clauses:                                36
% 3.81/1.03  conjectures:                            10
% 3.81/1.03  epr:                                    12
% 3.81/1.03  horn:                                   26
% 3.81/1.03  ground:                                 10
% 3.81/1.03  unary:                                  12
% 3.81/1.03  binary:                                 10
% 3.81/1.03  lits:                                   86
% 3.81/1.03  lits_eq:                                17
% 3.81/1.03  fd_pure:                                0
% 3.81/1.03  fd_pseudo:                              0
% 3.81/1.03  fd_cond:                                5
% 3.81/1.03  fd_pseudo_cond:                         0
% 3.81/1.03  ac_symbols:                             0
% 3.81/1.03  
% 3.81/1.03  ------ Propositional Solver
% 3.81/1.03  
% 3.81/1.03  prop_solver_calls:                      29
% 3.81/1.03  prop_fast_solver_calls:                 1711
% 3.81/1.03  smt_solver_calls:                       0
% 3.81/1.03  smt_fast_solver_calls:                  0
% 3.81/1.03  prop_num_of_clauses:                    3871
% 3.81/1.03  prop_preprocess_simplified:             9795
% 3.81/1.03  prop_fo_subsumed:                       60
% 3.81/1.03  prop_solver_time:                       0.
% 3.81/1.03  smt_solver_time:                        0.
% 3.81/1.03  smt_fast_solver_time:                   0.
% 3.81/1.03  prop_fast_solver_time:                  0.
% 3.81/1.03  prop_unsat_core_time:                   0.
% 3.81/1.03  
% 3.81/1.03  ------ QBF
% 3.81/1.03  
% 3.81/1.03  qbf_q_res:                              0
% 3.81/1.03  qbf_num_tautologies:                    0
% 3.81/1.03  qbf_prep_cycles:                        0
% 3.81/1.03  
% 3.81/1.03  ------ BMC1
% 3.81/1.03  
% 3.81/1.03  bmc1_current_bound:                     -1
% 3.81/1.03  bmc1_last_solved_bound:                 -1
% 3.81/1.03  bmc1_unsat_core_size:                   -1
% 3.81/1.03  bmc1_unsat_core_parents_size:           -1
% 3.81/1.03  bmc1_merge_next_fun:                    0
% 3.81/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.81/1.03  
% 3.81/1.03  ------ Instantiation
% 3.81/1.03  
% 3.81/1.03  inst_num_of_clauses:                    1215
% 3.81/1.03  inst_num_in_passive:                    262
% 3.81/1.03  inst_num_in_active:                     613
% 3.81/1.03  inst_num_in_unprocessed:                343
% 3.81/1.03  inst_num_of_loops:                      740
% 3.81/1.03  inst_num_of_learning_restarts:          0
% 3.81/1.03  inst_num_moves_active_passive:          123
% 3.81/1.03  inst_lit_activity:                      0
% 3.81/1.03  inst_lit_activity_moves:                0
% 3.81/1.03  inst_num_tautologies:                   0
% 3.81/1.03  inst_num_prop_implied:                  0
% 3.81/1.03  inst_num_existing_simplified:           0
% 3.81/1.03  inst_num_eq_res_simplified:             0
% 3.81/1.03  inst_num_child_elim:                    0
% 3.81/1.03  inst_num_of_dismatching_blockings:      663
% 3.81/1.03  inst_num_of_non_proper_insts:           1244
% 3.81/1.03  inst_num_of_duplicates:                 0
% 3.81/1.03  inst_inst_num_from_inst_to_res:         0
% 3.81/1.03  inst_dismatching_checking_time:         0.
% 3.81/1.03  
% 3.81/1.03  ------ Resolution
% 3.81/1.03  
% 3.81/1.03  res_num_of_clauses:                     0
% 3.81/1.03  res_num_in_passive:                     0
% 3.81/1.03  res_num_in_active:                      0
% 3.81/1.03  res_num_of_loops:                       181
% 3.81/1.03  res_forward_subset_subsumed:            141
% 3.81/1.03  res_backward_subset_subsumed:           12
% 3.81/1.03  res_forward_subsumed:                   0
% 3.81/1.03  res_backward_subsumed:                  0
% 3.81/1.03  res_forward_subsumption_resolution:     1
% 3.81/1.03  res_backward_subsumption_resolution:    0
% 3.81/1.03  res_clause_to_clause_subsumption:       621
% 3.81/1.03  res_orphan_elimination:                 0
% 3.81/1.03  res_tautology_del:                      156
% 3.81/1.03  res_num_eq_res_simplified:              0
% 3.81/1.03  res_num_sel_changes:                    0
% 3.81/1.03  res_moves_from_active_to_pass:          0
% 3.81/1.03  
% 3.81/1.03  ------ Superposition
% 3.81/1.03  
% 3.81/1.03  sup_time_total:                         0.
% 3.81/1.03  sup_time_generating:                    0.
% 3.81/1.03  sup_time_sim_full:                      0.
% 3.81/1.03  sup_time_sim_immed:                     0.
% 3.81/1.03  
% 3.81/1.03  sup_num_of_clauses:                     213
% 3.81/1.03  sup_num_in_active:                      134
% 3.81/1.03  sup_num_in_passive:                     79
% 3.81/1.03  sup_num_of_loops:                       146
% 3.81/1.03  sup_fw_superposition:                   142
% 3.81/1.03  sup_bw_superposition:                   99
% 3.81/1.03  sup_immediate_simplified:               24
% 3.81/1.03  sup_given_eliminated:                   1
% 3.81/1.03  comparisons_done:                       0
% 3.81/1.03  comparisons_avoided:                    8
% 3.81/1.03  
% 3.81/1.03  ------ Simplifications
% 3.81/1.03  
% 3.81/1.03  
% 3.81/1.03  sim_fw_subset_subsumed:                 16
% 3.81/1.03  sim_bw_subset_subsumed:                 1
% 3.81/1.03  sim_fw_subsumed:                        5
% 3.81/1.03  sim_bw_subsumed:                        3
% 3.81/1.03  sim_fw_subsumption_res:                 1
% 3.81/1.03  sim_bw_subsumption_res:                 0
% 3.81/1.03  sim_tautology_del:                      8
% 3.81/1.03  sim_eq_tautology_del:                   2
% 3.81/1.03  sim_eq_res_simp:                        0
% 3.81/1.03  sim_fw_demodulated:                     6
% 3.81/1.03  sim_bw_demodulated:                     12
% 3.81/1.03  sim_light_normalised:                   9
% 3.81/1.03  sim_joinable_taut:                      0
% 3.81/1.03  sim_joinable_simp:                      0
% 3.81/1.03  sim_ac_normalised:                      0
% 3.81/1.03  sim_smt_subsumption:                    0
% 3.81/1.03  
%------------------------------------------------------------------------------
