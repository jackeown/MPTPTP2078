%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:55 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 371 expanded)
%              Number of clauses        :   81 (  98 expanded)
%              Number of leaves         :   21 ( 127 expanded)
%              Depth                    :   19
%              Number of atoms          :  522 (2833 expanded)
%              Number of equality atoms :  150 ( 702 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
                   => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
                     => ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK7,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
              & k1_xboole_0 != X1
              & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                ( k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
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
                  ( k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5)
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

fof(f45,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)
    & k1_xboole_0 != sK3
    & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f44,f43,f42,f41])).

fof(f68,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1700,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1706,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3034,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1706])).

cnf(c_32,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1902,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1903,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1902])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1960,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1961,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1960])).

cnf(c_3202,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3034,c_32,c_17,c_1903,c_1961])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_293,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_294,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_298,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
    | ~ r2_hidden(X0,sK3)
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_24,c_22])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
    | k1_xboole_0 = sK4 ),
    inference(renaming,[status(thm)],[c_298])).

cnf(c_1696,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1699,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1702,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2435,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1699,c_1702])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1701,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2729,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2435,c_1701])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1709,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3057,plain,
    ( r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2729,c_1709])).

cnf(c_3455,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1696,c_3057])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1888,plain,
    ( ~ r1_tarski(X0,sK0(X0))
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2063,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1888])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2064,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2718,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1277,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3125,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_3130,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3125])).

cnf(c_3710,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3455,c_25,c_2063,c_2064,c_2718,c_3130])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_11,c_13])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_267,c_21])).

cnf(c_452,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k7_partfun1(X1,sK6,X2) = k1_funct_1(sK6,X2) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_1694,plain,
    ( k7_partfun1(X0,sK6,X1) = k1_funct_1(sK6,X1)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_2199,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1699,c_1694])).

cnf(c_3719,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3710,c_2199])).

cnf(c_31,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1883,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2209,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_2210,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2233,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2234,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_3737,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3719,c_31,c_2210,c_2234])).

cnf(c_3738,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3737])).

cnf(c_3747,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_3202,c_3738])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X3)
    | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
    | sK4 != X3
    | sK3 != X1
    | sK5 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK4)
    | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_319,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
    | ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_25,c_24,c_22,c_17])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2)) ),
    inference(renaming,[status(thm)],[c_319])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ m1_subset_1(X2,sK3)
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
    | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_320,c_21])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
    | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,sK6))
    | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_1695,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,sK6),X1) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_2256,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_1695])).

cnf(c_2261,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_31])).

cnf(c_2262,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_2261])).

cnf(c_2269,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_1700,c_2262])).

cnf(c_16,negated_conjecture,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2380,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_2269,c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3747,c_2380])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.38/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.01  
% 2.38/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.38/1.01  
% 2.38/1.01  ------  iProver source info
% 2.38/1.01  
% 2.38/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.38/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.38/1.01  git: non_committed_changes: false
% 2.38/1.01  git: last_make_outside_of_git: false
% 2.38/1.01  
% 2.38/1.01  ------ 
% 2.38/1.01  
% 2.38/1.01  ------ Input Options
% 2.38/1.01  
% 2.38/1.01  --out_options                           all
% 2.38/1.01  --tptp_safe_out                         true
% 2.38/1.01  --problem_path                          ""
% 2.38/1.01  --include_path                          ""
% 2.38/1.01  --clausifier                            res/vclausify_rel
% 2.38/1.01  --clausifier_options                    --mode clausify
% 2.38/1.01  --stdin                                 false
% 2.38/1.01  --stats_out                             all
% 2.38/1.01  
% 2.38/1.01  ------ General Options
% 2.38/1.01  
% 2.38/1.01  --fof                                   false
% 2.38/1.01  --time_out_real                         305.
% 2.38/1.01  --time_out_virtual                      -1.
% 2.38/1.01  --symbol_type_check                     false
% 2.38/1.01  --clausify_out                          false
% 2.38/1.01  --sig_cnt_out                           false
% 2.38/1.01  --trig_cnt_out                          false
% 2.38/1.01  --trig_cnt_out_tolerance                1.
% 2.38/1.01  --trig_cnt_out_sk_spl                   false
% 2.38/1.01  --abstr_cl_out                          false
% 2.38/1.01  
% 2.38/1.01  ------ Global Options
% 2.38/1.01  
% 2.38/1.01  --schedule                              default
% 2.38/1.01  --add_important_lit                     false
% 2.38/1.01  --prop_solver_per_cl                    1000
% 2.38/1.01  --min_unsat_core                        false
% 2.38/1.01  --soft_assumptions                      false
% 2.38/1.01  --soft_lemma_size                       3
% 2.38/1.01  --prop_impl_unit_size                   0
% 2.38/1.01  --prop_impl_unit                        []
% 2.38/1.01  --share_sel_clauses                     true
% 2.38/1.01  --reset_solvers                         false
% 2.38/1.01  --bc_imp_inh                            [conj_cone]
% 2.38/1.01  --conj_cone_tolerance                   3.
% 2.38/1.01  --extra_neg_conj                        none
% 2.38/1.01  --large_theory_mode                     true
% 2.38/1.01  --prolific_symb_bound                   200
% 2.38/1.01  --lt_threshold                          2000
% 2.38/1.01  --clause_weak_htbl                      true
% 2.38/1.01  --gc_record_bc_elim                     false
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing Options
% 2.38/1.01  
% 2.38/1.01  --preprocessing_flag                    true
% 2.38/1.01  --time_out_prep_mult                    0.1
% 2.38/1.01  --splitting_mode                        input
% 2.38/1.01  --splitting_grd                         true
% 2.38/1.01  --splitting_cvd                         false
% 2.38/1.01  --splitting_cvd_svl                     false
% 2.38/1.01  --splitting_nvd                         32
% 2.38/1.01  --sub_typing                            true
% 2.38/1.01  --prep_gs_sim                           true
% 2.38/1.01  --prep_unflatten                        true
% 2.38/1.01  --prep_res_sim                          true
% 2.38/1.01  --prep_upred                            true
% 2.38/1.01  --prep_sem_filter                       exhaustive
% 2.38/1.01  --prep_sem_filter_out                   false
% 2.38/1.01  --pred_elim                             true
% 2.38/1.01  --res_sim_input                         true
% 2.38/1.01  --eq_ax_congr_red                       true
% 2.38/1.01  --pure_diseq_elim                       true
% 2.38/1.01  --brand_transform                       false
% 2.38/1.01  --non_eq_to_eq                          false
% 2.38/1.01  --prep_def_merge                        true
% 2.38/1.01  --prep_def_merge_prop_impl              false
% 2.38/1.01  --prep_def_merge_mbd                    true
% 2.38/1.01  --prep_def_merge_tr_red                 false
% 2.38/1.01  --prep_def_merge_tr_cl                  false
% 2.38/1.01  --smt_preprocessing                     true
% 2.38/1.01  --smt_ac_axioms                         fast
% 2.38/1.01  --preprocessed_out                      false
% 2.38/1.01  --preprocessed_stats                    false
% 2.38/1.01  
% 2.38/1.01  ------ Abstraction refinement Options
% 2.38/1.01  
% 2.38/1.01  --abstr_ref                             []
% 2.38/1.01  --abstr_ref_prep                        false
% 2.38/1.01  --abstr_ref_until_sat                   false
% 2.38/1.01  --abstr_ref_sig_restrict                funpre
% 2.38/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.01  --abstr_ref_under                       []
% 2.38/1.01  
% 2.38/1.01  ------ SAT Options
% 2.38/1.01  
% 2.38/1.01  --sat_mode                              false
% 2.38/1.01  --sat_fm_restart_options                ""
% 2.38/1.01  --sat_gr_def                            false
% 2.38/1.01  --sat_epr_types                         true
% 2.38/1.01  --sat_non_cyclic_types                  false
% 2.38/1.01  --sat_finite_models                     false
% 2.38/1.01  --sat_fm_lemmas                         false
% 2.38/1.01  --sat_fm_prep                           false
% 2.38/1.01  --sat_fm_uc_incr                        true
% 2.38/1.01  --sat_out_model                         small
% 2.38/1.01  --sat_out_clauses                       false
% 2.38/1.01  
% 2.38/1.01  ------ QBF Options
% 2.38/1.01  
% 2.38/1.01  --qbf_mode                              false
% 2.38/1.01  --qbf_elim_univ                         false
% 2.38/1.01  --qbf_dom_inst                          none
% 2.38/1.01  --qbf_dom_pre_inst                      false
% 2.38/1.01  --qbf_sk_in                             false
% 2.38/1.01  --qbf_pred_elim                         true
% 2.38/1.01  --qbf_split                             512
% 2.38/1.01  
% 2.38/1.01  ------ BMC1 Options
% 2.38/1.01  
% 2.38/1.01  --bmc1_incremental                      false
% 2.38/1.01  --bmc1_axioms                           reachable_all
% 2.38/1.01  --bmc1_min_bound                        0
% 2.38/1.01  --bmc1_max_bound                        -1
% 2.38/1.01  --bmc1_max_bound_default                -1
% 2.38/1.01  --bmc1_symbol_reachability              true
% 2.38/1.01  --bmc1_property_lemmas                  false
% 2.38/1.01  --bmc1_k_induction                      false
% 2.38/1.01  --bmc1_non_equiv_states                 false
% 2.38/1.01  --bmc1_deadlock                         false
% 2.38/1.01  --bmc1_ucm                              false
% 2.38/1.01  --bmc1_add_unsat_core                   none
% 2.38/1.01  --bmc1_unsat_core_children              false
% 2.38/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.01  --bmc1_out_stat                         full
% 2.38/1.01  --bmc1_ground_init                      false
% 2.38/1.01  --bmc1_pre_inst_next_state              false
% 2.38/1.01  --bmc1_pre_inst_state                   false
% 2.38/1.01  --bmc1_pre_inst_reach_state             false
% 2.38/1.01  --bmc1_out_unsat_core                   false
% 2.38/1.01  --bmc1_aig_witness_out                  false
% 2.38/1.01  --bmc1_verbose                          false
% 2.38/1.01  --bmc1_dump_clauses_tptp                false
% 2.38/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.01  --bmc1_dump_file                        -
% 2.38/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.01  --bmc1_ucm_extend_mode                  1
% 2.38/1.01  --bmc1_ucm_init_mode                    2
% 2.38/1.01  --bmc1_ucm_cone_mode                    none
% 2.38/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.01  --bmc1_ucm_relax_model                  4
% 2.38/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.01  --bmc1_ucm_layered_model                none
% 2.38/1.01  --bmc1_ucm_max_lemma_size               10
% 2.38/1.01  
% 2.38/1.01  ------ AIG Options
% 2.38/1.01  
% 2.38/1.01  --aig_mode                              false
% 2.38/1.01  
% 2.38/1.01  ------ Instantiation Options
% 2.38/1.01  
% 2.38/1.01  --instantiation_flag                    true
% 2.38/1.01  --inst_sos_flag                         false
% 2.38/1.01  --inst_sos_phase                        true
% 2.38/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.01  --inst_lit_sel_side                     num_symb
% 2.38/1.01  --inst_solver_per_active                1400
% 2.38/1.01  --inst_solver_calls_frac                1.
% 2.38/1.01  --inst_passive_queue_type               priority_queues
% 2.38/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.01  --inst_passive_queues_freq              [25;2]
% 2.38/1.01  --inst_dismatching                      true
% 2.38/1.01  --inst_eager_unprocessed_to_passive     true
% 2.38/1.01  --inst_prop_sim_given                   true
% 2.38/1.01  --inst_prop_sim_new                     false
% 2.38/1.01  --inst_subs_new                         false
% 2.38/1.01  --inst_eq_res_simp                      false
% 2.38/1.01  --inst_subs_given                       false
% 2.38/1.01  --inst_orphan_elimination               true
% 2.38/1.01  --inst_learning_loop_flag               true
% 2.38/1.01  --inst_learning_start                   3000
% 2.38/1.01  --inst_learning_factor                  2
% 2.38/1.01  --inst_start_prop_sim_after_learn       3
% 2.38/1.01  --inst_sel_renew                        solver
% 2.38/1.01  --inst_lit_activity_flag                true
% 2.38/1.01  --inst_restr_to_given                   false
% 2.38/1.01  --inst_activity_threshold               500
% 2.38/1.01  --inst_out_proof                        true
% 2.38/1.01  
% 2.38/1.01  ------ Resolution Options
% 2.38/1.01  
% 2.38/1.01  --resolution_flag                       true
% 2.38/1.01  --res_lit_sel                           adaptive
% 2.38/1.01  --res_lit_sel_side                      none
% 2.38/1.01  --res_ordering                          kbo
% 2.38/1.01  --res_to_prop_solver                    active
% 2.38/1.01  --res_prop_simpl_new                    false
% 2.38/1.01  --res_prop_simpl_given                  true
% 2.38/1.01  --res_passive_queue_type                priority_queues
% 2.38/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.01  --res_passive_queues_freq               [15;5]
% 2.38/1.01  --res_forward_subs                      full
% 2.38/1.01  --res_backward_subs                     full
% 2.38/1.01  --res_forward_subs_resolution           true
% 2.38/1.01  --res_backward_subs_resolution          true
% 2.38/1.01  --res_orphan_elimination                true
% 2.38/1.01  --res_time_limit                        2.
% 2.38/1.01  --res_out_proof                         true
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Options
% 2.38/1.01  
% 2.38/1.01  --superposition_flag                    true
% 2.38/1.01  --sup_passive_queue_type                priority_queues
% 2.38/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.01  --demod_completeness_check              fast
% 2.38/1.01  --demod_use_ground                      true
% 2.38/1.01  --sup_to_prop_solver                    passive
% 2.38/1.01  --sup_prop_simpl_new                    true
% 2.38/1.01  --sup_prop_simpl_given                  true
% 2.38/1.01  --sup_fun_splitting                     false
% 2.38/1.01  --sup_smt_interval                      50000
% 2.38/1.01  
% 2.38/1.01  ------ Superposition Simplification Setup
% 2.38/1.01  
% 2.38/1.01  --sup_indices_passive                   []
% 2.38/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_full_bw                           [BwDemod]
% 2.38/1.01  --sup_immed_triv                        [TrivRules]
% 2.38/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_immed_bw_main                     []
% 2.38/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.01  
% 2.38/1.01  ------ Combination Options
% 2.38/1.01  
% 2.38/1.01  --comb_res_mult                         3
% 2.38/1.01  --comb_sup_mult                         2
% 2.38/1.01  --comb_inst_mult                        10
% 2.38/1.01  
% 2.38/1.01  ------ Debug Options
% 2.38/1.01  
% 2.38/1.01  --dbg_backtrace                         false
% 2.38/1.01  --dbg_dump_prop_clauses                 false
% 2.38/1.01  --dbg_dump_prop_clauses_file            -
% 2.38/1.01  --dbg_out_stat                          false
% 2.38/1.01  ------ Parsing...
% 2.38/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.38/1.01  ------ Proving...
% 2.38/1.01  ------ Problem Properties 
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  clauses                                 24
% 2.38/1.01  conjectures                             7
% 2.38/1.01  EPR                                     9
% 2.38/1.01  Horn                                    20
% 2.38/1.01  unary                                   9
% 2.38/1.01  binary                                  7
% 2.38/1.01  lits                                    51
% 2.38/1.01  lits eq                                 9
% 2.38/1.01  fd_pure                                 0
% 2.38/1.01  fd_pseudo                               0
% 2.38/1.01  fd_cond                                 1
% 2.38/1.01  fd_pseudo_cond                          0
% 2.38/1.01  AC symbols                              0
% 2.38/1.01  
% 2.38/1.01  ------ Schedule dynamic 5 is on 
% 2.38/1.01  
% 2.38/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.38/1.01  
% 2.38/1.01  
% 2.38/1.01  ------ 
% 2.38/1.01  Current options:
% 2.38/1.01  ------ 
% 2.38/1.01  
% 2.38/1.01  ------ Input Options
% 2.38/1.01  
% 2.38/1.01  --out_options                           all
% 2.38/1.01  --tptp_safe_out                         true
% 2.38/1.01  --problem_path                          ""
% 2.38/1.01  --include_path                          ""
% 2.38/1.01  --clausifier                            res/vclausify_rel
% 2.38/1.01  --clausifier_options                    --mode clausify
% 2.38/1.01  --stdin                                 false
% 2.38/1.01  --stats_out                             all
% 2.38/1.01  
% 2.38/1.01  ------ General Options
% 2.38/1.01  
% 2.38/1.01  --fof                                   false
% 2.38/1.01  --time_out_real                         305.
% 2.38/1.01  --time_out_virtual                      -1.
% 2.38/1.01  --symbol_type_check                     false
% 2.38/1.01  --clausify_out                          false
% 2.38/1.01  --sig_cnt_out                           false
% 2.38/1.01  --trig_cnt_out                          false
% 2.38/1.01  --trig_cnt_out_tolerance                1.
% 2.38/1.01  --trig_cnt_out_sk_spl                   false
% 2.38/1.01  --abstr_cl_out                          false
% 2.38/1.01  
% 2.38/1.01  ------ Global Options
% 2.38/1.01  
% 2.38/1.01  --schedule                              default
% 2.38/1.01  --add_important_lit                     false
% 2.38/1.01  --prop_solver_per_cl                    1000
% 2.38/1.01  --min_unsat_core                        false
% 2.38/1.01  --soft_assumptions                      false
% 2.38/1.01  --soft_lemma_size                       3
% 2.38/1.01  --prop_impl_unit_size                   0
% 2.38/1.01  --prop_impl_unit                        []
% 2.38/1.01  --share_sel_clauses                     true
% 2.38/1.01  --reset_solvers                         false
% 2.38/1.01  --bc_imp_inh                            [conj_cone]
% 2.38/1.01  --conj_cone_tolerance                   3.
% 2.38/1.01  --extra_neg_conj                        none
% 2.38/1.01  --large_theory_mode                     true
% 2.38/1.01  --prolific_symb_bound                   200
% 2.38/1.01  --lt_threshold                          2000
% 2.38/1.01  --clause_weak_htbl                      true
% 2.38/1.01  --gc_record_bc_elim                     false
% 2.38/1.01  
% 2.38/1.01  ------ Preprocessing Options
% 2.38/1.01  
% 2.38/1.01  --preprocessing_flag                    true
% 2.38/1.01  --time_out_prep_mult                    0.1
% 2.38/1.01  --splitting_mode                        input
% 2.38/1.01  --splitting_grd                         true
% 2.38/1.01  --splitting_cvd                         false
% 2.38/1.01  --splitting_cvd_svl                     false
% 2.38/1.01  --splitting_nvd                         32
% 2.38/1.01  --sub_typing                            true
% 2.38/1.01  --prep_gs_sim                           true
% 2.38/1.01  --prep_unflatten                        true
% 2.38/1.01  --prep_res_sim                          true
% 2.38/1.01  --prep_upred                            true
% 2.38/1.01  --prep_sem_filter                       exhaustive
% 2.38/1.01  --prep_sem_filter_out                   false
% 2.38/1.01  --pred_elim                             true
% 2.38/1.01  --res_sim_input                         true
% 2.38/1.01  --eq_ax_congr_red                       true
% 2.38/1.01  --pure_diseq_elim                       true
% 2.38/1.01  --brand_transform                       false
% 2.38/1.01  --non_eq_to_eq                          false
% 2.38/1.01  --prep_def_merge                        true
% 2.38/1.01  --prep_def_merge_prop_impl              false
% 2.38/1.01  --prep_def_merge_mbd                    true
% 2.38/1.01  --prep_def_merge_tr_red                 false
% 2.38/1.01  --prep_def_merge_tr_cl                  false
% 2.38/1.01  --smt_preprocessing                     true
% 2.38/1.01  --smt_ac_axioms                         fast
% 2.38/1.01  --preprocessed_out                      false
% 2.38/1.01  --preprocessed_stats                    false
% 2.38/1.01  
% 2.38/1.01  ------ Abstraction refinement Options
% 2.38/1.01  
% 2.38/1.01  --abstr_ref                             []
% 2.38/1.01  --abstr_ref_prep                        false
% 2.38/1.01  --abstr_ref_until_sat                   false
% 2.38/1.01  --abstr_ref_sig_restrict                funpre
% 2.38/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.38/1.01  --abstr_ref_under                       []
% 2.38/1.01  
% 2.38/1.01  ------ SAT Options
% 2.38/1.01  
% 2.38/1.01  --sat_mode                              false
% 2.38/1.01  --sat_fm_restart_options                ""
% 2.38/1.01  --sat_gr_def                            false
% 2.38/1.01  --sat_epr_types                         true
% 2.38/1.01  --sat_non_cyclic_types                  false
% 2.38/1.01  --sat_finite_models                     false
% 2.38/1.01  --sat_fm_lemmas                         false
% 2.38/1.01  --sat_fm_prep                           false
% 2.38/1.01  --sat_fm_uc_incr                        true
% 2.38/1.01  --sat_out_model                         small
% 2.38/1.01  --sat_out_clauses                       false
% 2.38/1.01  
% 2.38/1.01  ------ QBF Options
% 2.38/1.01  
% 2.38/1.01  --qbf_mode                              false
% 2.38/1.01  --qbf_elim_univ                         false
% 2.38/1.01  --qbf_dom_inst                          none
% 2.38/1.01  --qbf_dom_pre_inst                      false
% 2.38/1.01  --qbf_sk_in                             false
% 2.38/1.01  --qbf_pred_elim                         true
% 2.38/1.01  --qbf_split                             512
% 2.38/1.01  
% 2.38/1.01  ------ BMC1 Options
% 2.38/1.01  
% 2.38/1.01  --bmc1_incremental                      false
% 2.38/1.01  --bmc1_axioms                           reachable_all
% 2.38/1.01  --bmc1_min_bound                        0
% 2.38/1.01  --bmc1_max_bound                        -1
% 2.38/1.01  --bmc1_max_bound_default                -1
% 2.38/1.01  --bmc1_symbol_reachability              true
% 2.38/1.01  --bmc1_property_lemmas                  false
% 2.38/1.01  --bmc1_k_induction                      false
% 2.38/1.01  --bmc1_non_equiv_states                 false
% 2.38/1.01  --bmc1_deadlock                         false
% 2.38/1.01  --bmc1_ucm                              false
% 2.38/1.01  --bmc1_add_unsat_core                   none
% 2.38/1.01  --bmc1_unsat_core_children              false
% 2.38/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.38/1.01  --bmc1_out_stat                         full
% 2.38/1.01  --bmc1_ground_init                      false
% 2.38/1.01  --bmc1_pre_inst_next_state              false
% 2.38/1.01  --bmc1_pre_inst_state                   false
% 2.38/1.01  --bmc1_pre_inst_reach_state             false
% 2.38/1.01  --bmc1_out_unsat_core                   false
% 2.38/1.01  --bmc1_aig_witness_out                  false
% 2.38/1.01  --bmc1_verbose                          false
% 2.38/1.01  --bmc1_dump_clauses_tptp                false
% 2.38/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.38/1.01  --bmc1_dump_file                        -
% 2.38/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.38/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.38/1.01  --bmc1_ucm_extend_mode                  1
% 2.38/1.02  --bmc1_ucm_init_mode                    2
% 2.38/1.02  --bmc1_ucm_cone_mode                    none
% 2.38/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.38/1.02  --bmc1_ucm_relax_model                  4
% 2.38/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.38/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.38/1.02  --bmc1_ucm_layered_model                none
% 2.38/1.02  --bmc1_ucm_max_lemma_size               10
% 2.38/1.02  
% 2.38/1.02  ------ AIG Options
% 2.38/1.02  
% 2.38/1.02  --aig_mode                              false
% 2.38/1.02  
% 2.38/1.02  ------ Instantiation Options
% 2.38/1.02  
% 2.38/1.02  --instantiation_flag                    true
% 2.38/1.02  --inst_sos_flag                         false
% 2.38/1.02  --inst_sos_phase                        true
% 2.38/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.38/1.02  --inst_lit_sel_side                     none
% 2.38/1.02  --inst_solver_per_active                1400
% 2.38/1.02  --inst_solver_calls_frac                1.
% 2.38/1.02  --inst_passive_queue_type               priority_queues
% 2.38/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.38/1.02  --inst_passive_queues_freq              [25;2]
% 2.38/1.02  --inst_dismatching                      true
% 2.38/1.02  --inst_eager_unprocessed_to_passive     true
% 2.38/1.02  --inst_prop_sim_given                   true
% 2.38/1.02  --inst_prop_sim_new                     false
% 2.38/1.02  --inst_subs_new                         false
% 2.38/1.02  --inst_eq_res_simp                      false
% 2.38/1.02  --inst_subs_given                       false
% 2.38/1.02  --inst_orphan_elimination               true
% 2.38/1.02  --inst_learning_loop_flag               true
% 2.38/1.02  --inst_learning_start                   3000
% 2.38/1.02  --inst_learning_factor                  2
% 2.38/1.02  --inst_start_prop_sim_after_learn       3
% 2.38/1.02  --inst_sel_renew                        solver
% 2.38/1.02  --inst_lit_activity_flag                true
% 2.38/1.02  --inst_restr_to_given                   false
% 2.38/1.02  --inst_activity_threshold               500
% 2.38/1.02  --inst_out_proof                        true
% 2.38/1.02  
% 2.38/1.02  ------ Resolution Options
% 2.38/1.02  
% 2.38/1.02  --resolution_flag                       false
% 2.38/1.02  --res_lit_sel                           adaptive
% 2.38/1.02  --res_lit_sel_side                      none
% 2.38/1.02  --res_ordering                          kbo
% 2.38/1.02  --res_to_prop_solver                    active
% 2.38/1.02  --res_prop_simpl_new                    false
% 2.38/1.02  --res_prop_simpl_given                  true
% 2.38/1.02  --res_passive_queue_type                priority_queues
% 2.38/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.38/1.02  --res_passive_queues_freq               [15;5]
% 2.38/1.02  --res_forward_subs                      full
% 2.38/1.02  --res_backward_subs                     full
% 2.38/1.02  --res_forward_subs_resolution           true
% 2.38/1.02  --res_backward_subs_resolution          true
% 2.38/1.02  --res_orphan_elimination                true
% 2.38/1.02  --res_time_limit                        2.
% 2.38/1.02  --res_out_proof                         true
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Options
% 2.38/1.02  
% 2.38/1.02  --superposition_flag                    true
% 2.38/1.02  --sup_passive_queue_type                priority_queues
% 2.38/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.38/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.38/1.02  --demod_completeness_check              fast
% 2.38/1.02  --demod_use_ground                      true
% 2.38/1.02  --sup_to_prop_solver                    passive
% 2.38/1.02  --sup_prop_simpl_new                    true
% 2.38/1.02  --sup_prop_simpl_given                  true
% 2.38/1.02  --sup_fun_splitting                     false
% 2.38/1.02  --sup_smt_interval                      50000
% 2.38/1.02  
% 2.38/1.02  ------ Superposition Simplification Setup
% 2.38/1.02  
% 2.38/1.02  --sup_indices_passive                   []
% 2.38/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.38/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.38/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_full_bw                           [BwDemod]
% 2.38/1.02  --sup_immed_triv                        [TrivRules]
% 2.38/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.38/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_immed_bw_main                     []
% 2.38/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.38/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.38/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.38/1.02  
% 2.38/1.02  ------ Combination Options
% 2.38/1.02  
% 2.38/1.02  --comb_res_mult                         3
% 2.38/1.02  --comb_sup_mult                         2
% 2.38/1.02  --comb_inst_mult                        10
% 2.38/1.02  
% 2.38/1.02  ------ Debug Options
% 2.38/1.02  
% 2.38/1.02  --dbg_backtrace                         false
% 2.38/1.02  --dbg_dump_prop_clauses                 false
% 2.38/1.02  --dbg_dump_prop_clauses_file            -
% 2.38/1.02  --dbg_out_stat                          false
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  ------ Proving...
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  % SZS status Theorem for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  fof(f14,conjecture,(
% 2.38/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f15,negated_conjecture,(
% 2.38/1.02    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.38/1.02    inference(negated_conjecture,[],[f14])).
% 2.38/1.02  
% 2.38/1.02  fof(f31,plain,(
% 2.38/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.38/1.02    inference(ennf_transformation,[],[f15])).
% 2.38/1.02  
% 2.38/1.02  fof(f32,plain,(
% 2.38/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.38/1.02    inference(flattening,[],[f31])).
% 2.38/1.02  
% 2.38/1.02  fof(f44,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f43,plain,(
% 2.38/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f42,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f41,plain,(
% 2.38/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f45,plain,(
% 2.38/1.02    (((k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f32,f44,f43,f42,f41])).
% 2.38/1.02  
% 2.38/1.02  fof(f68,plain,(
% 2.38/1.02    m1_subset_1(sK7,sK3)),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f5,axiom,(
% 2.38/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f19,plain,(
% 2.38/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.38/1.02    inference(ennf_transformation,[],[f5])).
% 2.38/1.02  
% 2.38/1.02  fof(f20,plain,(
% 2.38/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.38/1.02    inference(flattening,[],[f19])).
% 2.38/1.02  
% 2.38/1.02  fof(f53,plain,(
% 2.38/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f20])).
% 2.38/1.02  
% 2.38/1.02  fof(f70,plain,(
% 2.38/1.02    k1_xboole_0 != sK3),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f3,axiom,(
% 2.38/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f18,plain,(
% 2.38/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.38/1.02    inference(ennf_transformation,[],[f3])).
% 2.38/1.02  
% 2.38/1.02  fof(f51,plain,(
% 2.38/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f18])).
% 2.38/1.02  
% 2.38/1.02  fof(f13,axiom,(
% 2.38/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f29,plain,(
% 2.38/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.38/1.02    inference(ennf_transformation,[],[f13])).
% 2.38/1.02  
% 2.38/1.02  fof(f30,plain,(
% 2.38/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.38/1.02    inference(flattening,[],[f29])).
% 2.38/1.02  
% 2.38/1.02  fof(f61,plain,(
% 2.38/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f30])).
% 2.38/1.02  
% 2.38/1.02  fof(f64,plain,(
% 2.38/1.02    v1_funct_2(sK5,sK3,sK4)),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f63,plain,(
% 2.38/1.02    v1_funct_1(sK5)),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f65,plain,(
% 2.38/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f67,plain,(
% 2.38/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f10,axiom,(
% 2.38/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f24,plain,(
% 2.38/1.02    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/1.02    inference(ennf_transformation,[],[f10])).
% 2.38/1.02  
% 2.38/1.02  fof(f58,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.38/1.02    inference(cnf_transformation,[],[f24])).
% 2.38/1.02  
% 2.38/1.02  fof(f69,plain,(
% 2.38/1.02    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f2,axiom,(
% 2.38/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f17,plain,(
% 2.38/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.38/1.02    inference(ennf_transformation,[],[f2])).
% 2.38/1.02  
% 2.38/1.02  fof(f37,plain,(
% 2.38/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/1.02    inference(nnf_transformation,[],[f17])).
% 2.38/1.02  
% 2.38/1.02  fof(f38,plain,(
% 2.38/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/1.02    inference(rectify,[],[f37])).
% 2.38/1.02  
% 2.38/1.02  fof(f39,plain,(
% 2.38/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f40,plain,(
% 2.38/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 2.38/1.02  
% 2.38/1.02  fof(f48,plain,(
% 2.38/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f40])).
% 2.38/1.02  
% 2.38/1.02  fof(f62,plain,(
% 2.38/1.02    ~v1_xboole_0(sK4)),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f8,axiom,(
% 2.38/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f22,plain,(
% 2.38/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.38/1.02    inference(ennf_transformation,[],[f8])).
% 2.38/1.02  
% 2.38/1.02  fof(f56,plain,(
% 2.38/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f22])).
% 2.38/1.02  
% 2.38/1.02  fof(f4,axiom,(
% 2.38/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f52,plain,(
% 2.38/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f4])).
% 2.38/1.02  
% 2.38/1.02  fof(f1,axiom,(
% 2.38/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f33,plain,(
% 2.38/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.38/1.02    inference(nnf_transformation,[],[f1])).
% 2.38/1.02  
% 2.38/1.02  fof(f34,plain,(
% 2.38/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.38/1.02    inference(rectify,[],[f33])).
% 2.38/1.02  
% 2.38/1.02  fof(f35,plain,(
% 2.38/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.38/1.02    introduced(choice_axiom,[])).
% 2.38/1.02  
% 2.38/1.02  fof(f36,plain,(
% 2.38/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.38/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.38/1.02  
% 2.38/1.02  fof(f47,plain,(
% 2.38/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f36])).
% 2.38/1.02  
% 2.38/1.02  fof(f9,axiom,(
% 2.38/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f16,plain,(
% 2.38/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.38/1.02    inference(pure_predicate_removal,[],[f9])).
% 2.38/1.02  
% 2.38/1.02  fof(f23,plain,(
% 2.38/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/1.02    inference(ennf_transformation,[],[f16])).
% 2.38/1.02  
% 2.38/1.02  fof(f57,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.38/1.02    inference(cnf_transformation,[],[f23])).
% 2.38/1.02  
% 2.38/1.02  fof(f11,axiom,(
% 2.38/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f25,plain,(
% 2.38/1.02    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.38/1.02    inference(ennf_transformation,[],[f11])).
% 2.38/1.02  
% 2.38/1.02  fof(f26,plain,(
% 2.38/1.02    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.38/1.02    inference(flattening,[],[f25])).
% 2.38/1.02  
% 2.38/1.02  fof(f59,plain,(
% 2.38/1.02    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f26])).
% 2.38/1.02  
% 2.38/1.02  fof(f66,plain,(
% 2.38/1.02    v1_funct_1(sK6)),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  fof(f6,axiom,(
% 2.38/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f21,plain,(
% 2.38/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.38/1.02    inference(ennf_transformation,[],[f6])).
% 2.38/1.02  
% 2.38/1.02  fof(f54,plain,(
% 2.38/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f21])).
% 2.38/1.02  
% 2.38/1.02  fof(f7,axiom,(
% 2.38/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f55,plain,(
% 2.38/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.38/1.02    inference(cnf_transformation,[],[f7])).
% 2.38/1.02  
% 2.38/1.02  fof(f12,axiom,(
% 2.38/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.38/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.38/1.02  
% 2.38/1.02  fof(f27,plain,(
% 2.38/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.38/1.02    inference(ennf_transformation,[],[f12])).
% 2.38/1.02  
% 2.38/1.02  fof(f28,plain,(
% 2.38/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.38/1.02    inference(flattening,[],[f27])).
% 2.38/1.02  
% 2.38/1.02  fof(f60,plain,(
% 2.38/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.38/1.02    inference(cnf_transformation,[],[f28])).
% 2.38/1.02  
% 2.38/1.02  fof(f71,plain,(
% 2.38/1.02    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 2.38/1.02    inference(cnf_transformation,[],[f45])).
% 2.38/1.02  
% 2.38/1.02  cnf(c_19,negated_conjecture,
% 2.38/1.02      ( m1_subset_1(sK7,sK3) ),
% 2.38/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1700,plain,
% 2.38/1.02      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_7,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1706,plain,
% 2.38/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 2.38/1.02      | r2_hidden(X0,X1) = iProver_top
% 2.38/1.02      | v1_xboole_0(X1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3034,plain,
% 2.38/1.02      ( r2_hidden(sK7,sK3) = iProver_top
% 2.38/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_1700,c_1706]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_32,plain,
% 2.38/1.02      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_17,negated_conjecture,
% 2.38/1.02      ( k1_xboole_0 != sK3 ),
% 2.38/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1902,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1903,plain,
% 2.38/1.02      ( m1_subset_1(sK7,sK3) != iProver_top
% 2.38/1.02      | r2_hidden(sK7,sK3) = iProver_top
% 2.38/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1902]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_5,plain,
% 2.38/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.38/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1960,plain,
% 2.38/1.02      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1961,plain,
% 2.38/1.02      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_1960]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3202,plain,
% 2.38/1.02      ( r2_hidden(sK7,sK3) = iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_3034,c_32,c_17,c_1903,c_1961]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_15,plain,
% 2.38/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.38/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.38/1.02      | ~ r2_hidden(X3,X1)
% 2.38/1.02      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | k1_xboole_0 = X2 ),
% 2.38/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_23,negated_conjecture,
% 2.38/1.02      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.38/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_293,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.38/1.02      | ~ r2_hidden(X3,X1)
% 2.38/1.02      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | sK4 != X2
% 2.38/1.02      | sK3 != X1
% 2.38/1.02      | sK5 != X0
% 2.38/1.02      | k1_xboole_0 = X2 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_294,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.38/1.02      | ~ r2_hidden(X0,sK3)
% 2.38/1.02      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
% 2.38/1.02      | ~ v1_funct_1(sK5)
% 2.38/1.02      | k1_xboole_0 = sK4 ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_293]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_24,negated_conjecture,
% 2.38/1.02      ( v1_funct_1(sK5) ),
% 2.38/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_22,negated_conjecture,
% 2.38/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.38/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_298,plain,
% 2.38/1.02      ( r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
% 2.38/1.02      | ~ r2_hidden(X0,sK3)
% 2.38/1.02      | k1_xboole_0 = sK4 ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_294,c_24,c_22]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_299,plain,
% 2.38/1.02      ( ~ r2_hidden(X0,sK3)
% 2.38/1.02      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5))
% 2.38/1.02      | k1_xboole_0 = sK4 ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_298]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1696,plain,
% 2.38/1.02      ( k1_xboole_0 = sK4
% 2.38/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.38/1.02      | r2_hidden(k1_funct_1(sK5,X0),k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_20,negated_conjecture,
% 2.38/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 2.38/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1699,plain,
% 2.38/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_12,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.38/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1702,plain,
% 2.38/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.38/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2435,plain,
% 2.38/1.02      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_1699,c_1702]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_18,negated_conjecture,
% 2.38/1.02      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 2.38/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1701,plain,
% 2.38/1.02      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2729,plain,
% 2.38/1.02      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relat_1(sK6)) = iProver_top ),
% 2.38/1.02      inference(demodulation,[status(thm)],[c_2435,c_1701]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_4,plain,
% 2.38/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.38/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1709,plain,
% 2.38/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.38/1.02      | r2_hidden(X2,X0) != iProver_top
% 2.38/1.02      | r2_hidden(X2,X1) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3057,plain,
% 2.38/1.02      ( r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top
% 2.38/1.02      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_2729,c_1709]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3455,plain,
% 2.38/1.02      ( sK4 = k1_xboole_0
% 2.38/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.38/1.02      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_1696,c_3057]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_25,negated_conjecture,
% 2.38/1.02      ( ~ v1_xboole_0(sK4) ),
% 2.38/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_10,plain,
% 2.38/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1888,plain,
% 2.38/1.02      ( ~ r1_tarski(X0,sK0(X0)) | ~ r2_hidden(sK0(X0),X0) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2063,plain,
% 2.38/1.02      ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
% 2.38/1.02      | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1888]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_6,plain,
% 2.38/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2064,plain,
% 2.38/1.02      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_0,plain,
% 2.38/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2718,plain,
% 2.38/1.02      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 2.38/1.02      | v1_xboole_0(k1_xboole_0) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1277,plain,
% 2.38/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.38/1.02      theory(equality) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3125,plain,
% 2.38/1.02      ( v1_xboole_0(X0)
% 2.38/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.38/1.02      | X0 != k1_xboole_0 ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1277]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3130,plain,
% 2.38/1.02      ( v1_xboole_0(sK4)
% 2.38/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.38/1.02      | sK4 != k1_xboole_0 ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_3125]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3710,plain,
% 2.38/1.02      ( r2_hidden(X0,sK3) != iProver_top
% 2.38/1.02      | r2_hidden(k1_funct_1(sK5,X0),k1_relat_1(sK6)) = iProver_top ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_3455,c_25,c_2063,c_2064,c_2718,c_3130]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_11,plain,
% 2.38/1.02      ( v5_relat_1(X0,X1)
% 2.38/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.38/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_13,plain,
% 2.38/1.02      ( ~ v5_relat_1(X0,X1)
% 2.38/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | ~ v1_relat_1(X0)
% 2.38/1.02      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.38/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_267,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.38/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | ~ v1_relat_1(X0)
% 2.38/1.02      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.38/1.02      inference(resolution,[status(thm)],[c_11,c_13]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_21,negated_conjecture,
% 2.38/1.02      ( v1_funct_1(sK6) ),
% 2.38/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_451,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.38/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.38/1.02      | ~ v1_relat_1(X0)
% 2.38/1.02      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3)
% 2.38/1.02      | sK6 != X0 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_267,c_21]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_452,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.38/1.02      | ~ r2_hidden(X2,k1_relat_1(sK6))
% 2.38/1.02      | ~ v1_relat_1(sK6)
% 2.38/1.02      | k7_partfun1(X1,sK6,X2) = k1_funct_1(sK6,X2) ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_451]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1694,plain,
% 2.38/1.02      ( k7_partfun1(X0,sK6,X1) = k1_funct_1(sK6,X1)
% 2.38/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.38/1.02      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 2.38/1.02      | v1_relat_1(sK6) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2199,plain,
% 2.38/1.02      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 2.38/1.02      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 2.38/1.02      | v1_relat_1(sK6) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_1699,c_1694]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3719,plain,
% 2.38/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 2.38/1.02      | r2_hidden(X0,sK3) != iProver_top
% 2.38/1.02      | v1_relat_1(sK6) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_3710,c_2199]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_31,plain,
% 2.38/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_8,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.38/1.02      | ~ v1_relat_1(X1)
% 2.38/1.02      | v1_relat_1(X0) ),
% 2.38/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1883,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.38/1.02      | v1_relat_1(X0)
% 2.38/1.02      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2209,plain,
% 2.38/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 2.38/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK2))
% 2.38/1.02      | v1_relat_1(sK6) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_1883]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2210,plain,
% 2.38/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 2.38/1.02      | v1_relat_1(k2_zfmisc_1(sK4,sK2)) != iProver_top
% 2.38/1.02      | v1_relat_1(sK6) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_9,plain,
% 2.38/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.38/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2233,plain,
% 2.38/1.02      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) ),
% 2.38/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2234,plain,
% 2.38/1.02      ( v1_relat_1(k2_zfmisc_1(sK4,sK2)) = iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3737,plain,
% 2.38/1.02      ( r2_hidden(X0,sK3) != iProver_top
% 2.38/1.02      | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_3719,c_31,c_2210,c_2234]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3738,plain,
% 2.38/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 2.38/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_3737]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_3747,plain,
% 2.38/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_3202,c_3738]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_14,plain,
% 2.38/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.38/1.02      | ~ m1_subset_1(X3,X1)
% 2.38/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.38/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.38/1.02      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 2.38/1.02      | ~ v1_funct_1(X4)
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | v1_xboole_0(X2)
% 2.38/1.02      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.38/1.02      | k1_xboole_0 = X1 ),
% 2.38/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_314,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,X1)
% 2.38/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.38/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
% 2.38/1.02      | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
% 2.38/1.02      | ~ v1_funct_1(X2)
% 2.38/1.02      | ~ v1_funct_1(X4)
% 2.38/1.02      | v1_xboole_0(X3)
% 2.38/1.02      | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
% 2.38/1.02      | sK4 != X3
% 2.38/1.02      | sK3 != X1
% 2.38/1.02      | sK5 != X2
% 2.38/1.02      | k1_xboole_0 = X1 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_315,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 2.38/1.02      | ~ m1_subset_1(X2,sK3)
% 2.38/1.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.38/1.02      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | ~ v1_funct_1(sK5)
% 2.38/1.02      | v1_xboole_0(sK4)
% 2.38/1.02      | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
% 2.38/1.02      | k1_xboole_0 = sK3 ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_314]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_319,plain,
% 2.38/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 2.38/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 2.38/1.02      | ~ m1_subset_1(X2,sK3) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_315,c_25,c_24,c_22,c_17]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_320,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 2.38/1.02      | ~ m1_subset_1(X2,sK3)
% 2.38/1.02      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 2.38/1.02      | ~ v1_funct_1(X0)
% 2.38/1.02      | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2)) ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_319]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_433,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 2.38/1.02      | ~ m1_subset_1(X2,sK3)
% 2.38/1.02      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,X0))
% 2.38/1.02      | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,X0),X2) = k1_funct_1(X0,k1_funct_1(sK5,X2))
% 2.38/1.02      | sK6 != X0 ),
% 2.38/1.02      inference(resolution_lifted,[status(thm)],[c_320,c_21]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_434,plain,
% 2.38/1.02      ( ~ m1_subset_1(X0,sK3)
% 2.38/1.02      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
% 2.38/1.02      | ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X1,sK6))
% 2.38/1.02      | k1_funct_1(k8_funct_2(sK3,sK4,X1,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 2.38/1.02      inference(unflattening,[status(thm)],[c_433]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_1695,plain,
% 2.38/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,sK6),X1) = k1_funct_1(sK6,k1_funct_1(sK5,X1))
% 2.38/1.02      | m1_subset_1(X1,sK3) != iProver_top
% 2.38/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 2.38/1.02      | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,X0,sK6)) != iProver_top ),
% 2.38/1.02      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2256,plain,
% 2.38/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 2.38/1.02      | m1_subset_1(X0,sK3) != iProver_top
% 2.38/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_1701,c_1695]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2261,plain,
% 2.38/1.02      ( m1_subset_1(X0,sK3) != iProver_top
% 2.38/1.02      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 2.38/1.02      inference(global_propositional_subsumption,
% 2.38/1.02                [status(thm)],
% 2.38/1.02                [c_2256,c_31]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2262,plain,
% 2.38/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 2.38/1.02      | m1_subset_1(X0,sK3) != iProver_top ),
% 2.38/1.02      inference(renaming,[status(thm)],[c_2261]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2269,plain,
% 2.38/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 2.38/1.02      inference(superposition,[status(thm)],[c_1700,c_2262]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_16,negated_conjecture,
% 2.38/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 2.38/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(c_2380,plain,
% 2.38/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 2.38/1.02      inference(demodulation,[status(thm)],[c_2269,c_16]) ).
% 2.38/1.02  
% 2.38/1.02  cnf(contradiction,plain,
% 2.38/1.02      ( $false ),
% 2.38/1.02      inference(minisat,[status(thm)],[c_3747,c_2380]) ).
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.38/1.02  
% 2.38/1.02  ------                               Statistics
% 2.38/1.02  
% 2.38/1.02  ------ General
% 2.38/1.02  
% 2.38/1.02  abstr_ref_over_cycles:                  0
% 2.38/1.02  abstr_ref_under_cycles:                 0
% 2.38/1.02  gc_basic_clause_elim:                   0
% 2.38/1.02  forced_gc_time:                         0
% 2.38/1.02  parsing_time:                           0.008
% 2.38/1.02  unif_index_cands_time:                  0.
% 2.38/1.02  unif_index_add_time:                    0.
% 2.38/1.02  orderings_time:                         0.
% 2.38/1.02  out_proof_time:                         0.009
% 2.38/1.02  total_time:                             0.098
% 2.38/1.02  num_of_symbols:                         56
% 2.38/1.02  num_of_terms:                           3040
% 2.38/1.02  
% 2.38/1.02  ------ Preprocessing
% 2.38/1.02  
% 2.38/1.02  num_of_splits:                          0
% 2.38/1.02  num_of_split_atoms:                     0
% 2.38/1.02  num_of_reused_defs:                     0
% 2.38/1.02  num_eq_ax_congr_red:                    12
% 2.38/1.02  num_of_sem_filtered_clauses:            1
% 2.38/1.02  num_of_subtypes:                        0
% 2.38/1.02  monotx_restored_types:                  0
% 2.38/1.02  sat_num_of_epr_types:                   0
% 2.38/1.02  sat_num_of_non_cyclic_types:            0
% 2.38/1.02  sat_guarded_non_collapsed_types:        0
% 2.38/1.02  num_pure_diseq_elim:                    0
% 2.38/1.02  simp_replaced_by:                       0
% 2.38/1.02  res_preprocessed:                       129
% 2.38/1.02  prep_upred:                             0
% 2.38/1.02  prep_unflattend:                        54
% 2.38/1.02  smt_new_axioms:                         0
% 2.38/1.02  pred_elim_cands:                        5
% 2.38/1.02  pred_elim:                              3
% 2.38/1.02  pred_elim_cl:                           2
% 2.38/1.02  pred_elim_cycles:                       7
% 2.38/1.02  merged_defs:                            0
% 2.38/1.02  merged_defs_ncl:                        0
% 2.38/1.02  bin_hyper_res:                          0
% 2.38/1.02  prep_cycles:                            4
% 2.38/1.02  pred_elim_time:                         0.012
% 2.38/1.02  splitting_time:                         0.
% 2.38/1.02  sem_filter_time:                        0.
% 2.38/1.02  monotx_time:                            0.
% 2.38/1.02  subtype_inf_time:                       0.
% 2.38/1.02  
% 2.38/1.02  ------ Problem properties
% 2.38/1.02  
% 2.38/1.02  clauses:                                24
% 2.38/1.02  conjectures:                            7
% 2.38/1.02  epr:                                    9
% 2.38/1.02  horn:                                   20
% 2.38/1.02  ground:                                 7
% 2.38/1.02  unary:                                  9
% 2.38/1.02  binary:                                 7
% 2.38/1.02  lits:                                   51
% 2.38/1.02  lits_eq:                                9
% 2.38/1.02  fd_pure:                                0
% 2.38/1.02  fd_pseudo:                              0
% 2.38/1.02  fd_cond:                                1
% 2.38/1.02  fd_pseudo_cond:                         0
% 2.38/1.02  ac_symbols:                             0
% 2.38/1.02  
% 2.38/1.02  ------ Propositional Solver
% 2.38/1.02  
% 2.38/1.02  prop_solver_calls:                      28
% 2.38/1.02  prop_fast_solver_calls:                 911
% 2.38/1.02  smt_solver_calls:                       0
% 2.38/1.02  smt_fast_solver_calls:                  0
% 2.38/1.02  prop_num_of_clauses:                    1141
% 2.38/1.02  prop_preprocess_simplified:             4846
% 2.38/1.02  prop_fo_subsumed:                       14
% 2.38/1.02  prop_solver_time:                       0.
% 2.38/1.02  smt_solver_time:                        0.
% 2.38/1.02  smt_fast_solver_time:                   0.
% 2.38/1.02  prop_fast_solver_time:                  0.
% 2.38/1.02  prop_unsat_core_time:                   0.
% 2.38/1.02  
% 2.38/1.02  ------ QBF
% 2.38/1.02  
% 2.38/1.02  qbf_q_res:                              0
% 2.38/1.02  qbf_num_tautologies:                    0
% 2.38/1.02  qbf_prep_cycles:                        0
% 2.38/1.02  
% 2.38/1.02  ------ BMC1
% 2.38/1.02  
% 2.38/1.02  bmc1_current_bound:                     -1
% 2.38/1.02  bmc1_last_solved_bound:                 -1
% 2.38/1.02  bmc1_unsat_core_size:                   -1
% 2.38/1.02  bmc1_unsat_core_parents_size:           -1
% 2.38/1.02  bmc1_merge_next_fun:                    0
% 2.38/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.38/1.02  
% 2.38/1.02  ------ Instantiation
% 2.38/1.02  
% 2.38/1.02  inst_num_of_clauses:                    339
% 2.38/1.02  inst_num_in_passive:                    107
% 2.38/1.02  inst_num_in_active:                     219
% 2.38/1.02  inst_num_in_unprocessed:                13
% 2.38/1.02  inst_num_of_loops:                      260
% 2.38/1.02  inst_num_of_learning_restarts:          0
% 2.38/1.02  inst_num_moves_active_passive:          38
% 2.38/1.02  inst_lit_activity:                      0
% 2.38/1.02  inst_lit_activity_moves:                0
% 2.38/1.02  inst_num_tautologies:                   0
% 2.38/1.02  inst_num_prop_implied:                  0
% 2.38/1.02  inst_num_existing_simplified:           0
% 2.38/1.02  inst_num_eq_res_simplified:             0
% 2.38/1.02  inst_num_child_elim:                    0
% 2.38/1.02  inst_num_of_dismatching_blockings:      60
% 2.38/1.02  inst_num_of_non_proper_insts:           320
% 2.38/1.02  inst_num_of_duplicates:                 0
% 2.38/1.02  inst_inst_num_from_inst_to_res:         0
% 2.38/1.02  inst_dismatching_checking_time:         0.
% 2.38/1.02  
% 2.38/1.02  ------ Resolution
% 2.38/1.02  
% 2.38/1.02  res_num_of_clauses:                     0
% 2.38/1.02  res_num_in_passive:                     0
% 2.38/1.02  res_num_in_active:                      0
% 2.38/1.02  res_num_of_loops:                       133
% 2.38/1.02  res_forward_subset_subsumed:            19
% 2.38/1.02  res_backward_subset_subsumed:           0
% 2.38/1.02  res_forward_subsumed:                   0
% 2.38/1.02  res_backward_subsumed:                  0
% 2.38/1.02  res_forward_subsumption_resolution:     0
% 2.38/1.02  res_backward_subsumption_resolution:    0
% 2.38/1.02  res_clause_to_clause_subsumption:       138
% 2.38/1.02  res_orphan_elimination:                 0
% 2.38/1.02  res_tautology_del:                      46
% 2.38/1.02  res_num_eq_res_simplified:              0
% 2.38/1.02  res_num_sel_changes:                    0
% 2.38/1.02  res_moves_from_active_to_pass:          0
% 2.38/1.02  
% 2.38/1.02  ------ Superposition
% 2.38/1.02  
% 2.38/1.02  sup_time_total:                         0.
% 2.38/1.02  sup_time_generating:                    0.
% 2.38/1.02  sup_time_sim_full:                      0.
% 2.38/1.02  sup_time_sim_immed:                     0.
% 2.38/1.02  
% 2.38/1.02  sup_num_of_clauses:                     64
% 2.38/1.02  sup_num_in_active:                      50
% 2.38/1.02  sup_num_in_passive:                     14
% 2.38/1.02  sup_num_of_loops:                       51
% 2.38/1.02  sup_fw_superposition:                   29
% 2.38/1.02  sup_bw_superposition:                   19
% 2.38/1.02  sup_immediate_simplified:               4
% 2.38/1.02  sup_given_eliminated:                   0
% 2.38/1.02  comparisons_done:                       0
% 2.38/1.02  comparisons_avoided:                    0
% 2.38/1.02  
% 2.38/1.02  ------ Simplifications
% 2.38/1.02  
% 2.38/1.02  
% 2.38/1.02  sim_fw_subset_subsumed:                 3
% 2.38/1.02  sim_bw_subset_subsumed:                 0
% 2.38/1.02  sim_fw_subsumed:                        1
% 2.38/1.02  sim_bw_subsumed:                        0
% 2.38/1.02  sim_fw_subsumption_res:                 0
% 2.38/1.02  sim_bw_subsumption_res:                 0
% 2.38/1.02  sim_tautology_del:                      4
% 2.38/1.02  sim_eq_tautology_del:                   1
% 2.38/1.02  sim_eq_res_simp:                        0
% 2.38/1.02  sim_fw_demodulated:                     0
% 2.38/1.02  sim_bw_demodulated:                     2
% 2.38/1.02  sim_light_normalised:                   1
% 2.38/1.02  sim_joinable_taut:                      0
% 2.38/1.02  sim_joinable_simp:                      0
% 2.38/1.02  sim_ac_normalised:                      0
% 2.38/1.02  sim_smt_subsumption:                    0
% 2.38/1.02  
%------------------------------------------------------------------------------
