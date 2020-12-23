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
% DateTime   : Thu Dec  3 12:09:44 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 947 expanded)
%              Number of clauses        :  125 ( 292 expanded)
%              Number of leaves         :   26 ( 296 expanded)
%              Depth                    :   21
%              Number of atoms          :  746 (6224 expanded)
%              Number of equality atoms :  294 (1668 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f43,f57,f56,f55,f54])).

fof(f94,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f58])).

fof(f60,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f97,plain,(
    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f58])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1175,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1187,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2935,plain,
    ( r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1187])).

cnf(c_45,plain,
    ( m1_subset_1(sK7,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_90,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_95,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_623,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1468,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1469,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1560,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1564,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

cnf(c_1615,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1616,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_1618,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_1804,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1805,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1804])).

cnf(c_2046,plain,
    ( ~ m1_subset_1(sK7,sK3)
    | r2_hidden(sK7,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2047,plain,
    ( m1_subset_1(sK7,sK3) != iProver_top
    | r2_hidden(sK7,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2046])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2127,plain,
    ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2128,plain,
    ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2127])).

cnf(c_3301,plain,
    ( r2_hidden(sK7,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2935,c_45,c_30,c_90,c_95,c_1469,c_1564,c_1618,c_1805,c_2047,c_2128])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1172,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1179,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4197,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1179])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1183,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2320,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1172,c_1183])).

cnf(c_4203,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4197,c_2320])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_40,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,plain,
    ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_624,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1441,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1442,plain,
    ( sK4 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_1444,plain,
    ( sK4 != k1_xboole_0
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1195,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1188,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1185,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1929,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1185])).

cnf(c_2146,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_1929])).

cnf(c_5147,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4203,c_39,c_40,c_41,c_1444,c_2146])).

cnf(c_5148,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5147])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1181,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5159,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK5,sK3,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5148,c_1181])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1177,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X1,X2,X3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3874,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1177])).

cnf(c_3880,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_2(sK5,sK3,X0) = iProver_top
    | v1_funct_2(sK5,sK3,sK4) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3874,c_2320])).

cnf(c_4919,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_funct_2(sK5,sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3880,c_39,c_40,c_41,c_1444,c_2146])).

cnf(c_4920,plain,
    ( v1_funct_2(sK5,sK3,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4919])).

cnf(c_10829,plain,
    ( r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5159,c_39,c_40,c_41,c_1444,c_2146,c_3880])).

cnf(c_10830,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10829])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1174,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_20,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_14,c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_375,plain,
    ( ~ v1_funct_1(X0)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_13])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(renaming,[status(thm)],[c_375])).

cnf(c_1167,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_2062,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_1167])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_43,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2558,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2062,c_43])).

cnf(c_2559,plain,
    ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2558])).

cnf(c_10841,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10830,c_2559])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1184,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2820,plain,
    ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1174,c_1184])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1176,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2425,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2320,c_1176])).

cnf(c_3155,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2820,c_2425])).

cnf(c_11033,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10841,c_3155])).

cnf(c_11034,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | k1_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_11033])).

cnf(c_11044,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3301,c_11034])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_1182,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4435,plain,
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
    inference(superposition,[status(thm)],[c_2320,c_1182])).

cnf(c_42,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5461,plain,
    ( m1_subset_1(X2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4435,c_39,c_40,c_41,c_42,c_30,c_90,c_95,c_1469])).

cnf(c_5462,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
    | m1_subset_1(X2,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5461])).

cnf(c_5472,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2820,c_5462])).

cnf(c_44,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6101,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5472,c_43,c_44,c_3155])).

cnf(c_6102,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6101])).

cnf(c_6109,plain,
    ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(superposition,[status(thm)],[c_1175,c_6102])).

cnf(c_29,negated_conjecture,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6111,plain,
    ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    inference(demodulation,[status(thm)],[c_6109,c_29])).

cnf(c_11198,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11044,c_6111])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1191,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4287,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3155,c_1191])).

cnf(c_5903,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5)),k1_relat_1(sK6)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_4287])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(resolution,[status(thm)],[c_13,c_10])).

cnf(c_1166,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1556,plain,
    ( v1_xboole_0(k2_relat_1(sK5)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1166])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_11])).

cnf(c_197,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(renaming,[status(thm)],[c_196])).

cnf(c_1168,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_197])).

cnf(c_2798,plain,
    ( v1_funct_2(sK5,sK3,sK4) != iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1168])).

cnf(c_5959,plain,
    ( r2_hidden(sK0(k2_relat_1(sK5)),k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5903,c_39,c_41,c_30,c_90,c_95,c_1469,c_1556,c_1564,c_1618,c_1805,c_2128,c_2798])).

cnf(c_1194,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5964,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5959,c_1194])).

cnf(c_11220,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11198,c_5964])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11220,c_2146])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.44/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.02  
% 3.44/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.44/1.02  
% 3.44/1.02  ------  iProver source info
% 3.44/1.02  
% 3.44/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.44/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.44/1.02  git: non_committed_changes: false
% 3.44/1.02  git: last_make_outside_of_git: false
% 3.44/1.02  
% 3.44/1.02  ------ 
% 3.44/1.02  
% 3.44/1.02  ------ Input Options
% 3.44/1.02  
% 3.44/1.02  --out_options                           all
% 3.44/1.02  --tptp_safe_out                         true
% 3.44/1.02  --problem_path                          ""
% 3.44/1.02  --include_path                          ""
% 3.44/1.02  --clausifier                            res/vclausify_rel
% 3.44/1.02  --clausifier_options                    --mode clausify
% 3.44/1.02  --stdin                                 false
% 3.44/1.02  --stats_out                             all
% 3.44/1.02  
% 3.44/1.02  ------ General Options
% 3.44/1.02  
% 3.44/1.02  --fof                                   false
% 3.44/1.02  --time_out_real                         305.
% 3.44/1.02  --time_out_virtual                      -1.
% 3.44/1.02  --symbol_type_check                     false
% 3.44/1.02  --clausify_out                          false
% 3.44/1.02  --sig_cnt_out                           false
% 3.44/1.02  --trig_cnt_out                          false
% 3.44/1.02  --trig_cnt_out_tolerance                1.
% 3.44/1.02  --trig_cnt_out_sk_spl                   false
% 3.44/1.02  --abstr_cl_out                          false
% 3.44/1.02  
% 3.44/1.02  ------ Global Options
% 3.44/1.02  
% 3.44/1.02  --schedule                              default
% 3.44/1.02  --add_important_lit                     false
% 3.44/1.02  --prop_solver_per_cl                    1000
% 3.44/1.02  --min_unsat_core                        false
% 3.44/1.02  --soft_assumptions                      false
% 3.44/1.02  --soft_lemma_size                       3
% 3.44/1.02  --prop_impl_unit_size                   0
% 3.44/1.02  --prop_impl_unit                        []
% 3.44/1.02  --share_sel_clauses                     true
% 3.44/1.02  --reset_solvers                         false
% 3.44/1.02  --bc_imp_inh                            [conj_cone]
% 3.44/1.02  --conj_cone_tolerance                   3.
% 3.44/1.02  --extra_neg_conj                        none
% 3.44/1.02  --large_theory_mode                     true
% 3.44/1.02  --prolific_symb_bound                   200
% 3.44/1.02  --lt_threshold                          2000
% 3.44/1.02  --clause_weak_htbl                      true
% 3.44/1.02  --gc_record_bc_elim                     false
% 3.44/1.02  
% 3.44/1.02  ------ Preprocessing Options
% 3.44/1.02  
% 3.44/1.02  --preprocessing_flag                    true
% 3.44/1.02  --time_out_prep_mult                    0.1
% 3.44/1.02  --splitting_mode                        input
% 3.44/1.02  --splitting_grd                         true
% 3.44/1.02  --splitting_cvd                         false
% 3.44/1.02  --splitting_cvd_svl                     false
% 3.44/1.02  --splitting_nvd                         32
% 3.44/1.02  --sub_typing                            true
% 3.44/1.02  --prep_gs_sim                           true
% 3.44/1.02  --prep_unflatten                        true
% 3.44/1.02  --prep_res_sim                          true
% 3.44/1.02  --prep_upred                            true
% 3.44/1.02  --prep_sem_filter                       exhaustive
% 3.44/1.02  --prep_sem_filter_out                   false
% 3.44/1.02  --pred_elim                             true
% 3.44/1.02  --res_sim_input                         true
% 3.44/1.02  --eq_ax_congr_red                       true
% 3.44/1.02  --pure_diseq_elim                       true
% 3.44/1.02  --brand_transform                       false
% 3.44/1.02  --non_eq_to_eq                          false
% 3.44/1.02  --prep_def_merge                        true
% 3.44/1.02  --prep_def_merge_prop_impl              false
% 3.44/1.02  --prep_def_merge_mbd                    true
% 3.44/1.02  --prep_def_merge_tr_red                 false
% 3.44/1.02  --prep_def_merge_tr_cl                  false
% 3.44/1.02  --smt_preprocessing                     true
% 3.44/1.02  --smt_ac_axioms                         fast
% 3.44/1.02  --preprocessed_out                      false
% 3.44/1.02  --preprocessed_stats                    false
% 3.44/1.02  
% 3.44/1.02  ------ Abstraction refinement Options
% 3.44/1.02  
% 3.44/1.02  --abstr_ref                             []
% 3.44/1.02  --abstr_ref_prep                        false
% 3.44/1.02  --abstr_ref_until_sat                   false
% 3.44/1.02  --abstr_ref_sig_restrict                funpre
% 3.44/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.02  --abstr_ref_under                       []
% 3.44/1.02  
% 3.44/1.02  ------ SAT Options
% 3.44/1.02  
% 3.44/1.02  --sat_mode                              false
% 3.44/1.02  --sat_fm_restart_options                ""
% 3.44/1.02  --sat_gr_def                            false
% 3.44/1.02  --sat_epr_types                         true
% 3.44/1.02  --sat_non_cyclic_types                  false
% 3.44/1.02  --sat_finite_models                     false
% 3.44/1.02  --sat_fm_lemmas                         false
% 3.44/1.02  --sat_fm_prep                           false
% 3.44/1.02  --sat_fm_uc_incr                        true
% 3.44/1.02  --sat_out_model                         small
% 3.44/1.02  --sat_out_clauses                       false
% 3.44/1.02  
% 3.44/1.02  ------ QBF Options
% 3.44/1.02  
% 3.44/1.02  --qbf_mode                              false
% 3.44/1.02  --qbf_elim_univ                         false
% 3.44/1.02  --qbf_dom_inst                          none
% 3.44/1.02  --qbf_dom_pre_inst                      false
% 3.44/1.02  --qbf_sk_in                             false
% 3.44/1.02  --qbf_pred_elim                         true
% 3.44/1.02  --qbf_split                             512
% 3.44/1.02  
% 3.44/1.02  ------ BMC1 Options
% 3.44/1.02  
% 3.44/1.02  --bmc1_incremental                      false
% 3.44/1.02  --bmc1_axioms                           reachable_all
% 3.44/1.02  --bmc1_min_bound                        0
% 3.44/1.02  --bmc1_max_bound                        -1
% 3.44/1.02  --bmc1_max_bound_default                -1
% 3.44/1.02  --bmc1_symbol_reachability              true
% 3.44/1.02  --bmc1_property_lemmas                  false
% 3.44/1.02  --bmc1_k_induction                      false
% 3.44/1.02  --bmc1_non_equiv_states                 false
% 3.44/1.02  --bmc1_deadlock                         false
% 3.44/1.02  --bmc1_ucm                              false
% 3.44/1.02  --bmc1_add_unsat_core                   none
% 3.44/1.02  --bmc1_unsat_core_children              false
% 3.44/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.02  --bmc1_out_stat                         full
% 3.44/1.02  --bmc1_ground_init                      false
% 3.44/1.02  --bmc1_pre_inst_next_state              false
% 3.44/1.02  --bmc1_pre_inst_state                   false
% 3.44/1.02  --bmc1_pre_inst_reach_state             false
% 3.44/1.02  --bmc1_out_unsat_core                   false
% 3.44/1.02  --bmc1_aig_witness_out                  false
% 3.44/1.02  --bmc1_verbose                          false
% 3.44/1.02  --bmc1_dump_clauses_tptp                false
% 3.44/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.02  --bmc1_dump_file                        -
% 3.44/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.02  --bmc1_ucm_extend_mode                  1
% 3.44/1.02  --bmc1_ucm_init_mode                    2
% 3.44/1.02  --bmc1_ucm_cone_mode                    none
% 3.44/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.02  --bmc1_ucm_relax_model                  4
% 3.44/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.02  --bmc1_ucm_layered_model                none
% 3.44/1.02  --bmc1_ucm_max_lemma_size               10
% 3.44/1.02  
% 3.44/1.02  ------ AIG Options
% 3.44/1.02  
% 3.44/1.02  --aig_mode                              false
% 3.44/1.02  
% 3.44/1.02  ------ Instantiation Options
% 3.44/1.02  
% 3.44/1.02  --instantiation_flag                    true
% 3.44/1.02  --inst_sos_flag                         false
% 3.44/1.02  --inst_sos_phase                        true
% 3.44/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.02  --inst_lit_sel_side                     num_symb
% 3.44/1.02  --inst_solver_per_active                1400
% 3.44/1.02  --inst_solver_calls_frac                1.
% 3.44/1.02  --inst_passive_queue_type               priority_queues
% 3.44/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.02  --inst_passive_queues_freq              [25;2]
% 3.44/1.02  --inst_dismatching                      true
% 3.44/1.02  --inst_eager_unprocessed_to_passive     true
% 3.44/1.02  --inst_prop_sim_given                   true
% 3.44/1.02  --inst_prop_sim_new                     false
% 3.44/1.02  --inst_subs_new                         false
% 3.44/1.02  --inst_eq_res_simp                      false
% 3.44/1.02  --inst_subs_given                       false
% 3.44/1.02  --inst_orphan_elimination               true
% 3.44/1.02  --inst_learning_loop_flag               true
% 3.44/1.02  --inst_learning_start                   3000
% 3.44/1.02  --inst_learning_factor                  2
% 3.44/1.02  --inst_start_prop_sim_after_learn       3
% 3.44/1.02  --inst_sel_renew                        solver
% 3.44/1.02  --inst_lit_activity_flag                true
% 3.44/1.02  --inst_restr_to_given                   false
% 3.44/1.02  --inst_activity_threshold               500
% 3.44/1.02  --inst_out_proof                        true
% 3.44/1.02  
% 3.44/1.02  ------ Resolution Options
% 3.44/1.02  
% 3.44/1.02  --resolution_flag                       true
% 3.44/1.02  --res_lit_sel                           adaptive
% 3.44/1.02  --res_lit_sel_side                      none
% 3.44/1.02  --res_ordering                          kbo
% 3.44/1.02  --res_to_prop_solver                    active
% 3.44/1.02  --res_prop_simpl_new                    false
% 3.44/1.02  --res_prop_simpl_given                  true
% 3.44/1.02  --res_passive_queue_type                priority_queues
% 3.44/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.02  --res_passive_queues_freq               [15;5]
% 3.44/1.02  --res_forward_subs                      full
% 3.44/1.02  --res_backward_subs                     full
% 3.44/1.02  --res_forward_subs_resolution           true
% 3.44/1.02  --res_backward_subs_resolution          true
% 3.44/1.02  --res_orphan_elimination                true
% 3.44/1.02  --res_time_limit                        2.
% 3.44/1.02  --res_out_proof                         true
% 3.44/1.02  
% 3.44/1.02  ------ Superposition Options
% 3.44/1.02  
% 3.44/1.02  --superposition_flag                    true
% 3.44/1.02  --sup_passive_queue_type                priority_queues
% 3.44/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.02  --demod_completeness_check              fast
% 3.44/1.02  --demod_use_ground                      true
% 3.44/1.02  --sup_to_prop_solver                    passive
% 3.44/1.02  --sup_prop_simpl_new                    true
% 3.44/1.02  --sup_prop_simpl_given                  true
% 3.44/1.02  --sup_fun_splitting                     false
% 3.44/1.02  --sup_smt_interval                      50000
% 3.44/1.02  
% 3.44/1.02  ------ Superposition Simplification Setup
% 3.44/1.02  
% 3.44/1.02  --sup_indices_passive                   []
% 3.44/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.02  --sup_full_bw                           [BwDemod]
% 3.44/1.02  --sup_immed_triv                        [TrivRules]
% 3.44/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.02  --sup_immed_bw_main                     []
% 3.44/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.02  
% 3.44/1.02  ------ Combination Options
% 3.44/1.02  
% 3.44/1.02  --comb_res_mult                         3
% 3.44/1.02  --comb_sup_mult                         2
% 3.44/1.02  --comb_inst_mult                        10
% 3.44/1.02  
% 3.44/1.02  ------ Debug Options
% 3.44/1.02  
% 3.44/1.02  --dbg_backtrace                         false
% 3.44/1.02  --dbg_dump_prop_clauses                 false
% 3.44/1.02  --dbg_dump_prop_clauses_file            -
% 3.44/1.02  --dbg_out_stat                          false
% 3.44/1.02  ------ Parsing...
% 3.44/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.44/1.02  
% 3.44/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.44/1.02  
% 3.44/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.44/1.02  
% 3.44/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.44/1.02  ------ Proving...
% 3.44/1.02  ------ Problem Properties 
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  clauses                                 32
% 3.44/1.02  conjectures                             10
% 3.44/1.02  EPR                                     14
% 3.44/1.02  Horn                                    24
% 3.44/1.02  unary                                   12
% 3.44/1.02  binary                                  8
% 3.44/1.02  lits                                    87
% 3.44/1.02  lits eq                                 11
% 3.44/1.02  fd_pure                                 0
% 3.44/1.02  fd_pseudo                               0
% 3.44/1.02  fd_cond                                 4
% 3.44/1.02  fd_pseudo_cond                          1
% 3.44/1.02  AC symbols                              0
% 3.44/1.02  
% 3.44/1.02  ------ Schedule dynamic 5 is on 
% 3.44/1.02  
% 3.44/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  ------ 
% 3.44/1.02  Current options:
% 3.44/1.02  ------ 
% 3.44/1.02  
% 3.44/1.02  ------ Input Options
% 3.44/1.02  
% 3.44/1.02  --out_options                           all
% 3.44/1.02  --tptp_safe_out                         true
% 3.44/1.02  --problem_path                          ""
% 3.44/1.02  --include_path                          ""
% 3.44/1.02  --clausifier                            res/vclausify_rel
% 3.44/1.02  --clausifier_options                    --mode clausify
% 3.44/1.02  --stdin                                 false
% 3.44/1.02  --stats_out                             all
% 3.44/1.02  
% 3.44/1.02  ------ General Options
% 3.44/1.02  
% 3.44/1.02  --fof                                   false
% 3.44/1.02  --time_out_real                         305.
% 3.44/1.02  --time_out_virtual                      -1.
% 3.44/1.02  --symbol_type_check                     false
% 3.44/1.02  --clausify_out                          false
% 3.44/1.02  --sig_cnt_out                           false
% 3.44/1.02  --trig_cnt_out                          false
% 3.44/1.02  --trig_cnt_out_tolerance                1.
% 3.44/1.02  --trig_cnt_out_sk_spl                   false
% 3.44/1.02  --abstr_cl_out                          false
% 3.44/1.02  
% 3.44/1.02  ------ Global Options
% 3.44/1.02  
% 3.44/1.02  --schedule                              default
% 3.44/1.02  --add_important_lit                     false
% 3.44/1.02  --prop_solver_per_cl                    1000
% 3.44/1.02  --min_unsat_core                        false
% 3.44/1.02  --soft_assumptions                      false
% 3.44/1.02  --soft_lemma_size                       3
% 3.44/1.02  --prop_impl_unit_size                   0
% 3.44/1.02  --prop_impl_unit                        []
% 3.44/1.02  --share_sel_clauses                     true
% 3.44/1.02  --reset_solvers                         false
% 3.44/1.02  --bc_imp_inh                            [conj_cone]
% 3.44/1.02  --conj_cone_tolerance                   3.
% 3.44/1.02  --extra_neg_conj                        none
% 3.44/1.02  --large_theory_mode                     true
% 3.44/1.02  --prolific_symb_bound                   200
% 3.44/1.02  --lt_threshold                          2000
% 3.44/1.02  --clause_weak_htbl                      true
% 3.44/1.02  --gc_record_bc_elim                     false
% 3.44/1.02  
% 3.44/1.02  ------ Preprocessing Options
% 3.44/1.02  
% 3.44/1.02  --preprocessing_flag                    true
% 3.44/1.02  --time_out_prep_mult                    0.1
% 3.44/1.02  --splitting_mode                        input
% 3.44/1.02  --splitting_grd                         true
% 3.44/1.02  --splitting_cvd                         false
% 3.44/1.02  --splitting_cvd_svl                     false
% 3.44/1.02  --splitting_nvd                         32
% 3.44/1.02  --sub_typing                            true
% 3.44/1.02  --prep_gs_sim                           true
% 3.44/1.02  --prep_unflatten                        true
% 3.44/1.02  --prep_res_sim                          true
% 3.44/1.02  --prep_upred                            true
% 3.44/1.02  --prep_sem_filter                       exhaustive
% 3.44/1.02  --prep_sem_filter_out                   false
% 3.44/1.02  --pred_elim                             true
% 3.44/1.02  --res_sim_input                         true
% 3.44/1.02  --eq_ax_congr_red                       true
% 3.44/1.02  --pure_diseq_elim                       true
% 3.44/1.02  --brand_transform                       false
% 3.44/1.02  --non_eq_to_eq                          false
% 3.44/1.02  --prep_def_merge                        true
% 3.44/1.02  --prep_def_merge_prop_impl              false
% 3.44/1.02  --prep_def_merge_mbd                    true
% 3.44/1.02  --prep_def_merge_tr_red                 false
% 3.44/1.02  --prep_def_merge_tr_cl                  false
% 3.44/1.02  --smt_preprocessing                     true
% 3.44/1.02  --smt_ac_axioms                         fast
% 3.44/1.02  --preprocessed_out                      false
% 3.44/1.02  --preprocessed_stats                    false
% 3.44/1.02  
% 3.44/1.02  ------ Abstraction refinement Options
% 3.44/1.02  
% 3.44/1.02  --abstr_ref                             []
% 3.44/1.02  --abstr_ref_prep                        false
% 3.44/1.02  --abstr_ref_until_sat                   false
% 3.44/1.02  --abstr_ref_sig_restrict                funpre
% 3.44/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.44/1.02  --abstr_ref_under                       []
% 3.44/1.02  
% 3.44/1.02  ------ SAT Options
% 3.44/1.02  
% 3.44/1.02  --sat_mode                              false
% 3.44/1.02  --sat_fm_restart_options                ""
% 3.44/1.02  --sat_gr_def                            false
% 3.44/1.02  --sat_epr_types                         true
% 3.44/1.02  --sat_non_cyclic_types                  false
% 3.44/1.02  --sat_finite_models                     false
% 3.44/1.02  --sat_fm_lemmas                         false
% 3.44/1.02  --sat_fm_prep                           false
% 3.44/1.02  --sat_fm_uc_incr                        true
% 3.44/1.02  --sat_out_model                         small
% 3.44/1.02  --sat_out_clauses                       false
% 3.44/1.02  
% 3.44/1.02  ------ QBF Options
% 3.44/1.02  
% 3.44/1.02  --qbf_mode                              false
% 3.44/1.02  --qbf_elim_univ                         false
% 3.44/1.02  --qbf_dom_inst                          none
% 3.44/1.02  --qbf_dom_pre_inst                      false
% 3.44/1.02  --qbf_sk_in                             false
% 3.44/1.02  --qbf_pred_elim                         true
% 3.44/1.02  --qbf_split                             512
% 3.44/1.02  
% 3.44/1.02  ------ BMC1 Options
% 3.44/1.02  
% 3.44/1.02  --bmc1_incremental                      false
% 3.44/1.02  --bmc1_axioms                           reachable_all
% 3.44/1.02  --bmc1_min_bound                        0
% 3.44/1.02  --bmc1_max_bound                        -1
% 3.44/1.02  --bmc1_max_bound_default                -1
% 3.44/1.02  --bmc1_symbol_reachability              true
% 3.44/1.02  --bmc1_property_lemmas                  false
% 3.44/1.02  --bmc1_k_induction                      false
% 3.44/1.02  --bmc1_non_equiv_states                 false
% 3.44/1.02  --bmc1_deadlock                         false
% 3.44/1.02  --bmc1_ucm                              false
% 3.44/1.02  --bmc1_add_unsat_core                   none
% 3.44/1.02  --bmc1_unsat_core_children              false
% 3.44/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.44/1.02  --bmc1_out_stat                         full
% 3.44/1.02  --bmc1_ground_init                      false
% 3.44/1.02  --bmc1_pre_inst_next_state              false
% 3.44/1.02  --bmc1_pre_inst_state                   false
% 3.44/1.02  --bmc1_pre_inst_reach_state             false
% 3.44/1.02  --bmc1_out_unsat_core                   false
% 3.44/1.02  --bmc1_aig_witness_out                  false
% 3.44/1.02  --bmc1_verbose                          false
% 3.44/1.02  --bmc1_dump_clauses_tptp                false
% 3.44/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.44/1.02  --bmc1_dump_file                        -
% 3.44/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.44/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.44/1.02  --bmc1_ucm_extend_mode                  1
% 3.44/1.02  --bmc1_ucm_init_mode                    2
% 3.44/1.02  --bmc1_ucm_cone_mode                    none
% 3.44/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.44/1.02  --bmc1_ucm_relax_model                  4
% 3.44/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.44/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.44/1.02  --bmc1_ucm_layered_model                none
% 3.44/1.02  --bmc1_ucm_max_lemma_size               10
% 3.44/1.02  
% 3.44/1.02  ------ AIG Options
% 3.44/1.02  
% 3.44/1.02  --aig_mode                              false
% 3.44/1.02  
% 3.44/1.02  ------ Instantiation Options
% 3.44/1.02  
% 3.44/1.02  --instantiation_flag                    true
% 3.44/1.02  --inst_sos_flag                         false
% 3.44/1.02  --inst_sos_phase                        true
% 3.44/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.44/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.44/1.02  --inst_lit_sel_side                     none
% 3.44/1.02  --inst_solver_per_active                1400
% 3.44/1.02  --inst_solver_calls_frac                1.
% 3.44/1.02  --inst_passive_queue_type               priority_queues
% 3.44/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.44/1.02  --inst_passive_queues_freq              [25;2]
% 3.44/1.02  --inst_dismatching                      true
% 3.44/1.02  --inst_eager_unprocessed_to_passive     true
% 3.44/1.02  --inst_prop_sim_given                   true
% 3.44/1.02  --inst_prop_sim_new                     false
% 3.44/1.02  --inst_subs_new                         false
% 3.44/1.02  --inst_eq_res_simp                      false
% 3.44/1.02  --inst_subs_given                       false
% 3.44/1.02  --inst_orphan_elimination               true
% 3.44/1.02  --inst_learning_loop_flag               true
% 3.44/1.02  --inst_learning_start                   3000
% 3.44/1.02  --inst_learning_factor                  2
% 3.44/1.02  --inst_start_prop_sim_after_learn       3
% 3.44/1.02  --inst_sel_renew                        solver
% 3.44/1.02  --inst_lit_activity_flag                true
% 3.44/1.02  --inst_restr_to_given                   false
% 3.44/1.02  --inst_activity_threshold               500
% 3.44/1.02  --inst_out_proof                        true
% 3.44/1.02  
% 3.44/1.02  ------ Resolution Options
% 3.44/1.02  
% 3.44/1.02  --resolution_flag                       false
% 3.44/1.02  --res_lit_sel                           adaptive
% 3.44/1.02  --res_lit_sel_side                      none
% 3.44/1.02  --res_ordering                          kbo
% 3.44/1.02  --res_to_prop_solver                    active
% 3.44/1.02  --res_prop_simpl_new                    false
% 3.44/1.02  --res_prop_simpl_given                  true
% 3.44/1.02  --res_passive_queue_type                priority_queues
% 3.44/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.44/1.02  --res_passive_queues_freq               [15;5]
% 3.44/1.02  --res_forward_subs                      full
% 3.44/1.02  --res_backward_subs                     full
% 3.44/1.02  --res_forward_subs_resolution           true
% 3.44/1.02  --res_backward_subs_resolution          true
% 3.44/1.02  --res_orphan_elimination                true
% 3.44/1.02  --res_time_limit                        2.
% 3.44/1.02  --res_out_proof                         true
% 3.44/1.02  
% 3.44/1.02  ------ Superposition Options
% 3.44/1.02  
% 3.44/1.02  --superposition_flag                    true
% 3.44/1.02  --sup_passive_queue_type                priority_queues
% 3.44/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.44/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.44/1.02  --demod_completeness_check              fast
% 3.44/1.02  --demod_use_ground                      true
% 3.44/1.02  --sup_to_prop_solver                    passive
% 3.44/1.02  --sup_prop_simpl_new                    true
% 3.44/1.02  --sup_prop_simpl_given                  true
% 3.44/1.02  --sup_fun_splitting                     false
% 3.44/1.02  --sup_smt_interval                      50000
% 3.44/1.02  
% 3.44/1.02  ------ Superposition Simplification Setup
% 3.44/1.02  
% 3.44/1.02  --sup_indices_passive                   []
% 3.44/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.44/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.44/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.02  --sup_full_bw                           [BwDemod]
% 3.44/1.02  --sup_immed_triv                        [TrivRules]
% 3.44/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.44/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.02  --sup_immed_bw_main                     []
% 3.44/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.44/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.44/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.44/1.02  
% 3.44/1.02  ------ Combination Options
% 3.44/1.02  
% 3.44/1.02  --comb_res_mult                         3
% 3.44/1.02  --comb_sup_mult                         2
% 3.44/1.02  --comb_inst_mult                        10
% 3.44/1.02  
% 3.44/1.02  ------ Debug Options
% 3.44/1.02  
% 3.44/1.02  --dbg_backtrace                         false
% 3.44/1.02  --dbg_dump_prop_clauses                 false
% 3.44/1.02  --dbg_dump_prop_clauses_file            -
% 3.44/1.02  --dbg_out_stat                          false
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  ------ Proving...
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  % SZS status Theorem for theBenchmark.p
% 3.44/1.02  
% 3.44/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.44/1.02  
% 3.44/1.02  fof(f18,conjecture,(
% 3.44/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f19,negated_conjecture,(
% 3.44/1.02    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.44/1.02    inference(negated_conjecture,[],[f18])).
% 3.44/1.02  
% 3.44/1.02  fof(f42,plain,(
% 3.44/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.44/1.02    inference(ennf_transformation,[],[f19])).
% 3.44/1.02  
% 3.44/1.02  fof(f43,plain,(
% 3.44/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.44/1.02    inference(flattening,[],[f42])).
% 3.44/1.02  
% 3.44/1.02  fof(f57,plain,(
% 3.44/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK7)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK7) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK7,X1))) )),
% 3.44/1.02    introduced(choice_axiom,[])).
% 3.44/1.02  
% 3.44/1.02  fof(f56,plain,(
% 3.44/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK6,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK6),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK6)) & m1_subset_1(X5,X1)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK6))) )),
% 3.44/1.02    introduced(choice_axiom,[])).
% 3.44/1.02  
% 3.44/1.02  fof(f55,plain,(
% 3.44/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK5,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK5,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK5),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.44/1.02    introduced(choice_axiom,[])).
% 3.44/1.02  
% 3.44/1.02  fof(f54,plain,(
% 3.44/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK2,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,X3,X4),X5) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,X3),k1_relset_1(sK4,sK2,X4)) & m1_subset_1(X5,sK3)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & ~v1_xboole_0(sK4))),
% 3.44/1.02    introduced(choice_axiom,[])).
% 3.44/1.02  
% 3.44/1.02  fof(f58,plain,(
% 3.44/1.02    (((k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) & k1_xboole_0 != sK3 & r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) & m1_subset_1(sK7,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 3.44/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f43,f57,f56,f55,f54])).
% 3.44/1.02  
% 3.44/1.02  fof(f94,plain,(
% 3.44/1.02    m1_subset_1(sK7,sK3)),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f5,axiom,(
% 3.44/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f22,plain,(
% 3.44/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.44/1.02    inference(ennf_transformation,[],[f5])).
% 3.44/1.02  
% 3.44/1.02  fof(f23,plain,(
% 3.44/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.44/1.02    inference(flattening,[],[f22])).
% 3.44/1.02  
% 3.44/1.02  fof(f68,plain,(
% 3.44/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f23])).
% 3.44/1.02  
% 3.44/1.02  fof(f96,plain,(
% 3.44/1.02    k1_xboole_0 != sK3),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f4,axiom,(
% 3.44/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f67,plain,(
% 3.44/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f4])).
% 3.44/1.02  
% 3.44/1.02  fof(f3,axiom,(
% 3.44/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f52,plain,(
% 3.44/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.44/1.02    inference(nnf_transformation,[],[f3])).
% 3.44/1.02  
% 3.44/1.02  fof(f53,plain,(
% 3.44/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.44/1.02    inference(flattening,[],[f52])).
% 3.44/1.02  
% 3.44/1.02  fof(f66,plain,(
% 3.44/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f53])).
% 3.44/1.02  
% 3.44/1.02  fof(f2,axiom,(
% 3.44/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f21,plain,(
% 3.44/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.44/1.02    inference(ennf_transformation,[],[f2])).
% 3.44/1.02  
% 3.44/1.02  fof(f48,plain,(
% 3.44/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/1.02    inference(nnf_transformation,[],[f21])).
% 3.44/1.02  
% 3.44/1.02  fof(f49,plain,(
% 3.44/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/1.02    inference(rectify,[],[f48])).
% 3.44/1.02  
% 3.44/1.02  fof(f50,plain,(
% 3.44/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.44/1.02    introduced(choice_axiom,[])).
% 3.44/1.02  
% 3.44/1.02  fof(f51,plain,(
% 3.44/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.44/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f49,f50])).
% 3.44/1.02  
% 3.44/1.02  fof(f62,plain,(
% 3.44/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f51])).
% 3.44/1.02  
% 3.44/1.02  fof(f1,axiom,(
% 3.44/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f44,plain,(
% 3.44/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.44/1.02    inference(nnf_transformation,[],[f1])).
% 3.44/1.02  
% 3.44/1.02  fof(f45,plain,(
% 3.44/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.44/1.02    inference(rectify,[],[f44])).
% 3.44/1.02  
% 3.44/1.02  fof(f46,plain,(
% 3.44/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.44/1.02    introduced(choice_axiom,[])).
% 3.44/1.02  
% 3.44/1.02  fof(f47,plain,(
% 3.44/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.44/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f46])).
% 3.44/1.02  
% 3.44/1.02  fof(f59,plain,(
% 3.44/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f47])).
% 3.44/1.02  
% 3.44/1.02  fof(f91,plain,(
% 3.44/1.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f17,axiom,(
% 3.44/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f40,plain,(
% 3.44/1.02    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.44/1.02    inference(ennf_transformation,[],[f17])).
% 3.44/1.02  
% 3.44/1.02  fof(f41,plain,(
% 3.44/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.44/1.02    inference(flattening,[],[f40])).
% 3.44/1.02  
% 3.44/1.02  fof(f86,plain,(
% 3.44/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f41])).
% 3.44/1.02  
% 3.44/1.02  fof(f12,axiom,(
% 3.44/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f31,plain,(
% 3.44/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.02    inference(ennf_transformation,[],[f12])).
% 3.44/1.02  
% 3.44/1.02  fof(f75,plain,(
% 3.44/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.02    inference(cnf_transformation,[],[f31])).
% 3.44/1.02  
% 3.44/1.02  fof(f88,plain,(
% 3.44/1.02    ~v1_xboole_0(sK4)),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f89,plain,(
% 3.44/1.02    v1_funct_1(sK5)),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f90,plain,(
% 3.44/1.02    v1_funct_2(sK5,sK3,sK4)),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f60,plain,(
% 3.44/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f47])).
% 3.44/1.02  
% 3.44/1.02  fof(f8,axiom,(
% 3.44/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f27,plain,(
% 3.44/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.44/1.02    inference(ennf_transformation,[],[f8])).
% 3.44/1.02  
% 3.44/1.02  fof(f71,plain,(
% 3.44/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f27])).
% 3.44/1.02  
% 3.44/1.02  fof(f16,axiom,(
% 3.44/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f38,plain,(
% 3.44/1.02    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.44/1.02    inference(ennf_transformation,[],[f16])).
% 3.44/1.02  
% 3.44/1.02  fof(f39,plain,(
% 3.44/1.02    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.44/1.02    inference(flattening,[],[f38])).
% 3.44/1.02  
% 3.44/1.02  fof(f81,plain,(
% 3.44/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f39])).
% 3.44/1.02  
% 3.44/1.02  fof(f84,plain,(
% 3.44/1.02    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f41])).
% 3.44/1.02  
% 3.44/1.02  fof(f93,plain,(
% 3.44/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f10,axiom,(
% 3.44/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f20,plain,(
% 3.44/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.44/1.02    inference(pure_predicate_removal,[],[f10])).
% 3.44/1.02  
% 3.44/1.02  fof(f29,plain,(
% 3.44/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.02    inference(ennf_transformation,[],[f20])).
% 3.44/1.02  
% 3.44/1.02  fof(f73,plain,(
% 3.44/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.02    inference(cnf_transformation,[],[f29])).
% 3.44/1.02  
% 3.44/1.02  fof(f14,axiom,(
% 3.44/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f34,plain,(
% 3.44/1.02    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.44/1.02    inference(ennf_transformation,[],[f14])).
% 3.44/1.02  
% 3.44/1.02  fof(f35,plain,(
% 3.44/1.02    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.44/1.02    inference(flattening,[],[f34])).
% 3.44/1.02  
% 3.44/1.02  fof(f79,plain,(
% 3.44/1.02    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f35])).
% 3.44/1.02  
% 3.44/1.02  fof(f9,axiom,(
% 3.44/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f28,plain,(
% 3.44/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.02    inference(ennf_transformation,[],[f9])).
% 3.44/1.02  
% 3.44/1.02  fof(f72,plain,(
% 3.44/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.02    inference(cnf_transformation,[],[f28])).
% 3.44/1.02  
% 3.44/1.02  fof(f92,plain,(
% 3.44/1.02    v1_funct_1(sK6)),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f11,axiom,(
% 3.44/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f30,plain,(
% 3.44/1.02    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.44/1.02    inference(ennf_transformation,[],[f11])).
% 3.44/1.02  
% 3.44/1.02  fof(f74,plain,(
% 3.44/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.44/1.02    inference(cnf_transformation,[],[f30])).
% 3.44/1.02  
% 3.44/1.02  fof(f95,plain,(
% 3.44/1.02    r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6))),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f15,axiom,(
% 3.44/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f36,plain,(
% 3.44/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.44/1.02    inference(ennf_transformation,[],[f15])).
% 3.44/1.02  
% 3.44/1.02  fof(f37,plain,(
% 3.44/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.44/1.02    inference(flattening,[],[f36])).
% 3.44/1.02  
% 3.44/1.02  fof(f80,plain,(
% 3.44/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f37])).
% 3.44/1.02  
% 3.44/1.02  fof(f97,plain,(
% 3.44/1.02    k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7)),
% 3.44/1.02    inference(cnf_transformation,[],[f58])).
% 3.44/1.02  
% 3.44/1.02  fof(f61,plain,(
% 3.44/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f51])).
% 3.44/1.02  
% 3.44/1.02  fof(f6,axiom,(
% 3.44/1.02    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f24,plain,(
% 3.44/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.44/1.02    inference(ennf_transformation,[],[f6])).
% 3.44/1.02  
% 3.44/1.02  fof(f25,plain,(
% 3.44/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.44/1.02    inference(flattening,[],[f24])).
% 3.44/1.02  
% 3.44/1.02  fof(f69,plain,(
% 3.44/1.02    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f25])).
% 3.44/1.02  
% 3.44/1.02  fof(f13,axiom,(
% 3.44/1.02    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f32,plain,(
% 3.44/1.02    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.44/1.02    inference(ennf_transformation,[],[f13])).
% 3.44/1.02  
% 3.44/1.02  fof(f33,plain,(
% 3.44/1.02    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.44/1.02    inference(flattening,[],[f32])).
% 3.44/1.02  
% 3.44/1.02  fof(f77,plain,(
% 3.44/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f33])).
% 3.44/1.02  
% 3.44/1.02  fof(f7,axiom,(
% 3.44/1.02    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 3.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.44/1.02  
% 3.44/1.02  fof(f26,plain,(
% 3.44/1.02    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 3.44/1.02    inference(ennf_transformation,[],[f7])).
% 3.44/1.02  
% 3.44/1.02  fof(f70,plain,(
% 3.44/1.02    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.44/1.02    inference(cnf_transformation,[],[f26])).
% 3.44/1.02  
% 3.44/1.02  cnf(c_32,negated_conjecture,
% 3.44/1.02      ( m1_subset_1(sK7,sK3) ),
% 3.44/1.02      inference(cnf_transformation,[],[f94]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1175,plain,
% 3.44/1.02      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_9,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.44/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1187,plain,
% 3.44/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.44/1.02      | r2_hidden(X0,X1) = iProver_top
% 3.44/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2935,plain,
% 3.44/1.02      ( r2_hidden(sK7,sK3) = iProver_top
% 3.44/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1175,c_1187]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_45,plain,
% 3.44/1.02      ( m1_subset_1(sK7,sK3) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_30,negated_conjecture,
% 3.44/1.02      ( k1_xboole_0 != sK3 ),
% 3.44/1.02      inference(cnf_transformation,[],[f96]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_8,plain,
% 3.44/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_90,plain,
% 3.44/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5,plain,
% 3.44/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.44/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_95,plain,
% 3.44/1.02      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.44/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_623,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1468,plain,
% 3.44/1.02      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_623]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1469,plain,
% 3.44/1.02      ( sK3 != k1_xboole_0
% 3.44/1.02      | k1_xboole_0 = sK3
% 3.44/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_1468]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_3,plain,
% 3.44/1.02      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1560,plain,
% 3.44/1.02      ( r1_tarski(sK3,k1_xboole_0)
% 3.44/1.02      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1564,plain,
% 3.44/1.02      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 3.44/1.02      | r2_hidden(sK1(sK3,k1_xboole_0),sK3) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1560]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1615,plain,
% 3.44/1.02      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_5]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1616,plain,
% 3.44/1.02      ( sK3 = X0
% 3.44/1.02      | r1_tarski(X0,sK3) != iProver_top
% 3.44/1.02      | r1_tarski(sK3,X0) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1618,plain,
% 3.44/1.02      ( sK3 = k1_xboole_0
% 3.44/1.02      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.44/1.02      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_1616]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1804,plain,
% 3.44/1.02      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1805,plain,
% 3.44/1.02      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1804]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2046,plain,
% 3.44/1.02      ( ~ m1_subset_1(sK7,sK3) | r2_hidden(sK7,sK3) | v1_xboole_0(sK3) ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2047,plain,
% 3.44/1.02      ( m1_subset_1(sK7,sK3) != iProver_top
% 3.44/1.02      | r2_hidden(sK7,sK3) = iProver_top
% 3.44/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_2046]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1,plain,
% 3.44/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.44/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2127,plain,
% 3.44/1.02      ( ~ r2_hidden(sK1(sK3,k1_xboole_0),sK3) | ~ v1_xboole_0(sK3) ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2128,plain,
% 3.44/1.02      ( r2_hidden(sK1(sK3,k1_xboole_0),sK3) != iProver_top
% 3.44/1.02      | v1_xboole_0(sK3) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_2127]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_3301,plain,
% 3.44/1.02      ( r2_hidden(sK7,sK3) = iProver_top ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_2935,c_45,c_30,c_90,c_95,c_1469,c_1564,c_1618,c_1805,
% 3.44/1.02                 c_2047,c_2128]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_35,negated_conjecture,
% 3.44/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.44/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1172,plain,
% 3.44/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_24,plain,
% 3.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.44/1.02      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | k1_xboole_0 = X2 ),
% 3.44/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1179,plain,
% 3.44/1.02      ( k1_xboole_0 = X0
% 3.44/1.02      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.44/1.02      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.44/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_4197,plain,
% 3.44/1.02      ( sK4 = k1_xboole_0
% 3.44/1.02      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.44/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.44/1.02      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.44/1.02      | v1_funct_1(sK5) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1172,c_1179]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_16,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1183,plain,
% 3.44/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.44/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2320,plain,
% 3.44/1.02      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1172,c_1183]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_4203,plain,
% 3.44/1.02      ( sK4 = k1_xboole_0
% 3.44/1.02      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.44/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.44/1.02      | v1_funct_1(sK5) != iProver_top ),
% 3.44/1.02      inference(light_normalisation,[status(thm)],[c_4197,c_2320]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_38,negated_conjecture,
% 3.44/1.02      ( ~ v1_xboole_0(sK4) ),
% 3.44/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_39,plain,
% 3.44/1.02      ( v1_xboole_0(sK4) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_37,negated_conjecture,
% 3.44/1.02      ( v1_funct_1(sK5) ),
% 3.44/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_40,plain,
% 3.44/1.02      ( v1_funct_1(sK5) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_36,negated_conjecture,
% 3.44/1.02      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.44/1.02      inference(cnf_transformation,[],[f90]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_41,plain,
% 3.44/1.02      ( v1_funct_2(sK5,sK3,sK4) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_624,plain,
% 3.44/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.44/1.02      theory(equality) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1441,plain,
% 3.44/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_624]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1442,plain,
% 3.44/1.02      ( sK4 != X0
% 3.44/1.02      | v1_xboole_0(X0) != iProver_top
% 3.44/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1441]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1444,plain,
% 3.44/1.02      ( sK4 != k1_xboole_0
% 3.44/1.02      | v1_xboole_0(sK4) = iProver_top
% 3.44/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.44/1.02      inference(instantiation,[status(thm)],[c_1442]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_0,plain,
% 3.44/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1195,plain,
% 3.44/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.44/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1188,plain,
% 3.44/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_12,plain,
% 3.44/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1185,plain,
% 3.44/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.44/1.02      | r2_hidden(X1,X0) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1929,plain,
% 3.44/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1188,c_1185]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2146,plain,
% 3.44/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1195,c_1929]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5147,plain,
% 3.44/1.02      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.44/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_4203,c_39,c_40,c_41,c_1444,c_2146]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5148,plain,
% 3.44/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_5147]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_22,plain,
% 3.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ r2_hidden(X3,X1)
% 3.44/1.02      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | k1_xboole_0 = X2 ),
% 3.44/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1181,plain,
% 3.44/1.02      ( k1_xboole_0 = X0
% 3.44/1.02      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.44/1.02      | r2_hidden(X3,X2) != iProver_top
% 3.44/1.02      | r2_hidden(k1_funct_1(X1,X3),X0) = iProver_top
% 3.44/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5159,plain,
% 3.44/1.02      ( k1_xboole_0 = X0
% 3.44/1.02      | v1_funct_2(sK5,sK3,X0) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.44/1.02      | r2_hidden(X1,sK3) != iProver_top
% 3.44/1.02      | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
% 3.44/1.02      | v1_funct_1(sK5) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_5148,c_1181]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_26,plain,
% 3.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.44/1.02      | v1_funct_2(X0,X1,X3)
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ r1_tarski(k2_relset_1(X1,X2,X0),X3)
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | k1_xboole_0 = X2 ),
% 3.44/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1177,plain,
% 3.44/1.02      ( k1_xboole_0 = X0
% 3.44/1.02      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.44/1.02      | v1_funct_2(X1,X2,X3) = iProver_top
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relset_1(X2,X0,X1),X3) != iProver_top
% 3.44/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_3874,plain,
% 3.44/1.02      ( sK4 = k1_xboole_0
% 3.44/1.02      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.44/1.02      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.44/1.02      | v1_funct_1(sK5) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1172,c_1177]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_3880,plain,
% 3.44/1.02      ( sK4 = k1_xboole_0
% 3.44/1.02      | v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.44/1.02      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.44/1.02      | v1_funct_1(sK5) != iProver_top ),
% 3.44/1.02      inference(light_normalisation,[status(thm)],[c_3874,c_2320]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_4919,plain,
% 3.44/1.02      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.44/1.02      | v1_funct_2(sK5,sK3,X0) = iProver_top ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_3880,c_39,c_40,c_41,c_1444,c_2146]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_4920,plain,
% 3.44/1.02      ( v1_funct_2(sK5,sK3,X0) = iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_4919]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_10829,plain,
% 3.44/1.02      ( r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top
% 3.44/1.02      | r2_hidden(X1,sK3) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.44/1.02      | k1_xboole_0 = X0 ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_5159,c_39,c_40,c_41,c_1444,c_2146,c_3880]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_10830,plain,
% 3.44/1.02      ( k1_xboole_0 = X0
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.44/1.02      | r2_hidden(X1,sK3) != iProver_top
% 3.44/1.02      | r2_hidden(k1_funct_1(sK5,X1),X0) = iProver_top ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_10829]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_33,negated_conjecture,
% 3.44/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.44/1.02      inference(cnf_transformation,[],[f93]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1174,plain,
% 3.44/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_14,plain,
% 3.44/1.02      ( v5_relat_1(X0,X1)
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.44/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_20,plain,
% 3.44/1.02      ( ~ v5_relat_1(X0,X1)
% 3.44/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | ~ v1_relat_1(X0)
% 3.44/1.02      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.44/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_371,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | ~ v1_relat_1(X0)
% 3.44/1.02      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.44/1.02      inference(resolution,[status(thm)],[c_14,c_20]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_13,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | v1_relat_1(X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_375,plain,
% 3.44/1.02      ( ~ v1_funct_1(X0)
% 3.44/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_371,c_13]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_376,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_375]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1167,plain,
% 3.44/1.02      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 3.44/1.02      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.44/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2062,plain,
% 3.44/1.02      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.44/1.02      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.44/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1174,c_1167]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_34,negated_conjecture,
% 3.44/1.02      ( v1_funct_1(sK6) ),
% 3.44/1.02      inference(cnf_transformation,[],[f92]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_43,plain,
% 3.44/1.02      ( v1_funct_1(sK6) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2558,plain,
% 3.44/1.02      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.44/1.02      | k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0) ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_2062,c_43]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2559,plain,
% 3.44/1.02      ( k7_partfun1(sK2,sK6,X0) = k1_funct_1(sK6,X0)
% 3.44/1.02      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_2558]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_10841,plain,
% 3.44/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.44/1.02      | k1_relat_1(sK6) = k1_xboole_0
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
% 3.44/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_10830,c_2559]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_15,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1184,plain,
% 3.44/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.44/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2820,plain,
% 3.44/1.02      ( k1_relset_1(sK4,sK2,sK6) = k1_relat_1(sK6) ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1174,c_1184]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_31,negated_conjecture,
% 3.44/1.02      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) ),
% 3.44/1.02      inference(cnf_transformation,[],[f95]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1176,plain,
% 3.44/1.02      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2425,plain,
% 3.44/1.02      ( r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,sK2,sK6)) = iProver_top ),
% 3.44/1.02      inference(demodulation,[status(thm)],[c_2320,c_1176]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_3155,plain,
% 3.44/1.02      ( r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) = iProver_top ),
% 3.44/1.02      inference(demodulation,[status(thm)],[c_2820,c_2425]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_11033,plain,
% 3.44/1.02      ( k1_relat_1(sK6) = k1_xboole_0
% 3.44/1.02      | k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.44/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_10841,c_3155]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_11034,plain,
% 3.44/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,X0)) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.44/1.02      | k1_relat_1(sK6) = k1_xboole_0
% 3.44/1.02      | r2_hidden(X0,sK3) != iProver_top ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_11033]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_11044,plain,
% 3.44/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
% 3.44/1.02      | k1_relat_1(sK6) = k1_xboole_0 ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_3301,c_11034]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_21,plain,
% 3.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.44/1.02      | ~ m1_subset_1(X3,X1)
% 3.44/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.44/1.02      | ~ v1_funct_1(X4)
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | v1_xboole_0(X2)
% 3.44/1.02      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.44/1.02      | k1_xboole_0 = X1 ),
% 3.44/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1182,plain,
% 3.44/1.02      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.44/1.02      | k1_xboole_0 = X0
% 3.44/1.02      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.44/1.02      | m1_subset_1(X5,X0) != iProver_top
% 3.44/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.44/1.02      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.44/1.02      | v1_funct_1(X3) != iProver_top
% 3.44/1.02      | v1_funct_1(X4) != iProver_top
% 3.44/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_4435,plain,
% 3.44/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 3.44/1.02      | sK3 = k1_xboole_0
% 3.44/1.02      | v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.44/1.02      | m1_subset_1(X2,sK3) != iProver_top
% 3.44/1.02      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.44/1.02      | v1_funct_1(X1) != iProver_top
% 3.44/1.02      | v1_funct_1(sK5) != iProver_top
% 3.44/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_2320,c_1182]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_42,plain,
% 3.44/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5461,plain,
% 3.44/1.02      ( m1_subset_1(X2,sK3) != iProver_top
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.44/1.02      | k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.44/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_4435,c_39,c_40,c_41,c_42,c_30,c_90,c_95,c_1469]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5462,plain,
% 3.44/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,X0,sK5,X1),X2) = k1_funct_1(X1,k1_funct_1(sK5,X2))
% 3.44/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) != iProver_top
% 3.44/1.02      | m1_subset_1(X2,sK3) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),k1_relset_1(sK4,X0,X1)) != iProver_top
% 3.44/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_5461]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5472,plain,
% 3.44/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.44/1.02      | m1_subset_1(X0,sK3) != iProver_top
% 3.44/1.02      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.44/1.02      | r1_tarski(k2_relat_1(sK5),k1_relat_1(sK6)) != iProver_top
% 3.44/1.02      | v1_funct_1(sK6) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_2820,c_5462]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_44,plain,
% 3.44/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_6101,plain,
% 3.44/1.02      ( m1_subset_1(X0,sK3) != iProver_top
% 3.44/1.02      | k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0)) ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_5472,c_43,c_44,c_3155]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_6102,plain,
% 3.44/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),X0) = k1_funct_1(sK6,k1_funct_1(sK5,X0))
% 3.44/1.02      | m1_subset_1(X0,sK3) != iProver_top ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_6101]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_6109,plain,
% 3.44/1.02      ( k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1175,c_6102]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_29,negated_conjecture,
% 3.44/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(k8_funct_2(sK3,sK4,sK2,sK5,sK6),sK7) ),
% 3.44/1.02      inference(cnf_transformation,[],[f97]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_6111,plain,
% 3.44/1.02      ( k7_partfun1(sK2,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
% 3.44/1.02      inference(demodulation,[status(thm)],[c_6109,c_29]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_11198,plain,
% 3.44/1.02      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_11044,c_6111]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_4,plain,
% 3.44/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.44/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1191,plain,
% 3.44/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.44/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.44/1.02      | r2_hidden(X2,X1) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_4287,plain,
% 3.44/1.02      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 3.44/1.02      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_3155,c_1191]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5903,plain,
% 3.44/1.02      ( r2_hidden(sK0(k2_relat_1(sK5)),k1_relat_1(sK6)) = iProver_top
% 3.44/1.02      | v1_xboole_0(k2_relat_1(sK5)) = iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1195,c_4287]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_10,plain,
% 3.44/1.02      ( ~ v1_relat_1(X0)
% 3.44/1.02      | v1_xboole_0(X0)
% 3.44/1.02      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 3.44/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_399,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | v1_xboole_0(X0)
% 3.44/1.02      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 3.44/1.02      inference(resolution,[status(thm)],[c_13,c_10]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1166,plain,
% 3.44/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/1.02      | v1_xboole_0(X0) = iProver_top
% 3.44/1.02      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1556,plain,
% 3.44/1.02      ( v1_xboole_0(k2_relat_1(sK5)) != iProver_top
% 3.44/1.02      | v1_xboole_0(sK5) = iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1172,c_1166]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_18,plain,
% 3.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ v1_funct_1(X0)
% 3.44/1.02      | ~ v1_xboole_0(X0)
% 3.44/1.02      | v1_xboole_0(X1)
% 3.44/1.02      | v1_xboole_0(X2) ),
% 3.44/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_11,plain,
% 3.44/1.02      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 3.44/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_196,plain,
% 3.44/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ v1_funct_2(X0,X1,X2)
% 3.44/1.02      | ~ v1_xboole_0(X0)
% 3.44/1.02      | v1_xboole_0(X1)
% 3.44/1.02      | v1_xboole_0(X2) ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_18,c_11]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_197,plain,
% 3.44/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.44/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.44/1.02      | ~ v1_xboole_0(X0)
% 3.44/1.02      | v1_xboole_0(X1)
% 3.44/1.02      | v1_xboole_0(X2) ),
% 3.44/1.02      inference(renaming,[status(thm)],[c_196]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1168,plain,
% 3.44/1.02      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.44/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.44/1.02      | v1_xboole_0(X0) != iProver_top
% 3.44/1.02      | v1_xboole_0(X2) = iProver_top
% 3.44/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_197]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_2798,plain,
% 3.44/1.02      ( v1_funct_2(sK5,sK3,sK4) != iProver_top
% 3.44/1.02      | v1_xboole_0(sK4) = iProver_top
% 3.44/1.02      | v1_xboole_0(sK3) = iProver_top
% 3.44/1.02      | v1_xboole_0(sK5) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_1172,c_1168]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5959,plain,
% 3.44/1.02      ( r2_hidden(sK0(k2_relat_1(sK5)),k1_relat_1(sK6)) = iProver_top ),
% 3.44/1.02      inference(global_propositional_subsumption,
% 3.44/1.02                [status(thm)],
% 3.44/1.02                [c_5903,c_39,c_41,c_30,c_90,c_95,c_1469,c_1556,c_1564,
% 3.44/1.02                 c_1618,c_1805,c_2128,c_2798]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_1194,plain,
% 3.44/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.44/1.02      | v1_xboole_0(X1) != iProver_top ),
% 3.44/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_5964,plain,
% 3.44/1.02      ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
% 3.44/1.02      inference(superposition,[status(thm)],[c_5959,c_1194]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(c_11220,plain,
% 3.44/1.02      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.44/1.02      inference(demodulation,[status(thm)],[c_11198,c_5964]) ).
% 3.44/1.02  
% 3.44/1.02  cnf(contradiction,plain,
% 3.44/1.02      ( $false ),
% 3.44/1.02      inference(minisat,[status(thm)],[c_11220,c_2146]) ).
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.44/1.02  
% 3.44/1.02  ------                               Statistics
% 3.44/1.02  
% 3.44/1.02  ------ General
% 3.44/1.02  
% 3.44/1.02  abstr_ref_over_cycles:                  0
% 3.44/1.02  abstr_ref_under_cycles:                 0
% 3.44/1.02  gc_basic_clause_elim:                   0
% 3.44/1.02  forced_gc_time:                         0
% 3.44/1.02  parsing_time:                           0.015
% 3.44/1.02  unif_index_cands_time:                  0.
% 3.44/1.02  unif_index_add_time:                    0.
% 3.44/1.02  orderings_time:                         0.
% 3.44/1.02  out_proof_time:                         0.02
% 3.44/1.02  total_time:                             0.48
% 3.44/1.02  num_of_symbols:                         57
% 3.44/1.02  num_of_terms:                           10431
% 3.44/1.02  
% 3.44/1.02  ------ Preprocessing
% 3.44/1.02  
% 3.44/1.02  num_of_splits:                          0
% 3.44/1.02  num_of_split_atoms:                     0
% 3.44/1.02  num_of_reused_defs:                     0
% 3.44/1.02  num_eq_ax_congr_red:                    18
% 3.44/1.02  num_of_sem_filtered_clauses:            1
% 3.44/1.02  num_of_subtypes:                        0
% 3.44/1.02  monotx_restored_types:                  0
% 3.44/1.02  sat_num_of_epr_types:                   0
% 3.44/1.02  sat_num_of_non_cyclic_types:            0
% 3.44/1.02  sat_guarded_non_collapsed_types:        0
% 3.44/1.02  num_pure_diseq_elim:                    0
% 3.44/1.02  simp_replaced_by:                       0
% 3.44/1.02  res_preprocessed:                       161
% 3.44/1.02  prep_upred:                             0
% 3.44/1.02  prep_unflattend:                        0
% 3.44/1.02  smt_new_axioms:                         0
% 3.44/1.02  pred_elim_cands:                        6
% 3.44/1.02  pred_elim:                              2
% 3.44/1.02  pred_elim_cl:                           2
% 3.44/1.02  pred_elim_cycles:                       4
% 3.44/1.02  merged_defs:                            0
% 3.44/1.02  merged_defs_ncl:                        0
% 3.44/1.02  bin_hyper_res:                          0
% 3.44/1.02  prep_cycles:                            4
% 3.44/1.02  pred_elim_time:                         0.003
% 3.44/1.02  splitting_time:                         0.
% 3.44/1.02  sem_filter_time:                        0.
% 3.44/1.02  monotx_time:                            0.
% 3.44/1.02  subtype_inf_time:                       0.
% 3.44/1.02  
% 3.44/1.02  ------ Problem properties
% 3.44/1.02  
% 3.44/1.02  clauses:                                32
% 3.44/1.02  conjectures:                            10
% 3.44/1.02  epr:                                    14
% 3.44/1.02  horn:                                   24
% 3.44/1.02  ground:                                 10
% 3.44/1.02  unary:                                  12
% 3.44/1.02  binary:                                 8
% 3.44/1.02  lits:                                   87
% 3.44/1.02  lits_eq:                                11
% 3.44/1.02  fd_pure:                                0
% 3.44/1.02  fd_pseudo:                              0
% 3.44/1.02  fd_cond:                                4
% 3.44/1.02  fd_pseudo_cond:                         1
% 3.44/1.02  ac_symbols:                             0
% 3.44/1.02  
% 3.44/1.02  ------ Propositional Solver
% 3.44/1.02  
% 3.44/1.02  prop_solver_calls:                      28
% 3.44/1.02  prop_fast_solver_calls:                 1417
% 3.44/1.02  smt_solver_calls:                       0
% 3.44/1.02  smt_fast_solver_calls:                  0
% 3.44/1.02  prop_num_of_clauses:                    4376
% 3.44/1.02  prop_preprocess_simplified:             10713
% 3.44/1.02  prop_fo_subsumed:                       54
% 3.44/1.02  prop_solver_time:                       0.
% 3.44/1.02  smt_solver_time:                        0.
% 3.44/1.02  smt_fast_solver_time:                   0.
% 3.44/1.02  prop_fast_solver_time:                  0.
% 3.44/1.02  prop_unsat_core_time:                   0.
% 3.44/1.02  
% 3.44/1.02  ------ QBF
% 3.44/1.02  
% 3.44/1.02  qbf_q_res:                              0
% 3.44/1.02  qbf_num_tautologies:                    0
% 3.44/1.02  qbf_prep_cycles:                        0
% 3.44/1.02  
% 3.44/1.02  ------ BMC1
% 3.44/1.02  
% 3.44/1.02  bmc1_current_bound:                     -1
% 3.44/1.02  bmc1_last_solved_bound:                 -1
% 3.44/1.02  bmc1_unsat_core_size:                   -1
% 3.44/1.02  bmc1_unsat_core_parents_size:           -1
% 3.44/1.02  bmc1_merge_next_fun:                    0
% 3.44/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.44/1.02  
% 3.44/1.02  ------ Instantiation
% 3.44/1.02  
% 3.44/1.02  inst_num_of_clauses:                    1393
% 3.44/1.02  inst_num_in_passive:                    173
% 3.44/1.02  inst_num_in_active:                     626
% 3.44/1.02  inst_num_in_unprocessed:                596
% 3.44/1.02  inst_num_of_loops:                      730
% 3.44/1.02  inst_num_of_learning_restarts:          0
% 3.44/1.02  inst_num_moves_active_passive:          102
% 3.44/1.02  inst_lit_activity:                      0
% 3.44/1.02  inst_lit_activity_moves:                0
% 3.44/1.02  inst_num_tautologies:                   0
% 3.44/1.02  inst_num_prop_implied:                  0
% 3.44/1.02  inst_num_existing_simplified:           0
% 3.44/1.02  inst_num_eq_res_simplified:             0
% 3.44/1.02  inst_num_child_elim:                    0
% 3.44/1.02  inst_num_of_dismatching_blockings:      263
% 3.44/1.02  inst_num_of_non_proper_insts:           1063
% 3.44/1.02  inst_num_of_duplicates:                 0
% 3.44/1.02  inst_inst_num_from_inst_to_res:         0
% 3.44/1.02  inst_dismatching_checking_time:         0.
% 3.44/1.02  
% 3.44/1.02  ------ Resolution
% 3.44/1.02  
% 3.44/1.02  res_num_of_clauses:                     0
% 3.44/1.02  res_num_in_passive:                     0
% 3.44/1.02  res_num_in_active:                      0
% 3.44/1.02  res_num_of_loops:                       165
% 3.44/1.02  res_forward_subset_subsumed:            128
% 3.44/1.02  res_backward_subset_subsumed:           12
% 3.44/1.02  res_forward_subsumed:                   0
% 3.44/1.02  res_backward_subsumed:                  0
% 3.44/1.02  res_forward_subsumption_resolution:     0
% 3.44/1.02  res_backward_subsumption_resolution:    0
% 3.44/1.02  res_clause_to_clause_subsumption:       810
% 3.44/1.02  res_orphan_elimination:                 0
% 3.44/1.02  res_tautology_del:                      75
% 3.44/1.02  res_num_eq_res_simplified:              0
% 3.44/1.02  res_num_sel_changes:                    0
% 3.44/1.02  res_moves_from_active_to_pass:          0
% 3.44/1.02  
% 3.44/1.02  ------ Superposition
% 3.44/1.02  
% 3.44/1.02  sup_time_total:                         0.
% 3.44/1.02  sup_time_generating:                    0.
% 3.44/1.02  sup_time_sim_full:                      0.
% 3.44/1.02  sup_time_sim_immed:                     0.
% 3.44/1.02  
% 3.44/1.02  sup_num_of_clauses:                     210
% 3.44/1.02  sup_num_in_active:                      106
% 3.44/1.02  sup_num_in_passive:                     104
% 3.44/1.02  sup_num_of_loops:                       144
% 3.44/1.02  sup_fw_superposition:                   143
% 3.44/1.02  sup_bw_superposition:                   124
% 3.44/1.02  sup_immediate_simplified:               38
% 3.44/1.02  sup_given_eliminated:                   0
% 3.44/1.02  comparisons_done:                       0
% 3.44/1.02  comparisons_avoided:                    87
% 3.44/1.02  
% 3.44/1.02  ------ Simplifications
% 3.44/1.02  
% 3.44/1.02  
% 3.44/1.02  sim_fw_subset_subsumed:                 23
% 3.44/1.02  sim_bw_subset_subsumed:                 3
% 3.44/1.02  sim_fw_subsumed:                        9
% 3.44/1.02  sim_bw_subsumed:                        0
% 3.44/1.02  sim_fw_subsumption_res:                 0
% 3.44/1.02  sim_bw_subsumption_res:                 0
% 3.44/1.02  sim_tautology_del:                      4
% 3.44/1.02  sim_eq_tautology_del:                   21
% 3.44/1.02  sim_eq_res_simp:                        0
% 3.44/1.02  sim_fw_demodulated:                     1
% 3.44/1.02  sim_bw_demodulated:                     36
% 3.44/1.02  sim_light_normalised:                   12
% 3.44/1.02  sim_joinable_taut:                      0
% 3.44/1.02  sim_joinable_simp:                      0
% 3.44/1.02  sim_ac_normalised:                      0
% 3.44/1.02  sim_smt_subsumption:                    0
% 3.44/1.02  
%------------------------------------------------------------------------------
