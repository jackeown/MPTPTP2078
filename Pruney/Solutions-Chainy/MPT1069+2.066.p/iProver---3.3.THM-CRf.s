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
% DateTime   : Thu Dec  3 12:09:55 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 437 expanded)
%              Number of clauses        :   99 ( 127 expanded)
%              Number of leaves         :   22 ( 143 expanded)
%              Depth                    :   19
%              Number of atoms          :  553 (3136 expanded)
%              Number of equality atoms :  173 ( 785 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
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
            ( k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
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
                ( k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
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
                  ( k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5)
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

fof(f45,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f44,f43,f42,f41])).

fof(f69,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1999,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2007,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3517,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1999,c_2007])).

cnf(c_33,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2219,plain,
    ( ~ m1_subset_1(sK6,sK2)
    | r2_hidden(sK6,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2220,plain,
    ( m1_subset_1(sK6,sK2) != iProver_top
    | r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2219])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2333,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2334,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2333])).

cnf(c_3847,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3517,c_33,c_18,c_2220,c_2334])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1997,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2001,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3379,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1997,c_2001])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK3 != X2
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_369,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(X0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_25,c_23])).

cnf(c_370,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_369])).

cnf(c_1993,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_3656,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3379,c_1993])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2000,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3659,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3379,c_2000])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1998,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2002,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3499,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1998,c_2002])).

cnf(c_3763,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3659,c_3499])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_190,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_190])).

cnf(c_1995,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_3766,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3763,c_1995])).

cnf(c_5215,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3656,c_3766])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2203,plain,
    ( ~ r1_tarski(k1_xboole_0,X0)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2416,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
    | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2203])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2417,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3166,plain,
    ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1401,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4740,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_4743,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4740])).

cnf(c_5379,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5215,c_26,c_2416,c_2417,c_3166,c_4743])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2005,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2883,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1998,c_2005])).

cnf(c_2006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_22])).

cnf(c_523,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k7_partfun1(X1,sK5,X2) = k1_funct_1(sK5,X2) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_1991,plain,
    ( k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_2895,plain,
    ( k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1)
    | r1_tarski(sK5,k2_zfmisc_1(X2,X0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_1991])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2193,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2194,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2193])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_245,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_190])).

cnf(c_2209,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_2569,plain,
    ( ~ r1_tarski(sK5,k2_zfmisc_1(sK3,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_2570,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2569])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2642,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2643,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2642])).

cnf(c_4424,plain,
    ( r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | r1_tarski(sK5,k2_zfmisc_1(X2,X0)) != iProver_top
    | k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2895,c_32,c_2194,c_2570,c_2643])).

cnf(c_4425,plain,
    ( k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1)
    | r1_tarski(sK5,k2_zfmisc_1(X2,X0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4424])).

cnf(c_4433,plain,
    ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_4425])).

cnf(c_5388,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5379,c_4433])).

cnf(c_5407,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_3847,c_5388])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X4)
    | v1_xboole_0(X3)
    | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
    | sK3 != X3
    | sK2 != X1
    | sK4 != X2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK3)
    | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2))
    | ~ v1_funct_1(X0)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_26,c_25,c_23,c_18])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
    | ~ v1_funct_1(X0)
    | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2)) ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ m1_subset_1(X2,sK2)
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
    | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_391,c_22])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,sK5))
    | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_1992,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,sK5),X1) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | m1_subset_1(X1,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_2605,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2000,c_1992])).

cnf(c_2610,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2605,c_32])).

cnf(c_2611,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2610])).

cnf(c_2618,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_1999,c_2611])).

cnf(c_17,negated_conjecture,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2659,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(demodulation,[status(thm)],[c_2618,c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5407,c_2659])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.43/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.00  
% 2.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/1.00  
% 2.43/1.00  ------  iProver source info
% 2.43/1.00  
% 2.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/1.00  git: non_committed_changes: false
% 2.43/1.00  git: last_make_outside_of_git: false
% 2.43/1.00  
% 2.43/1.00  ------ 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options
% 2.43/1.00  
% 2.43/1.00  --out_options                           all
% 2.43/1.00  --tptp_safe_out                         true
% 2.43/1.00  --problem_path                          ""
% 2.43/1.00  --include_path                          ""
% 2.43/1.00  --clausifier                            res/vclausify_rel
% 2.43/1.00  --clausifier_options                    --mode clausify
% 2.43/1.00  --stdin                                 false
% 2.43/1.00  --stats_out                             all
% 2.43/1.00  
% 2.43/1.00  ------ General Options
% 2.43/1.00  
% 2.43/1.00  --fof                                   false
% 2.43/1.00  --time_out_real                         305.
% 2.43/1.00  --time_out_virtual                      -1.
% 2.43/1.00  --symbol_type_check                     false
% 2.43/1.00  --clausify_out                          false
% 2.43/1.00  --sig_cnt_out                           false
% 2.43/1.00  --trig_cnt_out                          false
% 2.43/1.00  --trig_cnt_out_tolerance                1.
% 2.43/1.00  --trig_cnt_out_sk_spl                   false
% 2.43/1.00  --abstr_cl_out                          false
% 2.43/1.00  
% 2.43/1.00  ------ Global Options
% 2.43/1.00  
% 2.43/1.00  --schedule                              default
% 2.43/1.00  --add_important_lit                     false
% 2.43/1.00  --prop_solver_per_cl                    1000
% 2.43/1.00  --min_unsat_core                        false
% 2.43/1.00  --soft_assumptions                      false
% 2.43/1.00  --soft_lemma_size                       3
% 2.43/1.00  --prop_impl_unit_size                   0
% 2.43/1.00  --prop_impl_unit                        []
% 2.43/1.00  --share_sel_clauses                     true
% 2.43/1.00  --reset_solvers                         false
% 2.43/1.00  --bc_imp_inh                            [conj_cone]
% 2.43/1.00  --conj_cone_tolerance                   3.
% 2.43/1.00  --extra_neg_conj                        none
% 2.43/1.00  --large_theory_mode                     true
% 2.43/1.00  --prolific_symb_bound                   200
% 2.43/1.00  --lt_threshold                          2000
% 2.43/1.00  --clause_weak_htbl                      true
% 2.43/1.00  --gc_record_bc_elim                     false
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing Options
% 2.43/1.00  
% 2.43/1.00  --preprocessing_flag                    true
% 2.43/1.00  --time_out_prep_mult                    0.1
% 2.43/1.00  --splitting_mode                        input
% 2.43/1.00  --splitting_grd                         true
% 2.43/1.00  --splitting_cvd                         false
% 2.43/1.00  --splitting_cvd_svl                     false
% 2.43/1.00  --splitting_nvd                         32
% 2.43/1.00  --sub_typing                            true
% 2.43/1.00  --prep_gs_sim                           true
% 2.43/1.00  --prep_unflatten                        true
% 2.43/1.00  --prep_res_sim                          true
% 2.43/1.00  --prep_upred                            true
% 2.43/1.00  --prep_sem_filter                       exhaustive
% 2.43/1.00  --prep_sem_filter_out                   false
% 2.43/1.00  --pred_elim                             true
% 2.43/1.00  --res_sim_input                         true
% 2.43/1.00  --eq_ax_congr_red                       true
% 2.43/1.00  --pure_diseq_elim                       true
% 2.43/1.00  --brand_transform                       false
% 2.43/1.00  --non_eq_to_eq                          false
% 2.43/1.00  --prep_def_merge                        true
% 2.43/1.00  --prep_def_merge_prop_impl              false
% 2.43/1.00  --prep_def_merge_mbd                    true
% 2.43/1.00  --prep_def_merge_tr_red                 false
% 2.43/1.00  --prep_def_merge_tr_cl                  false
% 2.43/1.00  --smt_preprocessing                     true
% 2.43/1.00  --smt_ac_axioms                         fast
% 2.43/1.00  --preprocessed_out                      false
% 2.43/1.00  --preprocessed_stats                    false
% 2.43/1.00  
% 2.43/1.00  ------ Abstraction refinement Options
% 2.43/1.00  
% 2.43/1.00  --abstr_ref                             []
% 2.43/1.00  --abstr_ref_prep                        false
% 2.43/1.00  --abstr_ref_until_sat                   false
% 2.43/1.00  --abstr_ref_sig_restrict                funpre
% 2.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.00  --abstr_ref_under                       []
% 2.43/1.00  
% 2.43/1.00  ------ SAT Options
% 2.43/1.00  
% 2.43/1.00  --sat_mode                              false
% 2.43/1.00  --sat_fm_restart_options                ""
% 2.43/1.00  --sat_gr_def                            false
% 2.43/1.00  --sat_epr_types                         true
% 2.43/1.00  --sat_non_cyclic_types                  false
% 2.43/1.00  --sat_finite_models                     false
% 2.43/1.00  --sat_fm_lemmas                         false
% 2.43/1.00  --sat_fm_prep                           false
% 2.43/1.00  --sat_fm_uc_incr                        true
% 2.43/1.00  --sat_out_model                         small
% 2.43/1.00  --sat_out_clauses                       false
% 2.43/1.00  
% 2.43/1.00  ------ QBF Options
% 2.43/1.00  
% 2.43/1.00  --qbf_mode                              false
% 2.43/1.00  --qbf_elim_univ                         false
% 2.43/1.00  --qbf_dom_inst                          none
% 2.43/1.00  --qbf_dom_pre_inst                      false
% 2.43/1.00  --qbf_sk_in                             false
% 2.43/1.00  --qbf_pred_elim                         true
% 2.43/1.00  --qbf_split                             512
% 2.43/1.00  
% 2.43/1.00  ------ BMC1 Options
% 2.43/1.00  
% 2.43/1.00  --bmc1_incremental                      false
% 2.43/1.00  --bmc1_axioms                           reachable_all
% 2.43/1.00  --bmc1_min_bound                        0
% 2.43/1.00  --bmc1_max_bound                        -1
% 2.43/1.00  --bmc1_max_bound_default                -1
% 2.43/1.00  --bmc1_symbol_reachability              true
% 2.43/1.00  --bmc1_property_lemmas                  false
% 2.43/1.00  --bmc1_k_induction                      false
% 2.43/1.00  --bmc1_non_equiv_states                 false
% 2.43/1.00  --bmc1_deadlock                         false
% 2.43/1.00  --bmc1_ucm                              false
% 2.43/1.00  --bmc1_add_unsat_core                   none
% 2.43/1.00  --bmc1_unsat_core_children              false
% 2.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.00  --bmc1_out_stat                         full
% 2.43/1.00  --bmc1_ground_init                      false
% 2.43/1.00  --bmc1_pre_inst_next_state              false
% 2.43/1.00  --bmc1_pre_inst_state                   false
% 2.43/1.00  --bmc1_pre_inst_reach_state             false
% 2.43/1.00  --bmc1_out_unsat_core                   false
% 2.43/1.00  --bmc1_aig_witness_out                  false
% 2.43/1.00  --bmc1_verbose                          false
% 2.43/1.00  --bmc1_dump_clauses_tptp                false
% 2.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.00  --bmc1_dump_file                        -
% 2.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.00  --bmc1_ucm_extend_mode                  1
% 2.43/1.00  --bmc1_ucm_init_mode                    2
% 2.43/1.00  --bmc1_ucm_cone_mode                    none
% 2.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.00  --bmc1_ucm_relax_model                  4
% 2.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.00  --bmc1_ucm_layered_model                none
% 2.43/1.00  --bmc1_ucm_max_lemma_size               10
% 2.43/1.00  
% 2.43/1.00  ------ AIG Options
% 2.43/1.00  
% 2.43/1.00  --aig_mode                              false
% 2.43/1.00  
% 2.43/1.00  ------ Instantiation Options
% 2.43/1.00  
% 2.43/1.00  --instantiation_flag                    true
% 2.43/1.00  --inst_sos_flag                         false
% 2.43/1.00  --inst_sos_phase                        true
% 2.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel_side                     num_symb
% 2.43/1.00  --inst_solver_per_active                1400
% 2.43/1.00  --inst_solver_calls_frac                1.
% 2.43/1.00  --inst_passive_queue_type               priority_queues
% 2.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.00  --inst_passive_queues_freq              [25;2]
% 2.43/1.00  --inst_dismatching                      true
% 2.43/1.00  --inst_eager_unprocessed_to_passive     true
% 2.43/1.00  --inst_prop_sim_given                   true
% 2.43/1.00  --inst_prop_sim_new                     false
% 2.43/1.00  --inst_subs_new                         false
% 2.43/1.00  --inst_eq_res_simp                      false
% 2.43/1.00  --inst_subs_given                       false
% 2.43/1.00  --inst_orphan_elimination               true
% 2.43/1.00  --inst_learning_loop_flag               true
% 2.43/1.00  --inst_learning_start                   3000
% 2.43/1.00  --inst_learning_factor                  2
% 2.43/1.00  --inst_start_prop_sim_after_learn       3
% 2.43/1.00  --inst_sel_renew                        solver
% 2.43/1.00  --inst_lit_activity_flag                true
% 2.43/1.00  --inst_restr_to_given                   false
% 2.43/1.00  --inst_activity_threshold               500
% 2.43/1.00  --inst_out_proof                        true
% 2.43/1.00  
% 2.43/1.00  ------ Resolution Options
% 2.43/1.00  
% 2.43/1.00  --resolution_flag                       true
% 2.43/1.00  --res_lit_sel                           adaptive
% 2.43/1.00  --res_lit_sel_side                      none
% 2.43/1.00  --res_ordering                          kbo
% 2.43/1.00  --res_to_prop_solver                    active
% 2.43/1.00  --res_prop_simpl_new                    false
% 2.43/1.00  --res_prop_simpl_given                  true
% 2.43/1.00  --res_passive_queue_type                priority_queues
% 2.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.00  --res_passive_queues_freq               [15;5]
% 2.43/1.00  --res_forward_subs                      full
% 2.43/1.00  --res_backward_subs                     full
% 2.43/1.00  --res_forward_subs_resolution           true
% 2.43/1.00  --res_backward_subs_resolution          true
% 2.43/1.00  --res_orphan_elimination                true
% 2.43/1.00  --res_time_limit                        2.
% 2.43/1.00  --res_out_proof                         true
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Options
% 2.43/1.00  
% 2.43/1.00  --superposition_flag                    true
% 2.43/1.00  --sup_passive_queue_type                priority_queues
% 2.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.00  --demod_completeness_check              fast
% 2.43/1.00  --demod_use_ground                      true
% 2.43/1.00  --sup_to_prop_solver                    passive
% 2.43/1.00  --sup_prop_simpl_new                    true
% 2.43/1.00  --sup_prop_simpl_given                  true
% 2.43/1.00  --sup_fun_splitting                     false
% 2.43/1.00  --sup_smt_interval                      50000
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Simplification Setup
% 2.43/1.00  
% 2.43/1.00  --sup_indices_passive                   []
% 2.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_full_bw                           [BwDemod]
% 2.43/1.00  --sup_immed_triv                        [TrivRules]
% 2.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_immed_bw_main                     []
% 2.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  
% 2.43/1.00  ------ Combination Options
% 2.43/1.00  
% 2.43/1.00  --comb_res_mult                         3
% 2.43/1.00  --comb_sup_mult                         2
% 2.43/1.00  --comb_inst_mult                        10
% 2.43/1.00  
% 2.43/1.00  ------ Debug Options
% 2.43/1.00  
% 2.43/1.00  --dbg_backtrace                         false
% 2.43/1.00  --dbg_dump_prop_clauses                 false
% 2.43/1.00  --dbg_dump_prop_clauses_file            -
% 2.43/1.00  --dbg_out_stat                          false
% 2.43/1.00  ------ Parsing...
% 2.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/1.00  ------ Proving...
% 2.43/1.00  ------ Problem Properties 
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  clauses                                 25
% 2.43/1.00  conjectures                             7
% 2.43/1.00  EPR                                     10
% 2.43/1.00  Horn                                    22
% 2.43/1.00  unary                                   9
% 2.43/1.00  binary                                  8
% 2.43/1.00  lits                                    53
% 2.43/1.00  lits eq                                 10
% 2.43/1.00  fd_pure                                 0
% 2.43/1.00  fd_pseudo                               0
% 2.43/1.00  fd_cond                                 1
% 2.43/1.00  fd_pseudo_cond                          0
% 2.43/1.00  AC symbols                              0
% 2.43/1.00  
% 2.43/1.00  ------ Schedule dynamic 5 is on 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  ------ 
% 2.43/1.00  Current options:
% 2.43/1.00  ------ 
% 2.43/1.00  
% 2.43/1.00  ------ Input Options
% 2.43/1.00  
% 2.43/1.00  --out_options                           all
% 2.43/1.00  --tptp_safe_out                         true
% 2.43/1.00  --problem_path                          ""
% 2.43/1.00  --include_path                          ""
% 2.43/1.00  --clausifier                            res/vclausify_rel
% 2.43/1.00  --clausifier_options                    --mode clausify
% 2.43/1.00  --stdin                                 false
% 2.43/1.00  --stats_out                             all
% 2.43/1.00  
% 2.43/1.00  ------ General Options
% 2.43/1.00  
% 2.43/1.00  --fof                                   false
% 2.43/1.00  --time_out_real                         305.
% 2.43/1.00  --time_out_virtual                      -1.
% 2.43/1.00  --symbol_type_check                     false
% 2.43/1.00  --clausify_out                          false
% 2.43/1.00  --sig_cnt_out                           false
% 2.43/1.00  --trig_cnt_out                          false
% 2.43/1.00  --trig_cnt_out_tolerance                1.
% 2.43/1.00  --trig_cnt_out_sk_spl                   false
% 2.43/1.00  --abstr_cl_out                          false
% 2.43/1.00  
% 2.43/1.00  ------ Global Options
% 2.43/1.00  
% 2.43/1.00  --schedule                              default
% 2.43/1.00  --add_important_lit                     false
% 2.43/1.00  --prop_solver_per_cl                    1000
% 2.43/1.00  --min_unsat_core                        false
% 2.43/1.00  --soft_assumptions                      false
% 2.43/1.00  --soft_lemma_size                       3
% 2.43/1.00  --prop_impl_unit_size                   0
% 2.43/1.00  --prop_impl_unit                        []
% 2.43/1.00  --share_sel_clauses                     true
% 2.43/1.00  --reset_solvers                         false
% 2.43/1.00  --bc_imp_inh                            [conj_cone]
% 2.43/1.00  --conj_cone_tolerance                   3.
% 2.43/1.00  --extra_neg_conj                        none
% 2.43/1.00  --large_theory_mode                     true
% 2.43/1.00  --prolific_symb_bound                   200
% 2.43/1.00  --lt_threshold                          2000
% 2.43/1.00  --clause_weak_htbl                      true
% 2.43/1.00  --gc_record_bc_elim                     false
% 2.43/1.00  
% 2.43/1.00  ------ Preprocessing Options
% 2.43/1.00  
% 2.43/1.00  --preprocessing_flag                    true
% 2.43/1.00  --time_out_prep_mult                    0.1
% 2.43/1.00  --splitting_mode                        input
% 2.43/1.00  --splitting_grd                         true
% 2.43/1.00  --splitting_cvd                         false
% 2.43/1.00  --splitting_cvd_svl                     false
% 2.43/1.00  --splitting_nvd                         32
% 2.43/1.00  --sub_typing                            true
% 2.43/1.00  --prep_gs_sim                           true
% 2.43/1.00  --prep_unflatten                        true
% 2.43/1.00  --prep_res_sim                          true
% 2.43/1.00  --prep_upred                            true
% 2.43/1.00  --prep_sem_filter                       exhaustive
% 2.43/1.00  --prep_sem_filter_out                   false
% 2.43/1.00  --pred_elim                             true
% 2.43/1.00  --res_sim_input                         true
% 2.43/1.00  --eq_ax_congr_red                       true
% 2.43/1.00  --pure_diseq_elim                       true
% 2.43/1.00  --brand_transform                       false
% 2.43/1.00  --non_eq_to_eq                          false
% 2.43/1.00  --prep_def_merge                        true
% 2.43/1.00  --prep_def_merge_prop_impl              false
% 2.43/1.00  --prep_def_merge_mbd                    true
% 2.43/1.00  --prep_def_merge_tr_red                 false
% 2.43/1.00  --prep_def_merge_tr_cl                  false
% 2.43/1.00  --smt_preprocessing                     true
% 2.43/1.00  --smt_ac_axioms                         fast
% 2.43/1.00  --preprocessed_out                      false
% 2.43/1.00  --preprocessed_stats                    false
% 2.43/1.00  
% 2.43/1.00  ------ Abstraction refinement Options
% 2.43/1.00  
% 2.43/1.00  --abstr_ref                             []
% 2.43/1.00  --abstr_ref_prep                        false
% 2.43/1.00  --abstr_ref_until_sat                   false
% 2.43/1.00  --abstr_ref_sig_restrict                funpre
% 2.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.00  --abstr_ref_under                       []
% 2.43/1.00  
% 2.43/1.00  ------ SAT Options
% 2.43/1.00  
% 2.43/1.00  --sat_mode                              false
% 2.43/1.00  --sat_fm_restart_options                ""
% 2.43/1.00  --sat_gr_def                            false
% 2.43/1.00  --sat_epr_types                         true
% 2.43/1.00  --sat_non_cyclic_types                  false
% 2.43/1.00  --sat_finite_models                     false
% 2.43/1.00  --sat_fm_lemmas                         false
% 2.43/1.00  --sat_fm_prep                           false
% 2.43/1.00  --sat_fm_uc_incr                        true
% 2.43/1.00  --sat_out_model                         small
% 2.43/1.00  --sat_out_clauses                       false
% 2.43/1.00  
% 2.43/1.00  ------ QBF Options
% 2.43/1.00  
% 2.43/1.00  --qbf_mode                              false
% 2.43/1.00  --qbf_elim_univ                         false
% 2.43/1.00  --qbf_dom_inst                          none
% 2.43/1.00  --qbf_dom_pre_inst                      false
% 2.43/1.00  --qbf_sk_in                             false
% 2.43/1.00  --qbf_pred_elim                         true
% 2.43/1.00  --qbf_split                             512
% 2.43/1.00  
% 2.43/1.00  ------ BMC1 Options
% 2.43/1.00  
% 2.43/1.00  --bmc1_incremental                      false
% 2.43/1.00  --bmc1_axioms                           reachable_all
% 2.43/1.00  --bmc1_min_bound                        0
% 2.43/1.00  --bmc1_max_bound                        -1
% 2.43/1.00  --bmc1_max_bound_default                -1
% 2.43/1.00  --bmc1_symbol_reachability              true
% 2.43/1.00  --bmc1_property_lemmas                  false
% 2.43/1.00  --bmc1_k_induction                      false
% 2.43/1.00  --bmc1_non_equiv_states                 false
% 2.43/1.00  --bmc1_deadlock                         false
% 2.43/1.00  --bmc1_ucm                              false
% 2.43/1.00  --bmc1_add_unsat_core                   none
% 2.43/1.00  --bmc1_unsat_core_children              false
% 2.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.00  --bmc1_out_stat                         full
% 2.43/1.00  --bmc1_ground_init                      false
% 2.43/1.00  --bmc1_pre_inst_next_state              false
% 2.43/1.00  --bmc1_pre_inst_state                   false
% 2.43/1.00  --bmc1_pre_inst_reach_state             false
% 2.43/1.00  --bmc1_out_unsat_core                   false
% 2.43/1.00  --bmc1_aig_witness_out                  false
% 2.43/1.00  --bmc1_verbose                          false
% 2.43/1.00  --bmc1_dump_clauses_tptp                false
% 2.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.00  --bmc1_dump_file                        -
% 2.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.00  --bmc1_ucm_extend_mode                  1
% 2.43/1.00  --bmc1_ucm_init_mode                    2
% 2.43/1.00  --bmc1_ucm_cone_mode                    none
% 2.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.00  --bmc1_ucm_relax_model                  4
% 2.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.00  --bmc1_ucm_layered_model                none
% 2.43/1.00  --bmc1_ucm_max_lemma_size               10
% 2.43/1.00  
% 2.43/1.00  ------ AIG Options
% 2.43/1.00  
% 2.43/1.00  --aig_mode                              false
% 2.43/1.00  
% 2.43/1.00  ------ Instantiation Options
% 2.43/1.00  
% 2.43/1.00  --instantiation_flag                    true
% 2.43/1.00  --inst_sos_flag                         false
% 2.43/1.00  --inst_sos_phase                        true
% 2.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.00  --inst_lit_sel_side                     none
% 2.43/1.00  --inst_solver_per_active                1400
% 2.43/1.00  --inst_solver_calls_frac                1.
% 2.43/1.00  --inst_passive_queue_type               priority_queues
% 2.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.00  --inst_passive_queues_freq              [25;2]
% 2.43/1.00  --inst_dismatching                      true
% 2.43/1.00  --inst_eager_unprocessed_to_passive     true
% 2.43/1.00  --inst_prop_sim_given                   true
% 2.43/1.00  --inst_prop_sim_new                     false
% 2.43/1.00  --inst_subs_new                         false
% 2.43/1.00  --inst_eq_res_simp                      false
% 2.43/1.00  --inst_subs_given                       false
% 2.43/1.00  --inst_orphan_elimination               true
% 2.43/1.00  --inst_learning_loop_flag               true
% 2.43/1.00  --inst_learning_start                   3000
% 2.43/1.00  --inst_learning_factor                  2
% 2.43/1.00  --inst_start_prop_sim_after_learn       3
% 2.43/1.00  --inst_sel_renew                        solver
% 2.43/1.00  --inst_lit_activity_flag                true
% 2.43/1.00  --inst_restr_to_given                   false
% 2.43/1.00  --inst_activity_threshold               500
% 2.43/1.00  --inst_out_proof                        true
% 2.43/1.00  
% 2.43/1.00  ------ Resolution Options
% 2.43/1.00  
% 2.43/1.00  --resolution_flag                       false
% 2.43/1.00  --res_lit_sel                           adaptive
% 2.43/1.00  --res_lit_sel_side                      none
% 2.43/1.00  --res_ordering                          kbo
% 2.43/1.00  --res_to_prop_solver                    active
% 2.43/1.00  --res_prop_simpl_new                    false
% 2.43/1.00  --res_prop_simpl_given                  true
% 2.43/1.00  --res_passive_queue_type                priority_queues
% 2.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.00  --res_passive_queues_freq               [15;5]
% 2.43/1.00  --res_forward_subs                      full
% 2.43/1.00  --res_backward_subs                     full
% 2.43/1.00  --res_forward_subs_resolution           true
% 2.43/1.00  --res_backward_subs_resolution          true
% 2.43/1.00  --res_orphan_elimination                true
% 2.43/1.00  --res_time_limit                        2.
% 2.43/1.00  --res_out_proof                         true
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Options
% 2.43/1.00  
% 2.43/1.00  --superposition_flag                    true
% 2.43/1.00  --sup_passive_queue_type                priority_queues
% 2.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.00  --demod_completeness_check              fast
% 2.43/1.00  --demod_use_ground                      true
% 2.43/1.00  --sup_to_prop_solver                    passive
% 2.43/1.00  --sup_prop_simpl_new                    true
% 2.43/1.00  --sup_prop_simpl_given                  true
% 2.43/1.00  --sup_fun_splitting                     false
% 2.43/1.00  --sup_smt_interval                      50000
% 2.43/1.00  
% 2.43/1.00  ------ Superposition Simplification Setup
% 2.43/1.00  
% 2.43/1.00  --sup_indices_passive                   []
% 2.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_full_bw                           [BwDemod]
% 2.43/1.00  --sup_immed_triv                        [TrivRules]
% 2.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_immed_bw_main                     []
% 2.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.00  
% 2.43/1.00  ------ Combination Options
% 2.43/1.00  
% 2.43/1.00  --comb_res_mult                         3
% 2.43/1.00  --comb_sup_mult                         2
% 2.43/1.00  --comb_inst_mult                        10
% 2.43/1.00  
% 2.43/1.00  ------ Debug Options
% 2.43/1.00  
% 2.43/1.00  --dbg_backtrace                         false
% 2.43/1.00  --dbg_dump_prop_clauses                 false
% 2.43/1.00  --dbg_dump_prop_clauses_file            -
% 2.43/1.00  --dbg_out_stat                          false
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  ------ Proving...
% 2.43/1.00  
% 2.43/1.00  
% 2.43/1.00  % SZS status Theorem for theBenchmark.p
% 2.43/1.00  
% 2.43/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/1.00  
% 2.43/1.00  fof(f16,conjecture,(
% 2.43/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f17,negated_conjecture,(
% 2.43/1.01    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.43/1.01    inference(negated_conjecture,[],[f16])).
% 2.43/1.01  
% 2.43/1.01  fof(f34,plain,(
% 2.43/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.43/1.01    inference(ennf_transformation,[],[f17])).
% 2.43/1.01  
% 2.43/1.01  fof(f35,plain,(
% 2.43/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.43/1.01    inference(flattening,[],[f34])).
% 2.43/1.01  
% 2.43/1.01  fof(f44,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f43,plain,(
% 2.43/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f42,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f41,plain,(
% 2.43/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(X0,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f45,plain,(
% 2.43/1.01    (((k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f35,f44,f43,f42,f41])).
% 2.43/1.01  
% 2.43/1.01  fof(f69,plain,(
% 2.43/1.01    m1_subset_1(sK6,sK2)),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f5,axiom,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f21,plain,(
% 2.43/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.43/1.01    inference(ennf_transformation,[],[f5])).
% 2.43/1.01  
% 2.43/1.01  fof(f22,plain,(
% 2.43/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.43/1.01    inference(flattening,[],[f21])).
% 2.43/1.01  
% 2.43/1.01  fof(f51,plain,(
% 2.43/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f22])).
% 2.43/1.01  
% 2.43/1.01  fof(f71,plain,(
% 2.43/1.01    k1_xboole_0 != sK2),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f2,axiom,(
% 2.43/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f19,plain,(
% 2.43/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f2])).
% 2.43/1.01  
% 2.43/1.01  fof(f48,plain,(
% 2.43/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f19])).
% 2.43/1.01  
% 2.43/1.01  fof(f66,plain,(
% 2.43/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f12,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f27,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/1.01    inference(ennf_transformation,[],[f12])).
% 2.43/1.01  
% 2.43/1.01  fof(f59,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f27])).
% 2.43/1.01  
% 2.43/1.01  fof(f15,axiom,(
% 2.43/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f32,plain,(
% 2.43/1.01    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.43/1.01    inference(ennf_transformation,[],[f15])).
% 2.43/1.01  
% 2.43/1.01  fof(f33,plain,(
% 2.43/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.43/1.01    inference(flattening,[],[f32])).
% 2.43/1.01  
% 2.43/1.01  fof(f62,plain,(
% 2.43/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f33])).
% 2.43/1.01  
% 2.43/1.01  fof(f65,plain,(
% 2.43/1.01    v1_funct_2(sK4,sK2,sK3)),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f64,plain,(
% 2.43/1.01    v1_funct_1(sK4)),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f70,plain,(
% 2.43/1.01    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f68,plain,(
% 2.43/1.01    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f11,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f26,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/1.01    inference(ennf_transformation,[],[f11])).
% 2.43/1.01  
% 2.43/1.01  fof(f58,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f26])).
% 2.43/1.01  
% 2.43/1.01  fof(f4,axiom,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f20,plain,(
% 2.43/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f4])).
% 2.43/1.01  
% 2.43/1.01  fof(f50,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f20])).
% 2.43/1.01  
% 2.43/1.01  fof(f6,axiom,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f40,plain,(
% 2.43/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.43/1.01    inference(nnf_transformation,[],[f6])).
% 2.43/1.01  
% 2.43/1.01  fof(f53,plain,(
% 2.43/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f63,plain,(
% 2.43/1.01    ~v1_xboole_0(sK3)),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f9,axiom,(
% 2.43/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f24,plain,(
% 2.43/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.43/1.01    inference(ennf_transformation,[],[f9])).
% 2.43/1.01  
% 2.43/1.01  fof(f56,plain,(
% 2.43/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f24])).
% 2.43/1.01  
% 2.43/1.01  fof(f1,axiom,(
% 2.43/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f36,plain,(
% 2.43/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.43/1.01    inference(nnf_transformation,[],[f1])).
% 2.43/1.01  
% 2.43/1.01  fof(f37,plain,(
% 2.43/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.43/1.01    inference(rectify,[],[f36])).
% 2.43/1.01  
% 2.43/1.01  fof(f38,plain,(
% 2.43/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f39,plain,(
% 2.43/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.43/1.01  
% 2.43/1.01  fof(f47,plain,(
% 2.43/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f39])).
% 2.43/1.01  
% 2.43/1.01  fof(f3,axiom,(
% 2.43/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f49,plain,(
% 2.43/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f3])).
% 2.43/1.01  
% 2.43/1.01  fof(f52,plain,(
% 2.43/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f10,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f18,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.43/1.01    inference(pure_predicate_removal,[],[f10])).
% 2.43/1.01  
% 2.43/1.01  fof(f25,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.43/1.01    inference(ennf_transformation,[],[f18])).
% 2.43/1.01  
% 2.43/1.01  fof(f57,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f25])).
% 2.43/1.01  
% 2.43/1.01  fof(f13,axiom,(
% 2.43/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f28,plain,(
% 2.43/1.01    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.43/1.01    inference(ennf_transformation,[],[f13])).
% 2.43/1.01  
% 2.43/1.01  fof(f29,plain,(
% 2.43/1.01    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.43/1.01    inference(flattening,[],[f28])).
% 2.43/1.01  
% 2.43/1.01  fof(f60,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f29])).
% 2.43/1.01  
% 2.43/1.01  fof(f67,plain,(
% 2.43/1.01    v1_funct_1(sK5)),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f7,axiom,(
% 2.43/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f23,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f7])).
% 2.43/1.01  
% 2.43/1.01  fof(f54,plain,(
% 2.43/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f23])).
% 2.43/1.01  
% 2.43/1.01  fof(f8,axiom,(
% 2.43/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f55,plain,(
% 2.43/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f8])).
% 2.43/1.01  
% 2.43/1.01  fof(f14,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f30,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 2.43/1.01    inference(ennf_transformation,[],[f14])).
% 2.43/1.01  
% 2.43/1.01  fof(f31,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 2.43/1.01    inference(flattening,[],[f30])).
% 2.43/1.01  
% 2.43/1.01  fof(f61,plain,(
% 2.43/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f31])).
% 2.43/1.01  
% 2.43/1.01  fof(f72,plain,(
% 2.43/1.01    k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  cnf(c_20,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK6,sK2) ),
% 2.43/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1999,plain,
% 2.43/1.01      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2007,plain,
% 2.43/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.43/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.43/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3517,plain,
% 2.43/1.01      ( r2_hidden(sK6,sK2) = iProver_top
% 2.43/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1999,c_2007]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_33,plain,
% 2.43/1.01      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_18,negated_conjecture,
% 2.43/1.01      ( k1_xboole_0 != sK2 ),
% 2.43/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2219,plain,
% 2.43/1.01      ( ~ m1_subset_1(sK6,sK2) | r2_hidden(sK6,sK2) | v1_xboole_0(sK2) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2220,plain,
% 2.43/1.01      ( m1_subset_1(sK6,sK2) != iProver_top
% 2.43/1.01      | r2_hidden(sK6,sK2) = iProver_top
% 2.43/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_2219]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2,plain,
% 2.43/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2333,plain,
% 2.43/1.01      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2334,plain,
% 2.43/1.01      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_2333]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3847,plain,
% 2.43/1.01      ( r2_hidden(sK6,sK2) = iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_3517,c_33,c_18,c_2220,c_2334]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_23,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.43/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1997,plain,
% 2.43/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_13,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2001,plain,
% 2.43/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.43/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3379,plain,
% 2.43/1.01      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1997,c_2001]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_16,plain,
% 2.43/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/1.01      | ~ r2_hidden(X3,X1)
% 2.43/1.01      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | k1_xboole_0 = X2 ),
% 2.43/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_24,negated_conjecture,
% 2.43/1.01      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.43/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_364,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/1.01      | ~ r2_hidden(X3,X1)
% 2.43/1.01      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | sK3 != X2
% 2.43/1.01      | sK2 != X1
% 2.43/1.01      | sK4 != X0
% 2.43/1.01      | k1_xboole_0 = X2 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_365,plain,
% 2.43/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.43/1.01      | ~ r2_hidden(X0,sK2)
% 2.43/1.01      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 2.43/1.01      | ~ v1_funct_1(sK4)
% 2.43/1.01      | k1_xboole_0 = sK3 ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_364]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_25,negated_conjecture,
% 2.43/1.01      ( v1_funct_1(sK4) ),
% 2.43/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_369,plain,
% 2.43/1.01      ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 2.43/1.01      | ~ r2_hidden(X0,sK2)
% 2.43/1.01      | k1_xboole_0 = sK3 ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_365,c_25,c_23]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_370,plain,
% 2.43/1.01      ( ~ r2_hidden(X0,sK2)
% 2.43/1.01      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 2.43/1.01      | k1_xboole_0 = sK3 ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_369]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1993,plain,
% 2.43/1.01      ( k1_xboole_0 = sK3
% 2.43/1.01      | r2_hidden(X0,sK2) != iProver_top
% 2.43/1.01      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3656,plain,
% 2.43/1.01      ( sK3 = k1_xboole_0
% 2.43/1.01      | r2_hidden(X0,sK2) != iProver_top
% 2.43/1.01      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_3379,c_1993]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_19,negated_conjecture,
% 2.43/1.01      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2000,plain,
% 2.43/1.01      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3659,plain,
% 2.43/1.01      ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_3379,c_2000]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_21,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 2.43/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1998,plain,
% 2.43/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_12,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2002,plain,
% 2.43/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.43/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3499,plain,
% 2.43/1.01      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1998,c_2002]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3763,plain,
% 2.43/1.01      ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
% 2.43/1.01      inference(light_normalisation,[status(thm)],[c_3659,c_3499]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.43/1.01      | ~ r2_hidden(X2,X0)
% 2.43/1.01      | r2_hidden(X2,X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_6,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_189,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.43/1.01      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_190,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_189]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_242,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.43/1.01      inference(bin_hyper_res,[status(thm)],[c_4,c_190]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1995,plain,
% 2.43/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.43/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.43/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3766,plain,
% 2.43/1.01      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.43/1.01      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_3763,c_1995]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5215,plain,
% 2.43/1.01      ( sK3 = k1_xboole_0
% 2.43/1.01      | r2_hidden(X0,sK2) != iProver_top
% 2.43/1.01      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_3656,c_3766]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_26,negated_conjecture,
% 2.43/1.01      ( ~ v1_xboole_0(sK3) ),
% 2.43/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_10,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2203,plain,
% 2.43/1.01      ( ~ r1_tarski(k1_xboole_0,X0) | ~ r2_hidden(X0,k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2416,plain,
% 2.43/1.01      ( ~ r1_tarski(k1_xboole_0,sK0(k1_xboole_0))
% 2.43/1.01      | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2203]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_0,plain,
% 2.43/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2417,plain,
% 2.43/1.01      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 2.43/1.01      | v1_xboole_0(k1_xboole_0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3,plain,
% 2.43/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3166,plain,
% 2.43/1.01      ( r1_tarski(k1_xboole_0,sK0(k1_xboole_0)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1401,plain,
% 2.43/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.43/1.01      theory(equality) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4740,plain,
% 2.43/1.01      ( v1_xboole_0(X0)
% 2.43/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.43/1.01      | X0 != k1_xboole_0 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4743,plain,
% 2.43/1.01      ( v1_xboole_0(sK3)
% 2.43/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.43/1.01      | sK3 != k1_xboole_0 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_4740]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5379,plain,
% 2.43/1.01      ( r2_hidden(X0,sK2) != iProver_top
% 2.43/1.01      | r2_hidden(k1_funct_1(sK4,X0),k1_relat_1(sK5)) = iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_5215,c_26,c_2416,c_2417,c_3166,c_4743]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_7,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2005,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2883,plain,
% 2.43/1.01      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1998,c_2005]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2006,plain,
% 2.43/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.43/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_11,plain,
% 2.43/1.01      ( v5_relat_1(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.43/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_14,plain,
% 2.43/1.01      ( ~ v5_relat_1(X0,X1)
% 2.43/1.01      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | ~ v1_relat_1(X0)
% 2.43/1.01      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 2.43/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_338,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | ~ v1_relat_1(X0)
% 2.43/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3) ),
% 2.43/1.01      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_22,negated_conjecture,
% 2.43/1.01      ( v1_funct_1(sK5) ),
% 2.43/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_522,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/1.01      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.43/1.01      | ~ v1_relat_1(X0)
% 2.43/1.01      | k7_partfun1(X2,X0,X3) = k1_funct_1(X0,X3)
% 2.43/1.01      | sK5 != X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_338,c_22]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_523,plain,
% 2.43/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.43/1.01      | ~ r2_hidden(X2,k1_relat_1(sK5))
% 2.43/1.01      | ~ v1_relat_1(sK5)
% 2.43/1.01      | k7_partfun1(X1,sK5,X2) = k1_funct_1(sK5,X2) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_522]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1991,plain,
% 2.43/1.01      ( k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1)
% 2.43/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 2.43/1.01      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 2.43/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2895,plain,
% 2.43/1.01      ( k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1)
% 2.43/1.01      | r1_tarski(sK5,k2_zfmisc_1(X2,X0)) != iProver_top
% 2.43/1.01      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 2.43/1.01      | v1_relat_1(sK5) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2006,c_1991]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_32,plain,
% 2.43/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2193,plain,
% 2.43/1.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 2.43/1.01      | r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2194,plain,
% 2.43/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 2.43/1.01      | r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_2193]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_8,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.43/1.01      | ~ v1_relat_1(X1)
% 2.43/1.01      | v1_relat_1(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_245,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.43/1.01      inference(bin_hyper_res,[status(thm)],[c_8,c_190]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2209,plain,
% 2.43/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.43/1.01      | v1_relat_1(X0)
% 2.43/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_245]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2569,plain,
% 2.43/1.01      ( ~ r1_tarski(sK5,k2_zfmisc_1(sK3,sK1))
% 2.43/1.01      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 2.43/1.01      | v1_relat_1(sK5) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2209]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2570,plain,
% 2.43/1.01      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK1)) != iProver_top
% 2.43/1.01      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 2.43/1.01      | v1_relat_1(sK5) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_2569]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_9,plain,
% 2.43/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2642,plain,
% 2.43/1.01      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2643,plain,
% 2.43/1.01      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_2642]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4424,plain,
% 2.43/1.01      ( r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 2.43/1.01      | r1_tarski(sK5,k2_zfmisc_1(X2,X0)) != iProver_top
% 2.43/1.01      | k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_2895,c_32,c_2194,c_2570,c_2643]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4425,plain,
% 2.43/1.01      ( k7_partfun1(X0,sK5,X1) = k1_funct_1(sK5,X1)
% 2.43/1.01      | r1_tarski(sK5,k2_zfmisc_1(X2,X0)) != iProver_top
% 2.43/1.01      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_4424]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4433,plain,
% 2.43/1.01      ( k7_partfun1(sK1,sK5,X0) = k1_funct_1(sK5,X0)
% 2.43/1.01      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2883,c_4425]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5388,plain,
% 2.43/1.01      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,X0)) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 2.43/1.01      | r2_hidden(X0,sK2) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_5379,c_4433]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5407,plain,
% 2.43/1.01      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_3847,c_5388]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_15,plain,
% 2.43/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.43/1.01      | ~ m1_subset_1(X3,X1)
% 2.43/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.43/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 2.43/1.01      | ~ v1_funct_1(X4)
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | v1_xboole_0(X2)
% 2.43/1.01      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 2.43/1.01      | k1_xboole_0 = X1 ),
% 2.43/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_385,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.43/1.01      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
% 2.43/1.01      | ~ r1_tarski(k2_relset_1(X1,X3,X2),k1_relset_1(X3,X5,X4))
% 2.43/1.01      | ~ v1_funct_1(X2)
% 2.43/1.01      | ~ v1_funct_1(X4)
% 2.43/1.01      | v1_xboole_0(X3)
% 2.43/1.01      | k1_funct_1(k8_funct_2(X1,X3,X5,X2,X4),X0) = k1_funct_1(X4,k1_funct_1(X2,X0))
% 2.43/1.01      | sK3 != X3
% 2.43/1.01      | sK2 != X1
% 2.43/1.01      | sK4 != X2
% 2.43/1.01      | k1_xboole_0 = X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_386,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 2.43/1.01      | ~ m1_subset_1(X2,sK2)
% 2.43/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.43/1.01      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | ~ v1_funct_1(sK4)
% 2.43/1.01      | v1_xboole_0(sK3)
% 2.43/1.01      | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2))
% 2.43/1.01      | k1_xboole_0 = sK2 ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_385]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_390,plain,
% 2.43/1.01      ( k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2))
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 2.43/1.01      | ~ m1_subset_1(X2,sK2) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_386,c_26,c_25,c_23,c_18]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_391,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 2.43/1.01      | ~ m1_subset_1(X2,sK2)
% 2.43/1.01      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
% 2.43/1.01      | ~ v1_funct_1(X0)
% 2.43/1.01      | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2)) ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_390]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_504,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 2.43/1.01      | ~ m1_subset_1(X2,sK2)
% 2.43/1.01      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,X0))
% 2.43/1.01      | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,X0),X2) = k1_funct_1(X0,k1_funct_1(sK4,X2))
% 2.43/1.01      | sK5 != X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_391,c_22]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_505,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,sK2)
% 2.43/1.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
% 2.43/1.01      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X1,sK5))
% 2.43/1.01      | k1_funct_1(k8_funct_2(sK2,sK3,X1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0)) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_504]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1992,plain,
% 2.43/1.01      ( k1_funct_1(k8_funct_2(sK2,sK3,X0,sK4,sK5),X1) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 2.43/1.01      | m1_subset_1(X1,sK2) != iProver_top
% 2.43/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 2.43/1.01      | r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,X0,sK5)) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2605,plain,
% 2.43/1.01      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 2.43/1.01      | m1_subset_1(X0,sK2) != iProver_top
% 2.43/1.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2000,c_1992]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2610,plain,
% 2.43/1.01      ( m1_subset_1(X0,sK2) != iProver_top
% 2.43/1.01      | k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0)) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_2605,c_32]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2611,plain,
% 2.43/1.01      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK4,X0))
% 2.43/1.01      | m1_subset_1(X0,sK2) != iProver_top ),
% 2.43/1.01      inference(renaming,[status(thm)],[c_2610]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2618,plain,
% 2.43/1.01      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1999,c_2611]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_17,negated_conjecture,
% 2.43/1.01      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 2.43/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2659,plain,
% 2.43/1.01      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_2618,c_17]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(contradiction,plain,
% 2.43/1.01      ( $false ),
% 2.43/1.01      inference(minisat,[status(thm)],[c_5407,c_2659]) ).
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  ------                               Statistics
% 2.43/1.01  
% 2.43/1.01  ------ General
% 2.43/1.01  
% 2.43/1.01  abstr_ref_over_cycles:                  0
% 2.43/1.01  abstr_ref_under_cycles:                 0
% 2.43/1.01  gc_basic_clause_elim:                   0
% 2.43/1.01  forced_gc_time:                         0
% 2.43/1.01  parsing_time:                           0.012
% 2.43/1.01  unif_index_cands_time:                  0.
% 2.43/1.01  unif_index_add_time:                    0.
% 2.43/1.01  orderings_time:                         0.
% 2.43/1.01  out_proof_time:                         0.012
% 2.43/1.01  total_time:                             0.171
% 2.43/1.01  num_of_symbols:                         56
% 2.43/1.01  num_of_terms:                           3799
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing
% 2.43/1.01  
% 2.43/1.01  num_of_splits:                          0
% 2.43/1.01  num_of_split_atoms:                     0
% 2.43/1.01  num_of_reused_defs:                     0
% 2.43/1.01  num_eq_ax_congr_red:                    9
% 2.43/1.01  num_of_sem_filtered_clauses:            1
% 2.43/1.01  num_of_subtypes:                        0
% 2.43/1.01  monotx_restored_types:                  0
% 2.43/1.01  sat_num_of_epr_types:                   0
% 2.43/1.01  sat_num_of_non_cyclic_types:            0
% 2.43/1.01  sat_guarded_non_collapsed_types:        0
% 2.43/1.01  num_pure_diseq_elim:                    0
% 2.43/1.01  simp_replaced_by:                       0
% 2.43/1.01  res_preprocessed:                       133
% 2.43/1.01  prep_upred:                             0
% 2.43/1.01  prep_unflattend:                        62
% 2.43/1.01  smt_new_axioms:                         0
% 2.43/1.01  pred_elim_cands:                        5
% 2.43/1.01  pred_elim:                              3
% 2.43/1.01  pred_elim_cl:                           2
% 2.43/1.01  pred_elim_cycles:                       7
% 2.43/1.01  merged_defs:                            8
% 2.43/1.01  merged_defs_ncl:                        0
% 2.43/1.01  bin_hyper_res:                          10
% 2.43/1.01  prep_cycles:                            4
% 2.43/1.01  pred_elim_time:                         0.015
% 2.43/1.01  splitting_time:                         0.
% 2.43/1.01  sem_filter_time:                        0.
% 2.43/1.01  monotx_time:                            0.
% 2.43/1.01  subtype_inf_time:                       0.
% 2.43/1.01  
% 2.43/1.01  ------ Problem properties
% 2.43/1.01  
% 2.43/1.01  clauses:                                25
% 2.43/1.01  conjectures:                            7
% 2.43/1.01  epr:                                    10
% 2.43/1.01  horn:                                   22
% 2.43/1.01  ground:                                 7
% 2.43/1.01  unary:                                  9
% 2.43/1.01  binary:                                 8
% 2.43/1.01  lits:                                   53
% 2.43/1.01  lits_eq:                                10
% 2.43/1.01  fd_pure:                                0
% 2.43/1.01  fd_pseudo:                              0
% 2.43/1.01  fd_cond:                                1
% 2.43/1.01  fd_pseudo_cond:                         0
% 2.43/1.01  ac_symbols:                             0
% 2.43/1.01  
% 2.43/1.01  ------ Propositional Solver
% 2.43/1.01  
% 2.43/1.01  prop_solver_calls:                      27
% 2.43/1.01  prop_fast_solver_calls:                 981
% 2.43/1.01  smt_solver_calls:                       0
% 2.43/1.01  smt_fast_solver_calls:                  0
% 2.43/1.01  prop_num_of_clauses:                    1801
% 2.43/1.01  prop_preprocess_simplified:             5644
% 2.43/1.01  prop_fo_subsumed:                       18
% 2.43/1.01  prop_solver_time:                       0.
% 2.43/1.01  smt_solver_time:                        0.
% 2.43/1.01  smt_fast_solver_time:                   0.
% 2.43/1.01  prop_fast_solver_time:                  0.
% 2.43/1.01  prop_unsat_core_time:                   0.
% 2.43/1.01  
% 2.43/1.01  ------ QBF
% 2.43/1.01  
% 2.43/1.01  qbf_q_res:                              0
% 2.43/1.01  qbf_num_tautologies:                    0
% 2.43/1.01  qbf_prep_cycles:                        0
% 2.43/1.01  
% 2.43/1.01  ------ BMC1
% 2.43/1.01  
% 2.43/1.01  bmc1_current_bound:                     -1
% 2.43/1.01  bmc1_last_solved_bound:                 -1
% 2.43/1.01  bmc1_unsat_core_size:                   -1
% 2.43/1.01  bmc1_unsat_core_parents_size:           -1
% 2.43/1.01  bmc1_merge_next_fun:                    0
% 2.43/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation
% 2.43/1.01  
% 2.43/1.01  inst_num_of_clauses:                    571
% 2.43/1.01  inst_num_in_passive:                    0
% 2.43/1.01  inst_num_in_active:                     339
% 2.43/1.01  inst_num_in_unprocessed:                233
% 2.43/1.01  inst_num_of_loops:                      380
% 2.43/1.01  inst_num_of_learning_restarts:          0
% 2.43/1.01  inst_num_moves_active_passive:          38
% 2.43/1.01  inst_lit_activity:                      0
% 2.43/1.01  inst_lit_activity_moves:                0
% 2.43/1.01  inst_num_tautologies:                   0
% 2.43/1.01  inst_num_prop_implied:                  0
% 2.43/1.01  inst_num_existing_simplified:           0
% 2.43/1.01  inst_num_eq_res_simplified:             0
% 2.43/1.01  inst_num_child_elim:                    0
% 2.43/1.01  inst_num_of_dismatching_blockings:      110
% 2.43/1.01  inst_num_of_non_proper_insts:           537
% 2.43/1.01  inst_num_of_duplicates:                 0
% 2.43/1.01  inst_inst_num_from_inst_to_res:         0
% 2.43/1.01  inst_dismatching_checking_time:         0.
% 2.43/1.01  
% 2.43/1.01  ------ Resolution
% 2.43/1.01  
% 2.43/1.01  res_num_of_clauses:                     0
% 2.43/1.01  res_num_in_passive:                     0
% 2.43/1.01  res_num_in_active:                      0
% 2.43/1.01  res_num_of_loops:                       137
% 2.43/1.01  res_forward_subset_subsumed:            70
% 2.43/1.01  res_backward_subset_subsumed:           2
% 2.43/1.01  res_forward_subsumed:                   0
% 2.43/1.01  res_backward_subsumed:                  1
% 2.43/1.01  res_forward_subsumption_resolution:     0
% 2.43/1.01  res_backward_subsumption_resolution:    0
% 2.43/1.01  res_clause_to_clause_subsumption:       174
% 2.43/1.01  res_orphan_elimination:                 0
% 2.43/1.01  res_tautology_del:                      117
% 2.43/1.01  res_num_eq_res_simplified:              0
% 2.43/1.01  res_num_sel_changes:                    0
% 2.43/1.01  res_moves_from_active_to_pass:          0
% 2.43/1.01  
% 2.43/1.01  ------ Superposition
% 2.43/1.01  
% 2.43/1.01  sup_time_total:                         0.
% 2.43/1.01  sup_time_generating:                    0.
% 2.43/1.01  sup_time_sim_full:                      0.
% 2.43/1.01  sup_time_sim_immed:                     0.
% 2.43/1.01  
% 2.43/1.01  sup_num_of_clauses:                     77
% 2.43/1.01  sup_num_in_active:                      66
% 2.43/1.01  sup_num_in_passive:                     11
% 2.43/1.01  sup_num_of_loops:                       75
% 2.43/1.01  sup_fw_superposition:                   46
% 2.43/1.01  sup_bw_superposition:                   21
% 2.43/1.01  sup_immediate_simplified:               4
% 2.43/1.01  sup_given_eliminated:                   1
% 2.43/1.01  comparisons_done:                       0
% 2.43/1.01  comparisons_avoided:                    6
% 2.43/1.01  
% 2.43/1.01  ------ Simplifications
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  sim_fw_subset_subsumed:                 4
% 2.43/1.01  sim_bw_subset_subsumed:                 2
% 2.43/1.01  sim_fw_subsumed:                        0
% 2.43/1.01  sim_bw_subsumed:                        1
% 2.43/1.01  sim_fw_subsumption_res:                 0
% 2.43/1.01  sim_bw_subsumption_res:                 0
% 2.43/1.01  sim_tautology_del:                      4
% 2.43/1.01  sim_eq_tautology_del:                   1
% 2.43/1.01  sim_eq_res_simp:                        0
% 2.43/1.01  sim_fw_demodulated:                     0
% 2.43/1.01  sim_bw_demodulated:                     7
% 2.43/1.01  sim_light_normalised:                   5
% 2.43/1.01  sim_joinable_taut:                      0
% 2.43/1.01  sim_joinable_simp:                      0
% 2.43/1.01  sim_ac_normalised:                      0
% 2.43/1.01  sim_smt_subsumption:                    0
% 2.43/1.01  
%------------------------------------------------------------------------------
