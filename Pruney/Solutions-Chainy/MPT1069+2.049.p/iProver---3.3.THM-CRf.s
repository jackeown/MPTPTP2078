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
% DateTime   : Thu Dec  3 12:09:52 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 760 expanded)
%              Number of clauses        :  104 ( 214 expanded)
%              Number of leaves         :   21 ( 256 expanded)
%              Depth                    :   18
%              Number of atoms          :  635 (5610 expanded)
%              Number of equality atoms :  291 (1515 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) != k7_partfun1(X0,X4,k1_funct_1(X3,sK6))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) != k7_partfun1(X0,sK5,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK4,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
                  ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5))
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

fof(f67,plain,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f51,f66,f65,f64,f63])).

fof(f107,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f105,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f67])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f67])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f40,plain,(
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
    inference(flattening,[],[f40])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f102,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f104,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f103,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f106,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f16,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f111,plain,(
    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2051,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2071,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2922,plain,
    ( v5_relat_1(sK5,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2051,c_2071])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2052,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2078,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4205,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2052,c_2078])).

cnf(c_50,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2431,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2432,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2431])).

cnf(c_2635,plain,
    ( r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2995,plain,
    ( r2_hidden(sK6,sK2)
    | ~ m1_subset_1(sK6,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2635])).

cnf(c_2996,plain,
    ( r2_hidden(sK6,sK2) = iProver_top
    | m1_subset_1(sK6,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2995])).

cnf(c_4480,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4205,c_50,c_35,c_2432,c_2996])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2069,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3450,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2051,c_2069])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2049,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2068,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3099,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2049,c_2068])).

cnf(c_36,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2053,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3323,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3099,c_2053])).

cnf(c_3721,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3450,c_3323])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2075,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4383,plain,
    ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3721,c_2075])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2076,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4266,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_2076])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2073,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4477,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4266,c_2073])).

cnf(c_4694,plain,
    ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4383,c_4477])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2072,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2060,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6904,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_2060])).

cnf(c_27855,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4694,c_6904])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2061,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5805,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_2061])).

cnf(c_3451,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2049,c_2069])).

cnf(c_5815,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5805,c_3451])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_46,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1385,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2447,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_2449,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2447])).

cnf(c_8815,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5815,c_43,c_46,c_0,c_2449])).

cnf(c_27941,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27855,c_8815])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_45,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_48,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4265,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2051,c_2076])).

cnf(c_4399,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4265,c_2073])).

cnf(c_28631,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
    | v5_relat_1(sK5,X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27941,c_45,c_48,c_4399,c_4477])).

cnf(c_28641,plain,
    ( k7_partfun1(X0,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | v5_relat_1(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4480,c_28631])).

cnf(c_28804,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(superposition,[status(thm)],[c_2922,c_28641])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2067,plain,
    ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
    | k1_xboole_0 = X1
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7933,plain,
    ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_2067])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9664,plain,
    ( v1_funct_1(X1) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7933,c_43,c_45,c_46,c_47,c_0,c_2449])).

cnf(c_9665,plain,
    ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9664])).

cnf(c_9675,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3450,c_9665])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2059,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6676,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2051,c_2059])).

cnf(c_7510,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6676,c_48])).

cnf(c_7511,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7510])).

cnf(c_7521,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_7511])).

cnf(c_2609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2884,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X2,X3,X0,X1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_3316,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0,X1,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2884])).

cnf(c_3343,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3316])).

cnf(c_7601,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7521,c_42,c_40,c_39,c_38,c_3343])).

cnf(c_9689,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9675,c_7601])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9712,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9689,c_48,c_49,c_3721])).

cnf(c_34,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_9715,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k5_relat_1(sK4,sK5),sK6) ),
    inference(demodulation,[status(thm)],[c_9712,c_34])).

cnf(c_2050,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X4)
    | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2058,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | k1_xboole_0 = X3
    | v1_funct_2(X0,X4,X3) != iProver_top
    | r2_hidden(X2,X4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5626,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),X1) = k1_funct_1(X0,k1_funct_1(sK4,X1))
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_2058])).

cnf(c_6008,plain,
    ( v1_funct_1(X0) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | k1_funct_1(k5_relat_1(sK4,X0),X1) = k1_funct_1(X0,k1_funct_1(sK4,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5626,c_43,c_45,c_46,c_0,c_2449])).

cnf(c_6009,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),X1) = k1_funct_1(X0,k1_funct_1(sK4,X1))
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6008])).

cnf(c_6019,plain,
    ( k1_funct_1(X0,k1_funct_1(sK4,sK6)) = k1_funct_1(k5_relat_1(sK4,X0),sK6)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4480,c_6009])).

cnf(c_6050,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2050,c_6019])).

cnf(c_6191,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6050,c_4399])).

cnf(c_9716,plain,
    ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
    inference(light_normalisation,[status(thm)],[c_9715,c_6191])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28804,c_9716])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.66/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/1.51  
% 7.66/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.51  
% 7.66/1.51  ------  iProver source info
% 7.66/1.51  
% 7.66/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.51  git: non_committed_changes: false
% 7.66/1.51  git: last_make_outside_of_git: false
% 7.66/1.51  
% 7.66/1.51  ------ 
% 7.66/1.51  
% 7.66/1.51  ------ Input Options
% 7.66/1.51  
% 7.66/1.51  --out_options                           all
% 7.66/1.51  --tptp_safe_out                         true
% 7.66/1.51  --problem_path                          ""
% 7.66/1.51  --include_path                          ""
% 7.66/1.51  --clausifier                            res/vclausify_rel
% 7.66/1.51  --clausifier_options                    --mode clausify
% 7.66/1.51  --stdin                                 false
% 7.66/1.51  --stats_out                             all
% 7.66/1.51  
% 7.66/1.51  ------ General Options
% 7.66/1.51  
% 7.66/1.51  --fof                                   false
% 7.66/1.51  --time_out_real                         305.
% 7.66/1.51  --time_out_virtual                      -1.
% 7.66/1.51  --symbol_type_check                     false
% 7.66/1.51  --clausify_out                          false
% 7.66/1.51  --sig_cnt_out                           false
% 7.66/1.51  --trig_cnt_out                          false
% 7.66/1.51  --trig_cnt_out_tolerance                1.
% 7.66/1.51  --trig_cnt_out_sk_spl                   false
% 7.66/1.51  --abstr_cl_out                          false
% 7.66/1.51  
% 7.66/1.51  ------ Global Options
% 7.66/1.51  
% 7.66/1.51  --schedule                              default
% 7.66/1.51  --add_important_lit                     false
% 7.66/1.51  --prop_solver_per_cl                    1000
% 7.66/1.51  --min_unsat_core                        false
% 7.66/1.51  --soft_assumptions                      false
% 7.66/1.51  --soft_lemma_size                       3
% 7.66/1.51  --prop_impl_unit_size                   0
% 7.66/1.51  --prop_impl_unit                        []
% 7.66/1.51  --share_sel_clauses                     true
% 7.66/1.51  --reset_solvers                         false
% 7.66/1.51  --bc_imp_inh                            [conj_cone]
% 7.66/1.51  --conj_cone_tolerance                   3.
% 7.66/1.51  --extra_neg_conj                        none
% 7.66/1.51  --large_theory_mode                     true
% 7.66/1.51  --prolific_symb_bound                   200
% 7.66/1.51  --lt_threshold                          2000
% 7.66/1.51  --clause_weak_htbl                      true
% 7.66/1.51  --gc_record_bc_elim                     false
% 7.66/1.51  
% 7.66/1.51  ------ Preprocessing Options
% 7.66/1.51  
% 7.66/1.51  --preprocessing_flag                    true
% 7.66/1.51  --time_out_prep_mult                    0.1
% 7.66/1.51  --splitting_mode                        input
% 7.66/1.51  --splitting_grd                         true
% 7.66/1.51  --splitting_cvd                         false
% 7.66/1.51  --splitting_cvd_svl                     false
% 7.66/1.51  --splitting_nvd                         32
% 7.66/1.51  --sub_typing                            true
% 7.66/1.51  --prep_gs_sim                           true
% 7.66/1.51  --prep_unflatten                        true
% 7.66/1.51  --prep_res_sim                          true
% 7.66/1.51  --prep_upred                            true
% 7.66/1.51  --prep_sem_filter                       exhaustive
% 7.66/1.51  --prep_sem_filter_out                   false
% 7.66/1.51  --pred_elim                             true
% 7.66/1.51  --res_sim_input                         true
% 7.66/1.51  --eq_ax_congr_red                       true
% 7.66/1.51  --pure_diseq_elim                       true
% 7.66/1.51  --brand_transform                       false
% 7.66/1.51  --non_eq_to_eq                          false
% 7.66/1.51  --prep_def_merge                        true
% 7.66/1.51  --prep_def_merge_prop_impl              false
% 7.66/1.51  --prep_def_merge_mbd                    true
% 7.66/1.51  --prep_def_merge_tr_red                 false
% 7.66/1.51  --prep_def_merge_tr_cl                  false
% 7.66/1.51  --smt_preprocessing                     true
% 7.66/1.51  --smt_ac_axioms                         fast
% 7.66/1.51  --preprocessed_out                      false
% 7.66/1.51  --preprocessed_stats                    false
% 7.66/1.51  
% 7.66/1.51  ------ Abstraction refinement Options
% 7.66/1.51  
% 7.66/1.51  --abstr_ref                             []
% 7.66/1.51  --abstr_ref_prep                        false
% 7.66/1.51  --abstr_ref_until_sat                   false
% 7.66/1.51  --abstr_ref_sig_restrict                funpre
% 7.66/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.51  --abstr_ref_under                       []
% 7.66/1.51  
% 7.66/1.51  ------ SAT Options
% 7.66/1.51  
% 7.66/1.51  --sat_mode                              false
% 7.66/1.51  --sat_fm_restart_options                ""
% 7.66/1.51  --sat_gr_def                            false
% 7.66/1.51  --sat_epr_types                         true
% 7.66/1.51  --sat_non_cyclic_types                  false
% 7.66/1.51  --sat_finite_models                     false
% 7.66/1.51  --sat_fm_lemmas                         false
% 7.66/1.51  --sat_fm_prep                           false
% 7.66/1.52  --sat_fm_uc_incr                        true
% 7.66/1.52  --sat_out_model                         small
% 7.66/1.52  --sat_out_clauses                       false
% 7.66/1.52  
% 7.66/1.52  ------ QBF Options
% 7.66/1.52  
% 7.66/1.52  --qbf_mode                              false
% 7.66/1.52  --qbf_elim_univ                         false
% 7.66/1.52  --qbf_dom_inst                          none
% 7.66/1.52  --qbf_dom_pre_inst                      false
% 7.66/1.52  --qbf_sk_in                             false
% 7.66/1.52  --qbf_pred_elim                         true
% 7.66/1.52  --qbf_split                             512
% 7.66/1.52  
% 7.66/1.52  ------ BMC1 Options
% 7.66/1.52  
% 7.66/1.52  --bmc1_incremental                      false
% 7.66/1.52  --bmc1_axioms                           reachable_all
% 7.66/1.52  --bmc1_min_bound                        0
% 7.66/1.52  --bmc1_max_bound                        -1
% 7.66/1.52  --bmc1_max_bound_default                -1
% 7.66/1.52  --bmc1_symbol_reachability              true
% 7.66/1.52  --bmc1_property_lemmas                  false
% 7.66/1.52  --bmc1_k_induction                      false
% 7.66/1.52  --bmc1_non_equiv_states                 false
% 7.66/1.52  --bmc1_deadlock                         false
% 7.66/1.52  --bmc1_ucm                              false
% 7.66/1.52  --bmc1_add_unsat_core                   none
% 7.66/1.52  --bmc1_unsat_core_children              false
% 7.66/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.52  --bmc1_out_stat                         full
% 7.66/1.52  --bmc1_ground_init                      false
% 7.66/1.52  --bmc1_pre_inst_next_state              false
% 7.66/1.52  --bmc1_pre_inst_state                   false
% 7.66/1.52  --bmc1_pre_inst_reach_state             false
% 7.66/1.52  --bmc1_out_unsat_core                   false
% 7.66/1.52  --bmc1_aig_witness_out                  false
% 7.66/1.52  --bmc1_verbose                          false
% 7.66/1.52  --bmc1_dump_clauses_tptp                false
% 7.66/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.52  --bmc1_dump_file                        -
% 7.66/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.52  --bmc1_ucm_extend_mode                  1
% 7.66/1.52  --bmc1_ucm_init_mode                    2
% 7.66/1.52  --bmc1_ucm_cone_mode                    none
% 7.66/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.52  --bmc1_ucm_relax_model                  4
% 7.66/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.52  --bmc1_ucm_layered_model                none
% 7.66/1.52  --bmc1_ucm_max_lemma_size               10
% 7.66/1.52  
% 7.66/1.52  ------ AIG Options
% 7.66/1.52  
% 7.66/1.52  --aig_mode                              false
% 7.66/1.52  
% 7.66/1.52  ------ Instantiation Options
% 7.66/1.52  
% 7.66/1.52  --instantiation_flag                    true
% 7.66/1.52  --inst_sos_flag                         false
% 7.66/1.52  --inst_sos_phase                        true
% 7.66/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.52  --inst_lit_sel_side                     num_symb
% 7.66/1.52  --inst_solver_per_active                1400
% 7.66/1.52  --inst_solver_calls_frac                1.
% 7.66/1.52  --inst_passive_queue_type               priority_queues
% 7.66/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.52  --inst_passive_queues_freq              [25;2]
% 7.66/1.52  --inst_dismatching                      true
% 7.66/1.52  --inst_eager_unprocessed_to_passive     true
% 7.66/1.52  --inst_prop_sim_given                   true
% 7.66/1.52  --inst_prop_sim_new                     false
% 7.66/1.52  --inst_subs_new                         false
% 7.66/1.52  --inst_eq_res_simp                      false
% 7.66/1.52  --inst_subs_given                       false
% 7.66/1.52  --inst_orphan_elimination               true
% 7.66/1.52  --inst_learning_loop_flag               true
% 7.66/1.52  --inst_learning_start                   3000
% 7.66/1.52  --inst_learning_factor                  2
% 7.66/1.52  --inst_start_prop_sim_after_learn       3
% 7.66/1.52  --inst_sel_renew                        solver
% 7.66/1.52  --inst_lit_activity_flag                true
% 7.66/1.52  --inst_restr_to_given                   false
% 7.66/1.52  --inst_activity_threshold               500
% 7.66/1.52  --inst_out_proof                        true
% 7.66/1.52  
% 7.66/1.52  ------ Resolution Options
% 7.66/1.52  
% 7.66/1.52  --resolution_flag                       true
% 7.66/1.52  --res_lit_sel                           adaptive
% 7.66/1.52  --res_lit_sel_side                      none
% 7.66/1.52  --res_ordering                          kbo
% 7.66/1.52  --res_to_prop_solver                    active
% 7.66/1.52  --res_prop_simpl_new                    false
% 7.66/1.52  --res_prop_simpl_given                  true
% 7.66/1.52  --res_passive_queue_type                priority_queues
% 7.66/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.52  --res_passive_queues_freq               [15;5]
% 7.66/1.52  --res_forward_subs                      full
% 7.66/1.52  --res_backward_subs                     full
% 7.66/1.52  --res_forward_subs_resolution           true
% 7.66/1.52  --res_backward_subs_resolution          true
% 7.66/1.52  --res_orphan_elimination                true
% 7.66/1.52  --res_time_limit                        2.
% 7.66/1.52  --res_out_proof                         true
% 7.66/1.52  
% 7.66/1.52  ------ Superposition Options
% 7.66/1.52  
% 7.66/1.52  --superposition_flag                    true
% 7.66/1.52  --sup_passive_queue_type                priority_queues
% 7.66/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.52  --demod_completeness_check              fast
% 7.66/1.52  --demod_use_ground                      true
% 7.66/1.52  --sup_to_prop_solver                    passive
% 7.66/1.52  --sup_prop_simpl_new                    true
% 7.66/1.52  --sup_prop_simpl_given                  true
% 7.66/1.52  --sup_fun_splitting                     false
% 7.66/1.52  --sup_smt_interval                      50000
% 7.66/1.52  
% 7.66/1.52  ------ Superposition Simplification Setup
% 7.66/1.52  
% 7.66/1.52  --sup_indices_passive                   []
% 7.66/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.52  --sup_full_bw                           [BwDemod]
% 7.66/1.52  --sup_immed_triv                        [TrivRules]
% 7.66/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.52  --sup_immed_bw_main                     []
% 7.66/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.52  
% 7.66/1.52  ------ Combination Options
% 7.66/1.52  
% 7.66/1.52  --comb_res_mult                         3
% 7.66/1.52  --comb_sup_mult                         2
% 7.66/1.52  --comb_inst_mult                        10
% 7.66/1.52  
% 7.66/1.52  ------ Debug Options
% 7.66/1.52  
% 7.66/1.52  --dbg_backtrace                         false
% 7.66/1.52  --dbg_dump_prop_clauses                 false
% 7.66/1.52  --dbg_dump_prop_clauses_file            -
% 7.66/1.52  --dbg_out_stat                          false
% 7.66/1.52  ------ Parsing...
% 7.66/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.52  
% 7.66/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.66/1.52  
% 7.66/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.52  
% 7.66/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.52  ------ Proving...
% 7.66/1.52  ------ Problem Properties 
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  clauses                                 43
% 7.66/1.52  conjectures                             10
% 7.66/1.52  EPR                                     11
% 7.66/1.52  Horn                                    34
% 7.66/1.52  unary                                   16
% 7.66/1.52  binary                                  4
% 7.66/1.52  lits                                    127
% 7.66/1.52  lits eq                                 28
% 7.66/1.52  fd_pure                                 0
% 7.66/1.52  fd_pseudo                               0
% 7.66/1.52  fd_cond                                 7
% 7.66/1.52  fd_pseudo_cond                          1
% 7.66/1.52  AC symbols                              0
% 7.66/1.52  
% 7.66/1.52  ------ Schedule dynamic 5 is on 
% 7.66/1.52  
% 7.66/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  ------ 
% 7.66/1.52  Current options:
% 7.66/1.52  ------ 
% 7.66/1.52  
% 7.66/1.52  ------ Input Options
% 7.66/1.52  
% 7.66/1.52  --out_options                           all
% 7.66/1.52  --tptp_safe_out                         true
% 7.66/1.52  --problem_path                          ""
% 7.66/1.52  --include_path                          ""
% 7.66/1.52  --clausifier                            res/vclausify_rel
% 7.66/1.52  --clausifier_options                    --mode clausify
% 7.66/1.52  --stdin                                 false
% 7.66/1.52  --stats_out                             all
% 7.66/1.52  
% 7.66/1.52  ------ General Options
% 7.66/1.52  
% 7.66/1.52  --fof                                   false
% 7.66/1.52  --time_out_real                         305.
% 7.66/1.52  --time_out_virtual                      -1.
% 7.66/1.52  --symbol_type_check                     false
% 7.66/1.52  --clausify_out                          false
% 7.66/1.52  --sig_cnt_out                           false
% 7.66/1.52  --trig_cnt_out                          false
% 7.66/1.52  --trig_cnt_out_tolerance                1.
% 7.66/1.52  --trig_cnt_out_sk_spl                   false
% 7.66/1.52  --abstr_cl_out                          false
% 7.66/1.52  
% 7.66/1.52  ------ Global Options
% 7.66/1.52  
% 7.66/1.52  --schedule                              default
% 7.66/1.52  --add_important_lit                     false
% 7.66/1.52  --prop_solver_per_cl                    1000
% 7.66/1.52  --min_unsat_core                        false
% 7.66/1.52  --soft_assumptions                      false
% 7.66/1.52  --soft_lemma_size                       3
% 7.66/1.52  --prop_impl_unit_size                   0
% 7.66/1.52  --prop_impl_unit                        []
% 7.66/1.52  --share_sel_clauses                     true
% 7.66/1.52  --reset_solvers                         false
% 7.66/1.52  --bc_imp_inh                            [conj_cone]
% 7.66/1.52  --conj_cone_tolerance                   3.
% 7.66/1.52  --extra_neg_conj                        none
% 7.66/1.52  --large_theory_mode                     true
% 7.66/1.52  --prolific_symb_bound                   200
% 7.66/1.52  --lt_threshold                          2000
% 7.66/1.52  --clause_weak_htbl                      true
% 7.66/1.52  --gc_record_bc_elim                     false
% 7.66/1.52  
% 7.66/1.52  ------ Preprocessing Options
% 7.66/1.52  
% 7.66/1.52  --preprocessing_flag                    true
% 7.66/1.52  --time_out_prep_mult                    0.1
% 7.66/1.52  --splitting_mode                        input
% 7.66/1.52  --splitting_grd                         true
% 7.66/1.52  --splitting_cvd                         false
% 7.66/1.52  --splitting_cvd_svl                     false
% 7.66/1.52  --splitting_nvd                         32
% 7.66/1.52  --sub_typing                            true
% 7.66/1.52  --prep_gs_sim                           true
% 7.66/1.52  --prep_unflatten                        true
% 7.66/1.52  --prep_res_sim                          true
% 7.66/1.52  --prep_upred                            true
% 7.66/1.52  --prep_sem_filter                       exhaustive
% 7.66/1.52  --prep_sem_filter_out                   false
% 7.66/1.52  --pred_elim                             true
% 7.66/1.52  --res_sim_input                         true
% 7.66/1.52  --eq_ax_congr_red                       true
% 7.66/1.52  --pure_diseq_elim                       true
% 7.66/1.52  --brand_transform                       false
% 7.66/1.52  --non_eq_to_eq                          false
% 7.66/1.52  --prep_def_merge                        true
% 7.66/1.52  --prep_def_merge_prop_impl              false
% 7.66/1.52  --prep_def_merge_mbd                    true
% 7.66/1.52  --prep_def_merge_tr_red                 false
% 7.66/1.52  --prep_def_merge_tr_cl                  false
% 7.66/1.52  --smt_preprocessing                     true
% 7.66/1.52  --smt_ac_axioms                         fast
% 7.66/1.52  --preprocessed_out                      false
% 7.66/1.52  --preprocessed_stats                    false
% 7.66/1.52  
% 7.66/1.52  ------ Abstraction refinement Options
% 7.66/1.52  
% 7.66/1.52  --abstr_ref                             []
% 7.66/1.52  --abstr_ref_prep                        false
% 7.66/1.52  --abstr_ref_until_sat                   false
% 7.66/1.52  --abstr_ref_sig_restrict                funpre
% 7.66/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.52  --abstr_ref_under                       []
% 7.66/1.52  
% 7.66/1.52  ------ SAT Options
% 7.66/1.52  
% 7.66/1.52  --sat_mode                              false
% 7.66/1.52  --sat_fm_restart_options                ""
% 7.66/1.52  --sat_gr_def                            false
% 7.66/1.52  --sat_epr_types                         true
% 7.66/1.52  --sat_non_cyclic_types                  false
% 7.66/1.52  --sat_finite_models                     false
% 7.66/1.52  --sat_fm_lemmas                         false
% 7.66/1.52  --sat_fm_prep                           false
% 7.66/1.52  --sat_fm_uc_incr                        true
% 7.66/1.52  --sat_out_model                         small
% 7.66/1.52  --sat_out_clauses                       false
% 7.66/1.52  
% 7.66/1.52  ------ QBF Options
% 7.66/1.52  
% 7.66/1.52  --qbf_mode                              false
% 7.66/1.52  --qbf_elim_univ                         false
% 7.66/1.52  --qbf_dom_inst                          none
% 7.66/1.52  --qbf_dom_pre_inst                      false
% 7.66/1.52  --qbf_sk_in                             false
% 7.66/1.52  --qbf_pred_elim                         true
% 7.66/1.52  --qbf_split                             512
% 7.66/1.52  
% 7.66/1.52  ------ BMC1 Options
% 7.66/1.52  
% 7.66/1.52  --bmc1_incremental                      false
% 7.66/1.52  --bmc1_axioms                           reachable_all
% 7.66/1.52  --bmc1_min_bound                        0
% 7.66/1.52  --bmc1_max_bound                        -1
% 7.66/1.52  --bmc1_max_bound_default                -1
% 7.66/1.52  --bmc1_symbol_reachability              true
% 7.66/1.52  --bmc1_property_lemmas                  false
% 7.66/1.52  --bmc1_k_induction                      false
% 7.66/1.52  --bmc1_non_equiv_states                 false
% 7.66/1.52  --bmc1_deadlock                         false
% 7.66/1.52  --bmc1_ucm                              false
% 7.66/1.52  --bmc1_add_unsat_core                   none
% 7.66/1.52  --bmc1_unsat_core_children              false
% 7.66/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.52  --bmc1_out_stat                         full
% 7.66/1.52  --bmc1_ground_init                      false
% 7.66/1.52  --bmc1_pre_inst_next_state              false
% 7.66/1.52  --bmc1_pre_inst_state                   false
% 7.66/1.52  --bmc1_pre_inst_reach_state             false
% 7.66/1.52  --bmc1_out_unsat_core                   false
% 7.66/1.52  --bmc1_aig_witness_out                  false
% 7.66/1.52  --bmc1_verbose                          false
% 7.66/1.52  --bmc1_dump_clauses_tptp                false
% 7.66/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.52  --bmc1_dump_file                        -
% 7.66/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.52  --bmc1_ucm_extend_mode                  1
% 7.66/1.52  --bmc1_ucm_init_mode                    2
% 7.66/1.52  --bmc1_ucm_cone_mode                    none
% 7.66/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.52  --bmc1_ucm_relax_model                  4
% 7.66/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.52  --bmc1_ucm_layered_model                none
% 7.66/1.52  --bmc1_ucm_max_lemma_size               10
% 7.66/1.52  
% 7.66/1.52  ------ AIG Options
% 7.66/1.52  
% 7.66/1.52  --aig_mode                              false
% 7.66/1.52  
% 7.66/1.52  ------ Instantiation Options
% 7.66/1.52  
% 7.66/1.52  --instantiation_flag                    true
% 7.66/1.52  --inst_sos_flag                         false
% 7.66/1.52  --inst_sos_phase                        true
% 7.66/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.52  --inst_lit_sel_side                     none
% 7.66/1.52  --inst_solver_per_active                1400
% 7.66/1.52  --inst_solver_calls_frac                1.
% 7.66/1.52  --inst_passive_queue_type               priority_queues
% 7.66/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.52  --inst_passive_queues_freq              [25;2]
% 7.66/1.52  --inst_dismatching                      true
% 7.66/1.52  --inst_eager_unprocessed_to_passive     true
% 7.66/1.52  --inst_prop_sim_given                   true
% 7.66/1.52  --inst_prop_sim_new                     false
% 7.66/1.52  --inst_subs_new                         false
% 7.66/1.52  --inst_eq_res_simp                      false
% 7.66/1.52  --inst_subs_given                       false
% 7.66/1.52  --inst_orphan_elimination               true
% 7.66/1.52  --inst_learning_loop_flag               true
% 7.66/1.52  --inst_learning_start                   3000
% 7.66/1.52  --inst_learning_factor                  2
% 7.66/1.52  --inst_start_prop_sim_after_learn       3
% 7.66/1.52  --inst_sel_renew                        solver
% 7.66/1.52  --inst_lit_activity_flag                true
% 7.66/1.52  --inst_restr_to_given                   false
% 7.66/1.52  --inst_activity_threshold               500
% 7.66/1.52  --inst_out_proof                        true
% 7.66/1.52  
% 7.66/1.52  ------ Resolution Options
% 7.66/1.52  
% 7.66/1.52  --resolution_flag                       false
% 7.66/1.52  --res_lit_sel                           adaptive
% 7.66/1.52  --res_lit_sel_side                      none
% 7.66/1.52  --res_ordering                          kbo
% 7.66/1.52  --res_to_prop_solver                    active
% 7.66/1.52  --res_prop_simpl_new                    false
% 7.66/1.52  --res_prop_simpl_given                  true
% 7.66/1.52  --res_passive_queue_type                priority_queues
% 7.66/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.52  --res_passive_queues_freq               [15;5]
% 7.66/1.52  --res_forward_subs                      full
% 7.66/1.52  --res_backward_subs                     full
% 7.66/1.52  --res_forward_subs_resolution           true
% 7.66/1.52  --res_backward_subs_resolution          true
% 7.66/1.52  --res_orphan_elimination                true
% 7.66/1.52  --res_time_limit                        2.
% 7.66/1.52  --res_out_proof                         true
% 7.66/1.52  
% 7.66/1.52  ------ Superposition Options
% 7.66/1.52  
% 7.66/1.52  --superposition_flag                    true
% 7.66/1.52  --sup_passive_queue_type                priority_queues
% 7.66/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.52  --demod_completeness_check              fast
% 7.66/1.52  --demod_use_ground                      true
% 7.66/1.52  --sup_to_prop_solver                    passive
% 7.66/1.52  --sup_prop_simpl_new                    true
% 7.66/1.52  --sup_prop_simpl_given                  true
% 7.66/1.52  --sup_fun_splitting                     false
% 7.66/1.52  --sup_smt_interval                      50000
% 7.66/1.52  
% 7.66/1.52  ------ Superposition Simplification Setup
% 7.66/1.52  
% 7.66/1.52  --sup_indices_passive                   []
% 7.66/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.52  --sup_full_bw                           [BwDemod]
% 7.66/1.52  --sup_immed_triv                        [TrivRules]
% 7.66/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.52  --sup_immed_bw_main                     []
% 7.66/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.52  
% 7.66/1.52  ------ Combination Options
% 7.66/1.52  
% 7.66/1.52  --comb_res_mult                         3
% 7.66/1.52  --comb_sup_mult                         2
% 7.66/1.52  --comb_inst_mult                        10
% 7.66/1.52  
% 7.66/1.52  ------ Debug Options
% 7.66/1.52  
% 7.66/1.52  --dbg_backtrace                         false
% 7.66/1.52  --dbg_dump_prop_clauses                 false
% 7.66/1.52  --dbg_dump_prop_clauses_file            -
% 7.66/1.52  --dbg_out_stat                          false
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  ------ Proving...
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  % SZS status Theorem for theBenchmark.p
% 7.66/1.52  
% 7.66/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.52  
% 7.66/1.52  fof(f22,conjecture,(
% 7.66/1.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f23,negated_conjecture,(
% 7.66/1.52    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 7.66/1.52    inference(negated_conjecture,[],[f22])).
% 7.66/1.52  
% 7.66/1.52  fof(f50,plain,(
% 7.66/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.66/1.52    inference(ennf_transformation,[],[f23])).
% 7.66/1.52  
% 7.66/1.52  fof(f51,plain,(
% 7.66/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.66/1.52    inference(flattening,[],[f50])).
% 7.66/1.52  
% 7.66/1.52  fof(f66,plain,(
% 7.66/1.52    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) != k7_partfun1(X0,X4,k1_funct_1(X3,sK6)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 7.66/1.52    introduced(choice_axiom,[])).
% 7.66/1.52  
% 7.66/1.52  fof(f65,plain,(
% 7.66/1.52    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) != k7_partfun1(X0,sK5,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 7.66/1.52    introduced(choice_axiom,[])).
% 7.66/1.52  
% 7.66/1.52  fof(f64,plain,(
% 7.66/1.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK4,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.66/1.52    introduced(choice_axiom,[])).
% 7.66/1.52  
% 7.66/1.52  fof(f63,plain,(
% 7.66/1.52    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) != k7_partfun1(sK1,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 7.66/1.52    introduced(choice_axiom,[])).
% 7.66/1.52  
% 7.66/1.52  fof(f67,plain,(
% 7.66/1.52    (((k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 7.66/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f51,f66,f65,f64,f63])).
% 7.66/1.52  
% 7.66/1.52  fof(f107,plain,(
% 7.66/1.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f12,axiom,(
% 7.66/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f24,plain,(
% 7.66/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.66/1.52    inference(pure_predicate_removal,[],[f12])).
% 7.66/1.52  
% 7.66/1.52  fof(f34,plain,(
% 7.66/1.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.52    inference(ennf_transformation,[],[f24])).
% 7.66/1.52  
% 7.66/1.52  fof(f84,plain,(
% 7.66/1.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.52    inference(cnf_transformation,[],[f34])).
% 7.66/1.52  
% 7.66/1.52  fof(f108,plain,(
% 7.66/1.52    m1_subset_1(sK6,sK2)),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f6,axiom,(
% 7.66/1.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f26,plain,(
% 7.66/1.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.66/1.52    inference(ennf_transformation,[],[f6])).
% 7.66/1.52  
% 7.66/1.52  fof(f27,plain,(
% 7.66/1.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.66/1.52    inference(flattening,[],[f26])).
% 7.66/1.52  
% 7.66/1.52  fof(f77,plain,(
% 7.66/1.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f27])).
% 7.66/1.52  
% 7.66/1.52  fof(f110,plain,(
% 7.66/1.52    k1_xboole_0 != sK2),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f2,axiom,(
% 7.66/1.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f25,plain,(
% 7.66/1.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.66/1.52    inference(ennf_transformation,[],[f2])).
% 7.66/1.52  
% 7.66/1.52  fof(f69,plain,(
% 7.66/1.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f25])).
% 7.66/1.52  
% 7.66/1.52  fof(f14,axiom,(
% 7.66/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f36,plain,(
% 7.66/1.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.52    inference(ennf_transformation,[],[f14])).
% 7.66/1.52  
% 7.66/1.52  fof(f86,plain,(
% 7.66/1.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.52    inference(cnf_transformation,[],[f36])).
% 7.66/1.52  
% 7.66/1.52  fof(f105,plain,(
% 7.66/1.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f15,axiom,(
% 7.66/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f37,plain,(
% 7.66/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.52    inference(ennf_transformation,[],[f15])).
% 7.66/1.52  
% 7.66/1.52  fof(f87,plain,(
% 7.66/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.52    inference(cnf_transformation,[],[f37])).
% 7.66/1.52  
% 7.66/1.52  fof(f109,plain,(
% 7.66/1.52    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f9,axiom,(
% 7.66/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f31,plain,(
% 7.66/1.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.66/1.52    inference(ennf_transformation,[],[f9])).
% 7.66/1.52  
% 7.66/1.52  fof(f56,plain,(
% 7.66/1.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.66/1.52    inference(nnf_transformation,[],[f31])).
% 7.66/1.52  
% 7.66/1.52  fof(f81,plain,(
% 7.66/1.52    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f56])).
% 7.66/1.52  
% 7.66/1.52  fof(f8,axiom,(
% 7.66/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f30,plain,(
% 7.66/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.66/1.52    inference(ennf_transformation,[],[f8])).
% 7.66/1.52  
% 7.66/1.52  fof(f79,plain,(
% 7.66/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f30])).
% 7.66/1.52  
% 7.66/1.52  fof(f10,axiom,(
% 7.66/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f82,plain,(
% 7.66/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.66/1.52    inference(cnf_transformation,[],[f10])).
% 7.66/1.52  
% 7.66/1.52  fof(f11,axiom,(
% 7.66/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f32,plain,(
% 7.66/1.52    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.66/1.52    inference(ennf_transformation,[],[f11])).
% 7.66/1.52  
% 7.66/1.52  fof(f33,plain,(
% 7.66/1.52    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.66/1.52    inference(flattening,[],[f32])).
% 7.66/1.52  
% 7.66/1.52  fof(f83,plain,(
% 7.66/1.52    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f33])).
% 7.66/1.52  
% 7.66/1.52  fof(f18,axiom,(
% 7.66/1.52    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f42,plain,(
% 7.66/1.52    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.66/1.52    inference(ennf_transformation,[],[f18])).
% 7.66/1.52  
% 7.66/1.52  fof(f43,plain,(
% 7.66/1.52    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.66/1.52    inference(flattening,[],[f42])).
% 7.66/1.52  
% 7.66/1.52  fof(f95,plain,(
% 7.66/1.52    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f43])).
% 7.66/1.52  
% 7.66/1.52  fof(f17,axiom,(
% 7.66/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f40,plain,(
% 7.66/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.52    inference(ennf_transformation,[],[f17])).
% 7.66/1.52  
% 7.66/1.52  fof(f41,plain,(
% 7.66/1.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.52    inference(flattening,[],[f40])).
% 7.66/1.52  
% 7.66/1.52  fof(f57,plain,(
% 7.66/1.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.52    inference(nnf_transformation,[],[f41])).
% 7.66/1.52  
% 7.66/1.52  fof(f89,plain,(
% 7.66/1.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.52    inference(cnf_transformation,[],[f57])).
% 7.66/1.52  
% 7.66/1.52  fof(f102,plain,(
% 7.66/1.52    ~v1_xboole_0(sK3)),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f104,plain,(
% 7.66/1.52    v1_funct_2(sK4,sK2,sK3)),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f1,axiom,(
% 7.66/1.52    v1_xboole_0(k1_xboole_0)),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f68,plain,(
% 7.66/1.52    v1_xboole_0(k1_xboole_0)),
% 7.66/1.52    inference(cnf_transformation,[],[f1])).
% 7.66/1.52  
% 7.66/1.52  fof(f103,plain,(
% 7.66/1.52    v1_funct_1(sK4)),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f106,plain,(
% 7.66/1.52    v1_funct_1(sK5)),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f16,axiom,(
% 7.66/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f38,plain,(
% 7.66/1.52    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.66/1.52    inference(ennf_transformation,[],[f16])).
% 7.66/1.52  
% 7.66/1.52  fof(f39,plain,(
% 7.66/1.52    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.66/1.52    inference(flattening,[],[f38])).
% 7.66/1.52  
% 7.66/1.52  fof(f88,plain,(
% 7.66/1.52    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f39])).
% 7.66/1.52  
% 7.66/1.52  fof(f19,axiom,(
% 7.66/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f44,plain,(
% 7.66/1.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.66/1.52    inference(ennf_transformation,[],[f19])).
% 7.66/1.52  
% 7.66/1.52  fof(f45,plain,(
% 7.66/1.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.66/1.52    inference(flattening,[],[f44])).
% 7.66/1.52  
% 7.66/1.52  fof(f96,plain,(
% 7.66/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f45])).
% 7.66/1.52  
% 7.66/1.52  fof(f111,plain,(
% 7.66/1.52    k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6))),
% 7.66/1.52    inference(cnf_transformation,[],[f67])).
% 7.66/1.52  
% 7.66/1.52  fof(f20,axiom,(
% 7.66/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => (r2_hidden(X2,X0) => (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1))))),
% 7.66/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.52  
% 7.66/1.52  fof(f46,plain,(
% 7.66/1.52    ! [X0,X1,X2,X3] : (! [X4] : (((k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.66/1.52    inference(ennf_transformation,[],[f20])).
% 7.66/1.52  
% 7.66/1.52  fof(f47,plain,(
% 7.66/1.52    ! [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.66/1.52    inference(flattening,[],[f46])).
% 7.66/1.52  
% 7.66/1.52  fof(f97,plain,(
% 7.66/1.52    ( ! [X4,X2,X0,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X2)) = k1_funct_1(k5_relat_1(X3,X4),X2) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.66/1.52    inference(cnf_transformation,[],[f47])).
% 7.66/1.52  
% 7.66/1.52  cnf(c_38,negated_conjecture,
% 7.66/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.66/1.52      inference(cnf_transformation,[],[f107]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2051,plain,
% 7.66/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_16,plain,
% 7.66/1.52      ( v5_relat_1(X0,X1)
% 7.66/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.66/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2071,plain,
% 7.66/1.52      ( v5_relat_1(X0,X1) = iProver_top
% 7.66/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2922,plain,
% 7.66/1.52      ( v5_relat_1(sK5,sK1) = iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2051,c_2071]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_37,negated_conjecture,
% 7.66/1.52      ( m1_subset_1(sK6,sK2) ),
% 7.66/1.52      inference(cnf_transformation,[],[f108]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2052,plain,
% 7.66/1.52      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9,plain,
% 7.66/1.52      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 7.66/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2078,plain,
% 7.66/1.52      ( r2_hidden(X0,X1) = iProver_top
% 7.66/1.52      | m1_subset_1(X0,X1) != iProver_top
% 7.66/1.52      | v1_xboole_0(X1) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4205,plain,
% 7.66/1.52      ( r2_hidden(sK6,sK2) = iProver_top
% 7.66/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2052,c_2078]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_50,plain,
% 7.66/1.52      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_35,negated_conjecture,
% 7.66/1.52      ( k1_xboole_0 != sK2 ),
% 7.66/1.52      inference(cnf_transformation,[],[f110]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_1,plain,
% 7.66/1.52      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.66/1.52      inference(cnf_transformation,[],[f69]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2431,plain,
% 7.66/1.52      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_1]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2432,plain,
% 7.66/1.52      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_2431]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2635,plain,
% 7.66/1.52      ( r2_hidden(X0,sK2) | ~ m1_subset_1(X0,sK2) | v1_xboole_0(sK2) ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_9]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2995,plain,
% 7.66/1.52      ( r2_hidden(sK6,sK2) | ~ m1_subset_1(sK6,sK2) | v1_xboole_0(sK2) ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_2635]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2996,plain,
% 7.66/1.52      ( r2_hidden(sK6,sK2) = iProver_top
% 7.66/1.52      | m1_subset_1(sK6,sK2) != iProver_top
% 7.66/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_2995]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4480,plain,
% 7.66/1.52      ( r2_hidden(sK6,sK2) = iProver_top ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_4205,c_50,c_35,c_2432,c_2996]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_18,plain,
% 7.66/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.66/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2069,plain,
% 7.66/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.66/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_3450,plain,
% 7.66/1.52      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2051,c_2069]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_40,negated_conjecture,
% 7.66/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.66/1.52      inference(cnf_transformation,[],[f105]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2049,plain,
% 7.66/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_19,plain,
% 7.66/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.66/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2068,plain,
% 7.66/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.66/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_3099,plain,
% 7.66/1.52      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2049,c_2068]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_36,negated_conjecture,
% 7.66/1.52      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 7.66/1.52      inference(cnf_transformation,[],[f109]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2053,plain,
% 7.66/1.52      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_3323,plain,
% 7.66/1.52      ( r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 7.66/1.52      inference(demodulation,[status(thm)],[c_3099,c_2053]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_3721,plain,
% 7.66/1.52      ( r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) = iProver_top ),
% 7.66/1.52      inference(demodulation,[status(thm)],[c_3450,c_3323]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_12,plain,
% 7.66/1.52      ( v5_relat_1(X0,X1)
% 7.66/1.52      | ~ r1_tarski(k2_relat_1(X0),X1)
% 7.66/1.52      | ~ v1_relat_1(X0) ),
% 7.66/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2075,plain,
% 7.66/1.52      ( v5_relat_1(X0,X1) = iProver_top
% 7.66/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.66/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4383,plain,
% 7.66/1.52      ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top
% 7.66/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_3721,c_2075]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_11,plain,
% 7.66/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.66/1.52      | ~ v1_relat_1(X1)
% 7.66/1.52      | v1_relat_1(X0) ),
% 7.66/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2076,plain,
% 7.66/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.66/1.52      | v1_relat_1(X1) != iProver_top
% 7.66/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4266,plain,
% 7.66/1.52      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 7.66/1.52      | v1_relat_1(sK4) = iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2049,c_2076]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_14,plain,
% 7.66/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.66/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2073,plain,
% 7.66/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4477,plain,
% 7.66/1.52      ( v1_relat_1(sK4) = iProver_top ),
% 7.66/1.52      inference(forward_subsumption_resolution,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_4266,c_2073]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4694,plain,
% 7.66/1.52      ( v5_relat_1(sK4,k1_relat_1(sK5)) = iProver_top ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_4383,c_4477]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_15,plain,
% 7.66/1.52      ( ~ v5_relat_1(X0,X1)
% 7.66/1.52      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.66/1.52      | r2_hidden(k1_funct_1(X0,X2),X1)
% 7.66/1.52      | ~ v1_funct_1(X0)
% 7.66/1.52      | ~ v1_relat_1(X0) ),
% 7.66/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2072,plain,
% 7.66/1.52      ( v5_relat_1(X0,X1) != iProver_top
% 7.66/1.52      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 7.66/1.52      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 7.66/1.52      | v1_funct_1(X0) != iProver_top
% 7.66/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_27,plain,
% 7.66/1.52      ( ~ v5_relat_1(X0,X1)
% 7.66/1.52      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.66/1.52      | ~ v1_funct_1(X0)
% 7.66/1.52      | ~ v1_relat_1(X0)
% 7.66/1.52      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 7.66/1.52      inference(cnf_transformation,[],[f95]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2060,plain,
% 7.66/1.52      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 7.66/1.52      | v5_relat_1(X1,X0) != iProver_top
% 7.66/1.52      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 7.66/1.52      | v1_funct_1(X1) != iProver_top
% 7.66/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6904,plain,
% 7.66/1.52      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 7.66/1.52      | v5_relat_1(X1,X0) != iProver_top
% 7.66/1.52      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 7.66/1.52      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 7.66/1.52      | v1_funct_1(X1) != iProver_top
% 7.66/1.52      | v1_funct_1(X2) != iProver_top
% 7.66/1.52      | v1_relat_1(X2) != iProver_top
% 7.66/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2072,c_2060]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_27855,plain,
% 7.66/1.52      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 7.66/1.52      | v5_relat_1(sK5,X0) != iProver_top
% 7.66/1.52      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 7.66/1.52      | v1_funct_1(sK5) != iProver_top
% 7.66/1.52      | v1_funct_1(sK4) != iProver_top
% 7.66/1.52      | v1_relat_1(sK5) != iProver_top
% 7.66/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_4694,c_6904]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_26,plain,
% 7.66/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.66/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.66/1.52      | k1_xboole_0 = X2 ),
% 7.66/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2061,plain,
% 7.66/1.52      ( k1_relset_1(X0,X1,X2) = X0
% 7.66/1.52      | k1_xboole_0 = X1
% 7.66/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.66/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_5805,plain,
% 7.66/1.52      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 7.66/1.52      | sK3 = k1_xboole_0
% 7.66/1.52      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2049,c_2061]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_3451,plain,
% 7.66/1.52      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2049,c_2069]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_5815,plain,
% 7.66/1.52      ( k1_relat_1(sK4) = sK2
% 7.66/1.52      | sK3 = k1_xboole_0
% 7.66/1.52      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 7.66/1.52      inference(demodulation,[status(thm)],[c_5805,c_3451]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_43,negated_conjecture,
% 7.66/1.52      ( ~ v1_xboole_0(sK3) ),
% 7.66/1.52      inference(cnf_transformation,[],[f102]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_41,negated_conjecture,
% 7.66/1.52      ( v1_funct_2(sK4,sK2,sK3) ),
% 7.66/1.52      inference(cnf_transformation,[],[f104]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_46,plain,
% 7.66/1.52      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_0,plain,
% 7.66/1.52      ( v1_xboole_0(k1_xboole_0) ),
% 7.66/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_1385,plain,
% 7.66/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.66/1.52      theory(equality) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2447,plain,
% 7.66/1.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_1385]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2449,plain,
% 7.66/1.52      ( v1_xboole_0(sK3)
% 7.66/1.52      | ~ v1_xboole_0(k1_xboole_0)
% 7.66/1.52      | sK3 != k1_xboole_0 ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_2447]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_8815,plain,
% 7.66/1.52      ( k1_relat_1(sK4) = sK2 ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_5815,c_43,c_46,c_0,c_2449]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_27941,plain,
% 7.66/1.52      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 7.66/1.52      | v5_relat_1(sK5,X0) != iProver_top
% 7.66/1.52      | r2_hidden(X1,sK2) != iProver_top
% 7.66/1.52      | v1_funct_1(sK5) != iProver_top
% 7.66/1.52      | v1_funct_1(sK4) != iProver_top
% 7.66/1.52      | v1_relat_1(sK5) != iProver_top
% 7.66/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.66/1.52      inference(light_normalisation,[status(thm)],[c_27855,c_8815]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_42,negated_conjecture,
% 7.66/1.52      ( v1_funct_1(sK4) ),
% 7.66/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_45,plain,
% 7.66/1.52      ( v1_funct_1(sK4) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_39,negated_conjecture,
% 7.66/1.52      ( v1_funct_1(sK5) ),
% 7.66/1.52      inference(cnf_transformation,[],[f106]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_48,plain,
% 7.66/1.52      ( v1_funct_1(sK5) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4265,plain,
% 7.66/1.52      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.66/1.52      | v1_relat_1(sK5) = iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2051,c_2076]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_4399,plain,
% 7.66/1.52      ( v1_relat_1(sK5) = iProver_top ),
% 7.66/1.52      inference(forward_subsumption_resolution,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_4265,c_2073]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_28631,plain,
% 7.66/1.52      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,X1)) = k1_funct_1(sK5,k1_funct_1(sK4,X1))
% 7.66/1.52      | v5_relat_1(sK5,X0) != iProver_top
% 7.66/1.52      | r2_hidden(X1,sK2) != iProver_top ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_27941,c_45,c_48,c_4399,c_4477]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_28641,plain,
% 7.66/1.52      ( k7_partfun1(X0,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 7.66/1.52      | v5_relat_1(sK5,X0) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_4480,c_28631]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_28804,plain,
% 7.66/1.52      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2922,c_28641]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_20,plain,
% 7.66/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.66/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.66/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.52      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 7.66/1.52      | ~ v1_funct_1(X3)
% 7.66/1.52      | ~ v1_funct_1(X0)
% 7.66/1.52      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 7.66/1.52      | k1_xboole_0 = X2 ),
% 7.66/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2067,plain,
% 7.66/1.52      ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
% 7.66/1.52      | k1_xboole_0 = X1
% 7.66/1.52      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.66/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.66/1.52      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.66/1.52      | v1_funct_1(X3) != iProver_top
% 7.66/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_7933,plain,
% 7.66/1.52      ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 7.66/1.52      | sK3 = k1_xboole_0
% 7.66/1.52      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.66/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 7.66/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.66/1.52      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 7.66/1.52      | v1_funct_1(X1) != iProver_top
% 7.66/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_3099,c_2067]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_47,plain,
% 7.66/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9664,plain,
% 7.66/1.52      ( v1_funct_1(X1) != iProver_top
% 7.66/1.52      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 7.66/1.52      | k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 7.66/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_7933,c_43,c_45,c_46,c_47,c_0,c_2449]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9665,plain,
% 7.66/1.52      ( k1_partfun1(sK2,sK3,sK3,X0,sK4,X1) = k8_funct_2(sK2,sK3,X0,sK4,X1)
% 7.66/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) != iProver_top
% 7.66/1.52      | r1_tarski(k2_relat_1(sK4),k1_relset_1(sK3,X0,X1)) != iProver_top
% 7.66/1.52      | v1_funct_1(X1) != iProver_top ),
% 7.66/1.52      inference(renaming,[status(thm)],[c_9664]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9675,plain,
% 7.66/1.52      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
% 7.66/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.66/1.52      | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 7.66/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_3450,c_9665]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_28,plain,
% 7.66/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.66/1.52      | ~ v1_funct_1(X3)
% 7.66/1.52      | ~ v1_funct_1(X0)
% 7.66/1.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.66/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2059,plain,
% 7.66/1.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.66/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.66/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.52      | v1_funct_1(X5) != iProver_top
% 7.66/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6676,plain,
% 7.66/1.52      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 7.66/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.52      | v1_funct_1(X2) != iProver_top
% 7.66/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2051,c_2059]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_7510,plain,
% 7.66/1.52      ( v1_funct_1(X2) != iProver_top
% 7.66/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.52      | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_6676,c_48]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_7511,plain,
% 7.66/1.52      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 7.66/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.66/1.52      inference(renaming,[status(thm)],[c_7510]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_7521,plain,
% 7.66/1.52      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 7.66/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2049,c_7511]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2609,plain,
% 7.66/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.66/1.52      | ~ v1_funct_1(X0)
% 7.66/1.52      | ~ v1_funct_1(sK4)
% 7.66/1.52      | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_28]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2884,plain,
% 7.66/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.66/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.66/1.52      | ~ v1_funct_1(sK5)
% 7.66/1.52      | ~ v1_funct_1(sK4)
% 7.66/1.52      | k1_partfun1(X2,X3,X0,X1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_2609]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_3316,plain,
% 7.66/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.66/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.66/1.52      | ~ v1_funct_1(sK5)
% 7.66/1.52      | ~ v1_funct_1(sK4)
% 7.66/1.52      | k1_partfun1(X0,X1,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_2884]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_3343,plain,
% 7.66/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.66/1.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.66/1.52      | ~ v1_funct_1(sK5)
% 7.66/1.52      | ~ v1_funct_1(sK4)
% 7.66/1.52      | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.66/1.52      inference(instantiation,[status(thm)],[c_3316]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_7601,plain,
% 7.66/1.52      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_7521,c_42,c_40,c_39,c_38,c_3343]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9689,plain,
% 7.66/1.52      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 7.66/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.66/1.52      | r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5)) != iProver_top
% 7.66/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.66/1.52      inference(light_normalisation,[status(thm)],[c_9675,c_7601]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_49,plain,
% 7.66/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9712,plain,
% 7.66/1.52      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_9689,c_48,c_49,c_3721]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_34,negated_conjecture,
% 7.66/1.52      ( k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) != k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) ),
% 7.66/1.52      inference(cnf_transformation,[],[f111]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9715,plain,
% 7.66/1.52      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k5_relat_1(sK4,sK5),sK6) ),
% 7.66/1.52      inference(demodulation,[status(thm)],[c_9712,c_34]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2050,plain,
% 7.66/1.52      ( v1_funct_1(sK5) = iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_29,plain,
% 7.66/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.66/1.52      | ~ r2_hidden(X3,X1)
% 7.66/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.52      | ~ v1_funct_1(X4)
% 7.66/1.52      | ~ v1_funct_1(X0)
% 7.66/1.52      | ~ v1_relat_1(X4)
% 7.66/1.52      | k1_funct_1(k5_relat_1(X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 7.66/1.52      | k1_xboole_0 = X2 ),
% 7.66/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_2058,plain,
% 7.66/1.52      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 7.66/1.52      | k1_xboole_0 = X3
% 7.66/1.52      | v1_funct_2(X0,X4,X3) != iProver_top
% 7.66/1.52      | r2_hidden(X2,X4) != iProver_top
% 7.66/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) != iProver_top
% 7.66/1.52      | v1_funct_1(X0) != iProver_top
% 7.66/1.52      | v1_funct_1(X1) != iProver_top
% 7.66/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_5626,plain,
% 7.66/1.52      ( k1_funct_1(k5_relat_1(sK4,X0),X1) = k1_funct_1(X0,k1_funct_1(sK4,X1))
% 7.66/1.52      | sK3 = k1_xboole_0
% 7.66/1.52      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.66/1.52      | r2_hidden(X1,sK2) != iProver_top
% 7.66/1.52      | v1_funct_1(X0) != iProver_top
% 7.66/1.52      | v1_funct_1(sK4) != iProver_top
% 7.66/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2049,c_2058]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6008,plain,
% 7.66/1.52      ( v1_funct_1(X0) != iProver_top
% 7.66/1.52      | r2_hidden(X1,sK2) != iProver_top
% 7.66/1.52      | k1_funct_1(k5_relat_1(sK4,X0),X1) = k1_funct_1(X0,k1_funct_1(sK4,X1))
% 7.66/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_5626,c_43,c_45,c_46,c_0,c_2449]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6009,plain,
% 7.66/1.52      ( k1_funct_1(k5_relat_1(sK4,X0),X1) = k1_funct_1(X0,k1_funct_1(sK4,X1))
% 7.66/1.52      | r2_hidden(X1,sK2) != iProver_top
% 7.66/1.52      | v1_funct_1(X0) != iProver_top
% 7.66/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.52      inference(renaming,[status(thm)],[c_6008]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6019,plain,
% 7.66/1.52      ( k1_funct_1(X0,k1_funct_1(sK4,sK6)) = k1_funct_1(k5_relat_1(sK4,X0),sK6)
% 7.66/1.52      | v1_funct_1(X0) != iProver_top
% 7.66/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_4480,c_6009]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6050,plain,
% 7.66/1.52      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 7.66/1.52      | v1_relat_1(sK5) != iProver_top ),
% 7.66/1.52      inference(superposition,[status(thm)],[c_2050,c_6019]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_6191,plain,
% 7.66/1.52      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 7.66/1.52      inference(global_propositional_subsumption,
% 7.66/1.52                [status(thm)],
% 7.66/1.52                [c_6050,c_4399]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(c_9716,plain,
% 7.66/1.52      ( k7_partfun1(sK1,sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(sK5,k1_funct_1(sK4,sK6)) ),
% 7.66/1.52      inference(light_normalisation,[status(thm)],[c_9715,c_6191]) ).
% 7.66/1.52  
% 7.66/1.52  cnf(contradiction,plain,
% 7.66/1.52      ( $false ),
% 7.66/1.52      inference(minisat,[status(thm)],[c_28804,c_9716]) ).
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.52  
% 7.66/1.52  ------                               Statistics
% 7.66/1.52  
% 7.66/1.52  ------ General
% 7.66/1.52  
% 7.66/1.52  abstr_ref_over_cycles:                  0
% 7.66/1.52  abstr_ref_under_cycles:                 0
% 7.66/1.52  gc_basic_clause_elim:                   0
% 7.66/1.52  forced_gc_time:                         0
% 7.66/1.52  parsing_time:                           0.014
% 7.66/1.52  unif_index_cands_time:                  0.
% 7.66/1.52  unif_index_add_time:                    0.
% 7.66/1.52  orderings_time:                         0.
% 7.66/1.52  out_proof_time:                         0.016
% 7.66/1.52  total_time:                             0.791
% 7.66/1.52  num_of_symbols:                         58
% 7.66/1.52  num_of_terms:                           25499
% 7.66/1.52  
% 7.66/1.52  ------ Preprocessing
% 7.66/1.52  
% 7.66/1.52  num_of_splits:                          0
% 7.66/1.52  num_of_split_atoms:                     0
% 7.66/1.52  num_of_reused_defs:                     0
% 7.66/1.52  num_eq_ax_congr_red:                    42
% 7.66/1.52  num_of_sem_filtered_clauses:            1
% 7.66/1.52  num_of_subtypes:                        0
% 7.66/1.52  monotx_restored_types:                  0
% 7.66/1.52  sat_num_of_epr_types:                   0
% 7.66/1.52  sat_num_of_non_cyclic_types:            0
% 7.66/1.52  sat_guarded_non_collapsed_types:        0
% 7.66/1.52  num_pure_diseq_elim:                    0
% 7.66/1.52  simp_replaced_by:                       0
% 7.66/1.52  res_preprocessed:                       205
% 7.66/1.52  prep_upred:                             0
% 7.66/1.52  prep_unflattend:                        90
% 7.66/1.52  smt_new_axioms:                         0
% 7.66/1.52  pred_elim_cands:                        8
% 7.66/1.52  pred_elim:                              0
% 7.66/1.52  pred_elim_cl:                           0
% 7.66/1.52  pred_elim_cycles:                       4
% 7.66/1.52  merged_defs:                            0
% 7.66/1.52  merged_defs_ncl:                        0
% 7.66/1.52  bin_hyper_res:                          0
% 7.66/1.52  prep_cycles:                            4
% 7.66/1.52  pred_elim_time:                         0.018
% 7.66/1.52  splitting_time:                         0.
% 7.66/1.52  sem_filter_time:                        0.
% 7.66/1.52  monotx_time:                            0.001
% 7.66/1.52  subtype_inf_time:                       0.
% 7.66/1.52  
% 7.66/1.52  ------ Problem properties
% 7.66/1.52  
% 7.66/1.52  clauses:                                43
% 7.66/1.52  conjectures:                            10
% 7.66/1.52  epr:                                    11
% 7.66/1.52  horn:                                   34
% 7.66/1.52  ground:                                 11
% 7.66/1.52  unary:                                  16
% 7.66/1.52  binary:                                 4
% 7.66/1.52  lits:                                   127
% 7.66/1.52  lits_eq:                                28
% 7.66/1.52  fd_pure:                                0
% 7.66/1.52  fd_pseudo:                              0
% 7.66/1.52  fd_cond:                                7
% 7.66/1.52  fd_pseudo_cond:                         1
% 7.66/1.52  ac_symbols:                             0
% 7.66/1.52  
% 7.66/1.52  ------ Propositional Solver
% 7.66/1.52  
% 7.66/1.52  prop_solver_calls:                      31
% 7.66/1.52  prop_fast_solver_calls:                 2960
% 7.66/1.52  smt_solver_calls:                       0
% 7.66/1.52  smt_fast_solver_calls:                  0
% 7.66/1.52  prop_num_of_clauses:                    9386
% 7.66/1.52  prop_preprocess_simplified:             19965
% 7.66/1.52  prop_fo_subsumed:                       121
% 7.66/1.52  prop_solver_time:                       0.
% 7.66/1.52  smt_solver_time:                        0.
% 7.66/1.52  smt_fast_solver_time:                   0.
% 7.66/1.52  prop_fast_solver_time:                  0.
% 7.66/1.52  prop_unsat_core_time:                   0.001
% 7.66/1.52  
% 7.66/1.52  ------ QBF
% 7.66/1.52  
% 7.66/1.52  qbf_q_res:                              0
% 7.66/1.52  qbf_num_tautologies:                    0
% 7.66/1.52  qbf_prep_cycles:                        0
% 7.66/1.52  
% 7.66/1.52  ------ BMC1
% 7.66/1.52  
% 7.66/1.52  bmc1_current_bound:                     -1
% 7.66/1.52  bmc1_last_solved_bound:                 -1
% 7.66/1.52  bmc1_unsat_core_size:                   -1
% 7.66/1.52  bmc1_unsat_core_parents_size:           -1
% 7.66/1.52  bmc1_merge_next_fun:                    0
% 7.66/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.66/1.52  
% 7.66/1.52  ------ Instantiation
% 7.66/1.52  
% 7.66/1.52  inst_num_of_clauses:                    2885
% 7.66/1.52  inst_num_in_passive:                    722
% 7.66/1.52  inst_num_in_active:                     1239
% 7.66/1.52  inst_num_in_unprocessed:                924
% 7.66/1.52  inst_num_of_loops:                      1370
% 7.66/1.52  inst_num_of_learning_restarts:          0
% 7.66/1.52  inst_num_moves_active_passive:          127
% 7.66/1.52  inst_lit_activity:                      0
% 7.66/1.52  inst_lit_activity_moves:                0
% 7.66/1.52  inst_num_tautologies:                   0
% 7.66/1.52  inst_num_prop_implied:                  0
% 7.66/1.52  inst_num_existing_simplified:           0
% 7.66/1.52  inst_num_eq_res_simplified:             0
% 7.66/1.52  inst_num_child_elim:                    0
% 7.66/1.52  inst_num_of_dismatching_blockings:      1442
% 7.66/1.52  inst_num_of_non_proper_insts:           2780
% 7.66/1.52  inst_num_of_duplicates:                 0
% 7.66/1.52  inst_inst_num_from_inst_to_res:         0
% 7.66/1.52  inst_dismatching_checking_time:         0.
% 7.66/1.52  
% 7.66/1.52  ------ Resolution
% 7.66/1.52  
% 7.66/1.52  res_num_of_clauses:                     0
% 7.66/1.52  res_num_in_passive:                     0
% 7.66/1.52  res_num_in_active:                      0
% 7.66/1.52  res_num_of_loops:                       209
% 7.66/1.52  res_forward_subset_subsumed:            181
% 7.66/1.52  res_backward_subset_subsumed:           2
% 7.66/1.52  res_forward_subsumed:                   2
% 7.66/1.52  res_backward_subsumed:                  0
% 7.66/1.52  res_forward_subsumption_resolution:     0
% 7.66/1.52  res_backward_subsumption_resolution:    0
% 7.66/1.52  res_clause_to_clause_subsumption:       3157
% 7.66/1.52  res_orphan_elimination:                 0
% 7.66/1.52  res_tautology_del:                      114
% 7.66/1.52  res_num_eq_res_simplified:              0
% 7.66/1.52  res_num_sel_changes:                    0
% 7.66/1.52  res_moves_from_active_to_pass:          0
% 7.66/1.52  
% 7.66/1.52  ------ Superposition
% 7.66/1.52  
% 7.66/1.52  sup_time_total:                         0.
% 7.66/1.52  sup_time_generating:                    0.
% 7.66/1.52  sup_time_sim_full:                      0.
% 7.66/1.52  sup_time_sim_immed:                     0.
% 7.66/1.52  
% 7.66/1.52  sup_num_of_clauses:                     532
% 7.66/1.52  sup_num_in_active:                      265
% 7.66/1.52  sup_num_in_passive:                     267
% 7.66/1.52  sup_num_of_loops:                       272
% 7.66/1.52  sup_fw_superposition:                   387
% 7.66/1.52  sup_bw_superposition:                   221
% 7.66/1.52  sup_immediate_simplified:               81
% 7.66/1.52  sup_given_eliminated:                   4
% 7.66/1.52  comparisons_done:                       0
% 7.66/1.52  comparisons_avoided:                    14
% 7.66/1.52  
% 7.66/1.52  ------ Simplifications
% 7.66/1.52  
% 7.66/1.52  
% 7.66/1.52  sim_fw_subset_subsumed:                 16
% 7.66/1.52  sim_bw_subset_subsumed:                 0
% 7.66/1.52  sim_fw_subsumed:                        29
% 7.66/1.52  sim_bw_subsumed:                        38
% 7.66/1.52  sim_fw_subsumption_res:                 5
% 7.66/1.52  sim_bw_subsumption_res:                 0
% 7.66/1.52  sim_tautology_del:                      3
% 7.66/1.52  sim_eq_tautology_del:                   17
% 7.66/1.52  sim_eq_res_simp:                        0
% 7.66/1.52  sim_fw_demodulated:                     5
% 7.66/1.52  sim_bw_demodulated:                     4
% 7.66/1.52  sim_light_normalised:                   15
% 7.66/1.52  sim_joinable_taut:                      0
% 7.66/1.52  sim_joinable_simp:                      0
% 7.66/1.52  sim_ac_normalised:                      0
% 7.66/1.52  sim_smt_subsumption:                    0
% 7.66/1.52  
%------------------------------------------------------------------------------
