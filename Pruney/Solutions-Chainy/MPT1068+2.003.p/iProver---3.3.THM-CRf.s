%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:35 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  177 (2901 expanded)
%              Number of clauses        :  113 ( 803 expanded)
%              Number of leaves         :   20 ( 971 expanded)
%              Depth                    :   25
%              Number of atoms          :  634 (22573 expanded)
%              Number of equality atoms :  330 (6543 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f44,f43,f42,f41])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2003,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2017,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2756,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_2017])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2006,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2009,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3566,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_2009])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2016,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2914,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2003,c_2016])).

cnf(c_3570,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3566,c_2914])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4469,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3570,c_34])).

cnf(c_4470,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4469])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X1)
    | X4 != X0
    | k1_funct_1(X2,k1_funct_1(X3,X4)) = k1_funct_1(k5_relat_1(X3,X2),X4)
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | v1_xboole_0(k1_relat_1(X1))
    | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_1997,plain,
    ( k1_funct_1(X0,k1_funct_1(X1,X2)) = k1_funct_1(k5_relat_1(X1,X0),X2)
    | m1_subset_1(X2,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_4473,plain,
    ( k1_funct_1(k5_relat_1(sK3,X0),X1) = k1_funct_1(X0,k1_funct_1(sK3,X1))
    | sK2 = k1_xboole_0
    | m1_subset_1(X1,sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4470,c_1997])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2241,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2242,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2241])).

cnf(c_4686,plain,
    ( v1_funct_1(X0) != iProver_top
    | k1_funct_1(k5_relat_1(sK3,X0),X1) = k1_funct_1(X0,k1_funct_1(sK3,X1))
    | sK2 = k1_xboole_0
    | m1_subset_1(X1,sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4473,c_33,c_35,c_2242])).

cnf(c_4687,plain,
    ( k1_funct_1(k5_relat_1(sK3,X0),X1) = k1_funct_1(X0,k1_funct_1(sK3,X1))
    | sK2 = k1_xboole_0
    | m1_subset_1(X1,sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4686])).

cnf(c_4698,plain,
    ( k1_funct_1(X0,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,X0),sK5)
    | sK2 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_4687])).

cnf(c_4789,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK3),sK5) = k1_funct_1(sK3,k1_funct_1(sK3,sK5))
    | sK2 = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_4698])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2223,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2224,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2223])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2005,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2755,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_2017])).

cnf(c_4788,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK2 = k1_xboole_0
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2755,c_4698])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2913,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2005,c_2016])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2007,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3078,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2913,c_2007])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2015,plain,
    ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
    | k1_xboole_0 = X1
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4325,plain,
    ( k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) = k8_funct_2(X0,sK2,sK0,X1,sK4)
    | sK2 = k1_xboole_0
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2913,c_2015])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4502,plain,
    ( v1_funct_1(X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) != iProver_top
    | k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) = k8_funct_2(X0,sK2,sK0,X1,sK4)
    | sK2 = k1_xboole_0
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4325,c_36,c_37])).

cnf(c_4503,plain,
    ( k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) = k8_funct_2(X0,sK2,sK0,X1,sK4)
    | sK2 = k1_xboole_0
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4502])).

cnf(c_4514,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_4503])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2008,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3665,plain,
    ( k1_partfun1(X0,X1,sK2,sK0,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_2008])).

cnf(c_3839,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK0,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3665,c_36])).

cnf(c_3840,plain,
    ( k1_partfun1(X0,X1,sK2,sK0,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3839])).

cnf(c_3850,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_3840])).

cnf(c_2315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X3,X4,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2542,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0,X1,X2,X3,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2717,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2542])).

cnf(c_2903,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2717])).

cnf(c_3957,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3850,c_30,c_28,c_27,c_26,c_2903])).

cnf(c_4515,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4514,c_3957])).

cnf(c_4518,plain,
    ( sK2 = k1_xboole_0
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4515,c_33,c_34,c_35])).

cnf(c_4519,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4518])).

cnf(c_22,negated_conjecture,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_4522,plain,
    ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4519,c_22])).

cnf(c_5595,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4788,c_36,c_4522])).

cnf(c_5601,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4470,c_5595])).

cnf(c_5619,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4789,c_23,c_2224,c_5601])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2019,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2641,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_2019])).

cnf(c_5644,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_2641])).

cnf(c_5647,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_2003])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2013,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5890,plain,
    ( sK1 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5647,c_2013])).

cnf(c_1369,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1396,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_2474,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_2258,plain,
    ( ~ v1_funct_2(X0,sK1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2498,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_2503,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2498])).

cnf(c_2508,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_1370,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2530,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_2531,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_2653,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_3430,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2653])).

cnf(c_3431,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3430])).

cnf(c_1380,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2307,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | X2 != sK2
    | X1 != sK1
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_3998,plain,
    ( v1_funct_2(X0,sK1,X1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | X1 != sK2
    | X0 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2307])).

cnf(c_4394,plain,
    ( v1_funct_2(sK3,sK1,X0)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | X0 != sK2
    | sK1 != sK1
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3998])).

cnf(c_4395,plain,
    ( X0 != sK2
    | sK1 != sK1
    | sK3 != sK3
    | v1_funct_2(sK3,sK1,X0) = iProver_top
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4394])).

cnf(c_4397,plain,
    ( sK1 != sK1
    | sK3 != sK3
    | k1_xboole_0 != sK2
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK3,sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4395])).

cnf(c_5918,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5890,c_34,c_23,c_1396,c_2224,c_2474,c_2503,c_2508,c_2531,c_3431,c_4397,c_5601,c_5647])).

cnf(c_6203,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5644,c_5918])).

cnf(c_1,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_381,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_1998,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_2806,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1998])).

cnf(c_6210,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6203,c_2806])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2000,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5649,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5619,c_2000])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6210,c_5649])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:39:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.57/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/1.01  
% 2.57/1.01  ------  iProver source info
% 2.57/1.01  
% 2.57/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.57/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/1.01  git: non_committed_changes: false
% 2.57/1.01  git: last_make_outside_of_git: false
% 2.57/1.01  
% 2.57/1.01  ------ 
% 2.57/1.01  
% 2.57/1.01  ------ Input Options
% 2.57/1.01  
% 2.57/1.01  --out_options                           all
% 2.57/1.01  --tptp_safe_out                         true
% 2.57/1.01  --problem_path                          ""
% 2.57/1.01  --include_path                          ""
% 2.57/1.01  --clausifier                            res/vclausify_rel
% 2.57/1.01  --clausifier_options                    --mode clausify
% 2.57/1.01  --stdin                                 false
% 2.57/1.01  --stats_out                             all
% 2.57/1.01  
% 2.57/1.01  ------ General Options
% 2.57/1.01  
% 2.57/1.01  --fof                                   false
% 2.57/1.01  --time_out_real                         305.
% 2.57/1.01  --time_out_virtual                      -1.
% 2.57/1.01  --symbol_type_check                     false
% 2.57/1.01  --clausify_out                          false
% 2.57/1.01  --sig_cnt_out                           false
% 2.57/1.01  --trig_cnt_out                          false
% 2.57/1.01  --trig_cnt_out_tolerance                1.
% 2.57/1.01  --trig_cnt_out_sk_spl                   false
% 2.57/1.01  --abstr_cl_out                          false
% 2.57/1.01  
% 2.57/1.01  ------ Global Options
% 2.57/1.01  
% 2.57/1.01  --schedule                              default
% 2.57/1.01  --add_important_lit                     false
% 2.57/1.01  --prop_solver_per_cl                    1000
% 2.57/1.01  --min_unsat_core                        false
% 2.57/1.01  --soft_assumptions                      false
% 2.57/1.01  --soft_lemma_size                       3
% 2.57/1.01  --prop_impl_unit_size                   0
% 2.57/1.01  --prop_impl_unit                        []
% 2.57/1.01  --share_sel_clauses                     true
% 2.57/1.01  --reset_solvers                         false
% 2.57/1.01  --bc_imp_inh                            [conj_cone]
% 2.57/1.01  --conj_cone_tolerance                   3.
% 2.57/1.01  --extra_neg_conj                        none
% 2.57/1.01  --large_theory_mode                     true
% 2.57/1.01  --prolific_symb_bound                   200
% 2.57/1.01  --lt_threshold                          2000
% 2.57/1.01  --clause_weak_htbl                      true
% 2.57/1.01  --gc_record_bc_elim                     false
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing Options
% 2.57/1.01  
% 2.57/1.01  --preprocessing_flag                    true
% 2.57/1.01  --time_out_prep_mult                    0.1
% 2.57/1.01  --splitting_mode                        input
% 2.57/1.01  --splitting_grd                         true
% 2.57/1.01  --splitting_cvd                         false
% 2.57/1.01  --splitting_cvd_svl                     false
% 2.57/1.01  --splitting_nvd                         32
% 2.57/1.01  --sub_typing                            true
% 2.57/1.01  --prep_gs_sim                           true
% 2.57/1.01  --prep_unflatten                        true
% 2.57/1.01  --prep_res_sim                          true
% 2.57/1.01  --prep_upred                            true
% 2.57/1.01  --prep_sem_filter                       exhaustive
% 2.57/1.01  --prep_sem_filter_out                   false
% 2.57/1.01  --pred_elim                             true
% 2.57/1.01  --res_sim_input                         true
% 2.57/1.01  --eq_ax_congr_red                       true
% 2.57/1.01  --pure_diseq_elim                       true
% 2.57/1.01  --brand_transform                       false
% 2.57/1.01  --non_eq_to_eq                          false
% 2.57/1.01  --prep_def_merge                        true
% 2.57/1.01  --prep_def_merge_prop_impl              false
% 2.57/1.01  --prep_def_merge_mbd                    true
% 2.57/1.01  --prep_def_merge_tr_red                 false
% 2.57/1.01  --prep_def_merge_tr_cl                  false
% 2.57/1.01  --smt_preprocessing                     true
% 2.57/1.01  --smt_ac_axioms                         fast
% 2.57/1.01  --preprocessed_out                      false
% 2.57/1.01  --preprocessed_stats                    false
% 2.57/1.01  
% 2.57/1.01  ------ Abstraction refinement Options
% 2.57/1.01  
% 2.57/1.01  --abstr_ref                             []
% 2.57/1.01  --abstr_ref_prep                        false
% 2.57/1.01  --abstr_ref_until_sat                   false
% 2.57/1.01  --abstr_ref_sig_restrict                funpre
% 2.57/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.01  --abstr_ref_under                       []
% 2.57/1.01  
% 2.57/1.01  ------ SAT Options
% 2.57/1.01  
% 2.57/1.01  --sat_mode                              false
% 2.57/1.01  --sat_fm_restart_options                ""
% 2.57/1.01  --sat_gr_def                            false
% 2.57/1.01  --sat_epr_types                         true
% 2.57/1.01  --sat_non_cyclic_types                  false
% 2.57/1.01  --sat_finite_models                     false
% 2.57/1.01  --sat_fm_lemmas                         false
% 2.57/1.01  --sat_fm_prep                           false
% 2.57/1.01  --sat_fm_uc_incr                        true
% 2.57/1.01  --sat_out_model                         small
% 2.57/1.01  --sat_out_clauses                       false
% 2.57/1.01  
% 2.57/1.01  ------ QBF Options
% 2.57/1.01  
% 2.57/1.01  --qbf_mode                              false
% 2.57/1.01  --qbf_elim_univ                         false
% 2.57/1.01  --qbf_dom_inst                          none
% 2.57/1.01  --qbf_dom_pre_inst                      false
% 2.57/1.01  --qbf_sk_in                             false
% 2.57/1.01  --qbf_pred_elim                         true
% 2.57/1.01  --qbf_split                             512
% 2.57/1.01  
% 2.57/1.01  ------ BMC1 Options
% 2.57/1.01  
% 2.57/1.01  --bmc1_incremental                      false
% 2.57/1.01  --bmc1_axioms                           reachable_all
% 2.57/1.01  --bmc1_min_bound                        0
% 2.57/1.01  --bmc1_max_bound                        -1
% 2.57/1.01  --bmc1_max_bound_default                -1
% 2.57/1.01  --bmc1_symbol_reachability              true
% 2.57/1.01  --bmc1_property_lemmas                  false
% 2.57/1.01  --bmc1_k_induction                      false
% 2.57/1.01  --bmc1_non_equiv_states                 false
% 2.57/1.01  --bmc1_deadlock                         false
% 2.57/1.01  --bmc1_ucm                              false
% 2.57/1.01  --bmc1_add_unsat_core                   none
% 2.57/1.01  --bmc1_unsat_core_children              false
% 2.57/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.01  --bmc1_out_stat                         full
% 2.57/1.01  --bmc1_ground_init                      false
% 2.57/1.01  --bmc1_pre_inst_next_state              false
% 2.57/1.01  --bmc1_pre_inst_state                   false
% 2.57/1.01  --bmc1_pre_inst_reach_state             false
% 2.57/1.01  --bmc1_out_unsat_core                   false
% 2.57/1.01  --bmc1_aig_witness_out                  false
% 2.57/1.01  --bmc1_verbose                          false
% 2.57/1.01  --bmc1_dump_clauses_tptp                false
% 2.57/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.01  --bmc1_dump_file                        -
% 2.57/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.01  --bmc1_ucm_extend_mode                  1
% 2.57/1.01  --bmc1_ucm_init_mode                    2
% 2.57/1.01  --bmc1_ucm_cone_mode                    none
% 2.57/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.01  --bmc1_ucm_relax_model                  4
% 2.57/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.01  --bmc1_ucm_layered_model                none
% 2.57/1.01  --bmc1_ucm_max_lemma_size               10
% 2.57/1.01  
% 2.57/1.01  ------ AIG Options
% 2.57/1.01  
% 2.57/1.01  --aig_mode                              false
% 2.57/1.01  
% 2.57/1.01  ------ Instantiation Options
% 2.57/1.01  
% 2.57/1.01  --instantiation_flag                    true
% 2.57/1.01  --inst_sos_flag                         false
% 2.57/1.01  --inst_sos_phase                        true
% 2.57/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel_side                     num_symb
% 2.57/1.01  --inst_solver_per_active                1400
% 2.57/1.01  --inst_solver_calls_frac                1.
% 2.57/1.01  --inst_passive_queue_type               priority_queues
% 2.57/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.01  --inst_passive_queues_freq              [25;2]
% 2.57/1.01  --inst_dismatching                      true
% 2.57/1.01  --inst_eager_unprocessed_to_passive     true
% 2.57/1.01  --inst_prop_sim_given                   true
% 2.57/1.01  --inst_prop_sim_new                     false
% 2.57/1.01  --inst_subs_new                         false
% 2.57/1.01  --inst_eq_res_simp                      false
% 2.57/1.01  --inst_subs_given                       false
% 2.57/1.01  --inst_orphan_elimination               true
% 2.57/1.01  --inst_learning_loop_flag               true
% 2.57/1.01  --inst_learning_start                   3000
% 2.57/1.01  --inst_learning_factor                  2
% 2.57/1.01  --inst_start_prop_sim_after_learn       3
% 2.57/1.01  --inst_sel_renew                        solver
% 2.57/1.01  --inst_lit_activity_flag                true
% 2.57/1.01  --inst_restr_to_given                   false
% 2.57/1.01  --inst_activity_threshold               500
% 2.57/1.01  --inst_out_proof                        true
% 2.57/1.01  
% 2.57/1.01  ------ Resolution Options
% 2.57/1.01  
% 2.57/1.01  --resolution_flag                       true
% 2.57/1.01  --res_lit_sel                           adaptive
% 2.57/1.01  --res_lit_sel_side                      none
% 2.57/1.01  --res_ordering                          kbo
% 2.57/1.01  --res_to_prop_solver                    active
% 2.57/1.01  --res_prop_simpl_new                    false
% 2.57/1.01  --res_prop_simpl_given                  true
% 2.57/1.01  --res_passive_queue_type                priority_queues
% 2.57/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.01  --res_passive_queues_freq               [15;5]
% 2.57/1.01  --res_forward_subs                      full
% 2.57/1.01  --res_backward_subs                     full
% 2.57/1.01  --res_forward_subs_resolution           true
% 2.57/1.01  --res_backward_subs_resolution          true
% 2.57/1.01  --res_orphan_elimination                true
% 2.57/1.01  --res_time_limit                        2.
% 2.57/1.01  --res_out_proof                         true
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Options
% 2.57/1.01  
% 2.57/1.01  --superposition_flag                    true
% 2.57/1.01  --sup_passive_queue_type                priority_queues
% 2.57/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.01  --demod_completeness_check              fast
% 2.57/1.01  --demod_use_ground                      true
% 2.57/1.01  --sup_to_prop_solver                    passive
% 2.57/1.01  --sup_prop_simpl_new                    true
% 2.57/1.01  --sup_prop_simpl_given                  true
% 2.57/1.01  --sup_fun_splitting                     false
% 2.57/1.01  --sup_smt_interval                      50000
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Simplification Setup
% 2.57/1.01  
% 2.57/1.01  --sup_indices_passive                   []
% 2.57/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_full_bw                           [BwDemod]
% 2.57/1.01  --sup_immed_triv                        [TrivRules]
% 2.57/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_immed_bw_main                     []
% 2.57/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  
% 2.57/1.01  ------ Combination Options
% 2.57/1.01  
% 2.57/1.01  --comb_res_mult                         3
% 2.57/1.01  --comb_sup_mult                         2
% 2.57/1.01  --comb_inst_mult                        10
% 2.57/1.01  
% 2.57/1.01  ------ Debug Options
% 2.57/1.01  
% 2.57/1.01  --dbg_backtrace                         false
% 2.57/1.01  --dbg_dump_prop_clauses                 false
% 2.57/1.01  --dbg_dump_prop_clauses_file            -
% 2.57/1.01  --dbg_out_stat                          false
% 2.57/1.01  ------ Parsing...
% 2.57/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/1.01  ------ Proving...
% 2.57/1.01  ------ Problem Properties 
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  clauses                                 28
% 2.57/1.01  conjectures                             10
% 2.57/1.01  EPR                                     8
% 2.57/1.01  Horn                                    21
% 2.57/1.01  unary                                   11
% 2.57/1.01  binary                                  6
% 2.57/1.01  lits                                    72
% 2.57/1.01  lits eq                                 19
% 2.57/1.01  fd_pure                                 0
% 2.57/1.01  fd_pseudo                               0
% 2.57/1.01  fd_cond                                 5
% 2.57/1.01  fd_pseudo_cond                          0
% 2.57/1.01  AC symbols                              0
% 2.57/1.01  
% 2.57/1.01  ------ Schedule dynamic 5 is on 
% 2.57/1.01  
% 2.57/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  ------ 
% 2.57/1.01  Current options:
% 2.57/1.01  ------ 
% 2.57/1.01  
% 2.57/1.01  ------ Input Options
% 2.57/1.01  
% 2.57/1.01  --out_options                           all
% 2.57/1.01  --tptp_safe_out                         true
% 2.57/1.01  --problem_path                          ""
% 2.57/1.01  --include_path                          ""
% 2.57/1.01  --clausifier                            res/vclausify_rel
% 2.57/1.01  --clausifier_options                    --mode clausify
% 2.57/1.01  --stdin                                 false
% 2.57/1.01  --stats_out                             all
% 2.57/1.01  
% 2.57/1.01  ------ General Options
% 2.57/1.01  
% 2.57/1.01  --fof                                   false
% 2.57/1.01  --time_out_real                         305.
% 2.57/1.01  --time_out_virtual                      -1.
% 2.57/1.01  --symbol_type_check                     false
% 2.57/1.01  --clausify_out                          false
% 2.57/1.01  --sig_cnt_out                           false
% 2.57/1.01  --trig_cnt_out                          false
% 2.57/1.01  --trig_cnt_out_tolerance                1.
% 2.57/1.01  --trig_cnt_out_sk_spl                   false
% 2.57/1.01  --abstr_cl_out                          false
% 2.57/1.01  
% 2.57/1.01  ------ Global Options
% 2.57/1.01  
% 2.57/1.01  --schedule                              default
% 2.57/1.01  --add_important_lit                     false
% 2.57/1.01  --prop_solver_per_cl                    1000
% 2.57/1.01  --min_unsat_core                        false
% 2.57/1.01  --soft_assumptions                      false
% 2.57/1.01  --soft_lemma_size                       3
% 2.57/1.01  --prop_impl_unit_size                   0
% 2.57/1.01  --prop_impl_unit                        []
% 2.57/1.01  --share_sel_clauses                     true
% 2.57/1.01  --reset_solvers                         false
% 2.57/1.01  --bc_imp_inh                            [conj_cone]
% 2.57/1.01  --conj_cone_tolerance                   3.
% 2.57/1.01  --extra_neg_conj                        none
% 2.57/1.01  --large_theory_mode                     true
% 2.57/1.01  --prolific_symb_bound                   200
% 2.57/1.01  --lt_threshold                          2000
% 2.57/1.01  --clause_weak_htbl                      true
% 2.57/1.01  --gc_record_bc_elim                     false
% 2.57/1.01  
% 2.57/1.01  ------ Preprocessing Options
% 2.57/1.01  
% 2.57/1.01  --preprocessing_flag                    true
% 2.57/1.01  --time_out_prep_mult                    0.1
% 2.57/1.01  --splitting_mode                        input
% 2.57/1.01  --splitting_grd                         true
% 2.57/1.01  --splitting_cvd                         false
% 2.57/1.01  --splitting_cvd_svl                     false
% 2.57/1.01  --splitting_nvd                         32
% 2.57/1.01  --sub_typing                            true
% 2.57/1.01  --prep_gs_sim                           true
% 2.57/1.01  --prep_unflatten                        true
% 2.57/1.01  --prep_res_sim                          true
% 2.57/1.01  --prep_upred                            true
% 2.57/1.01  --prep_sem_filter                       exhaustive
% 2.57/1.01  --prep_sem_filter_out                   false
% 2.57/1.01  --pred_elim                             true
% 2.57/1.01  --res_sim_input                         true
% 2.57/1.01  --eq_ax_congr_red                       true
% 2.57/1.01  --pure_diseq_elim                       true
% 2.57/1.01  --brand_transform                       false
% 2.57/1.01  --non_eq_to_eq                          false
% 2.57/1.01  --prep_def_merge                        true
% 2.57/1.01  --prep_def_merge_prop_impl              false
% 2.57/1.01  --prep_def_merge_mbd                    true
% 2.57/1.01  --prep_def_merge_tr_red                 false
% 2.57/1.01  --prep_def_merge_tr_cl                  false
% 2.57/1.01  --smt_preprocessing                     true
% 2.57/1.01  --smt_ac_axioms                         fast
% 2.57/1.01  --preprocessed_out                      false
% 2.57/1.01  --preprocessed_stats                    false
% 2.57/1.01  
% 2.57/1.01  ------ Abstraction refinement Options
% 2.57/1.01  
% 2.57/1.01  --abstr_ref                             []
% 2.57/1.01  --abstr_ref_prep                        false
% 2.57/1.01  --abstr_ref_until_sat                   false
% 2.57/1.01  --abstr_ref_sig_restrict                funpre
% 2.57/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.01  --abstr_ref_under                       []
% 2.57/1.01  
% 2.57/1.01  ------ SAT Options
% 2.57/1.01  
% 2.57/1.01  --sat_mode                              false
% 2.57/1.01  --sat_fm_restart_options                ""
% 2.57/1.01  --sat_gr_def                            false
% 2.57/1.01  --sat_epr_types                         true
% 2.57/1.01  --sat_non_cyclic_types                  false
% 2.57/1.01  --sat_finite_models                     false
% 2.57/1.01  --sat_fm_lemmas                         false
% 2.57/1.01  --sat_fm_prep                           false
% 2.57/1.01  --sat_fm_uc_incr                        true
% 2.57/1.01  --sat_out_model                         small
% 2.57/1.01  --sat_out_clauses                       false
% 2.57/1.01  
% 2.57/1.01  ------ QBF Options
% 2.57/1.01  
% 2.57/1.01  --qbf_mode                              false
% 2.57/1.01  --qbf_elim_univ                         false
% 2.57/1.01  --qbf_dom_inst                          none
% 2.57/1.01  --qbf_dom_pre_inst                      false
% 2.57/1.01  --qbf_sk_in                             false
% 2.57/1.01  --qbf_pred_elim                         true
% 2.57/1.01  --qbf_split                             512
% 2.57/1.01  
% 2.57/1.01  ------ BMC1 Options
% 2.57/1.01  
% 2.57/1.01  --bmc1_incremental                      false
% 2.57/1.01  --bmc1_axioms                           reachable_all
% 2.57/1.01  --bmc1_min_bound                        0
% 2.57/1.01  --bmc1_max_bound                        -1
% 2.57/1.01  --bmc1_max_bound_default                -1
% 2.57/1.01  --bmc1_symbol_reachability              true
% 2.57/1.01  --bmc1_property_lemmas                  false
% 2.57/1.01  --bmc1_k_induction                      false
% 2.57/1.01  --bmc1_non_equiv_states                 false
% 2.57/1.01  --bmc1_deadlock                         false
% 2.57/1.01  --bmc1_ucm                              false
% 2.57/1.01  --bmc1_add_unsat_core                   none
% 2.57/1.01  --bmc1_unsat_core_children              false
% 2.57/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.01  --bmc1_out_stat                         full
% 2.57/1.01  --bmc1_ground_init                      false
% 2.57/1.01  --bmc1_pre_inst_next_state              false
% 2.57/1.01  --bmc1_pre_inst_state                   false
% 2.57/1.01  --bmc1_pre_inst_reach_state             false
% 2.57/1.01  --bmc1_out_unsat_core                   false
% 2.57/1.01  --bmc1_aig_witness_out                  false
% 2.57/1.01  --bmc1_verbose                          false
% 2.57/1.01  --bmc1_dump_clauses_tptp                false
% 2.57/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.01  --bmc1_dump_file                        -
% 2.57/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.01  --bmc1_ucm_extend_mode                  1
% 2.57/1.01  --bmc1_ucm_init_mode                    2
% 2.57/1.01  --bmc1_ucm_cone_mode                    none
% 2.57/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.01  --bmc1_ucm_relax_model                  4
% 2.57/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.01  --bmc1_ucm_layered_model                none
% 2.57/1.01  --bmc1_ucm_max_lemma_size               10
% 2.57/1.01  
% 2.57/1.01  ------ AIG Options
% 2.57/1.01  
% 2.57/1.01  --aig_mode                              false
% 2.57/1.01  
% 2.57/1.01  ------ Instantiation Options
% 2.57/1.01  
% 2.57/1.01  --instantiation_flag                    true
% 2.57/1.01  --inst_sos_flag                         false
% 2.57/1.01  --inst_sos_phase                        true
% 2.57/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.01  --inst_lit_sel_side                     none
% 2.57/1.01  --inst_solver_per_active                1400
% 2.57/1.01  --inst_solver_calls_frac                1.
% 2.57/1.01  --inst_passive_queue_type               priority_queues
% 2.57/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.01  --inst_passive_queues_freq              [25;2]
% 2.57/1.01  --inst_dismatching                      true
% 2.57/1.01  --inst_eager_unprocessed_to_passive     true
% 2.57/1.01  --inst_prop_sim_given                   true
% 2.57/1.01  --inst_prop_sim_new                     false
% 2.57/1.01  --inst_subs_new                         false
% 2.57/1.01  --inst_eq_res_simp                      false
% 2.57/1.01  --inst_subs_given                       false
% 2.57/1.01  --inst_orphan_elimination               true
% 2.57/1.01  --inst_learning_loop_flag               true
% 2.57/1.01  --inst_learning_start                   3000
% 2.57/1.01  --inst_learning_factor                  2
% 2.57/1.01  --inst_start_prop_sim_after_learn       3
% 2.57/1.01  --inst_sel_renew                        solver
% 2.57/1.01  --inst_lit_activity_flag                true
% 2.57/1.01  --inst_restr_to_given                   false
% 2.57/1.01  --inst_activity_threshold               500
% 2.57/1.01  --inst_out_proof                        true
% 2.57/1.01  
% 2.57/1.01  ------ Resolution Options
% 2.57/1.01  
% 2.57/1.01  --resolution_flag                       false
% 2.57/1.01  --res_lit_sel                           adaptive
% 2.57/1.01  --res_lit_sel_side                      none
% 2.57/1.01  --res_ordering                          kbo
% 2.57/1.01  --res_to_prop_solver                    active
% 2.57/1.01  --res_prop_simpl_new                    false
% 2.57/1.01  --res_prop_simpl_given                  true
% 2.57/1.01  --res_passive_queue_type                priority_queues
% 2.57/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.01  --res_passive_queues_freq               [15;5]
% 2.57/1.01  --res_forward_subs                      full
% 2.57/1.01  --res_backward_subs                     full
% 2.57/1.01  --res_forward_subs_resolution           true
% 2.57/1.01  --res_backward_subs_resolution          true
% 2.57/1.01  --res_orphan_elimination                true
% 2.57/1.01  --res_time_limit                        2.
% 2.57/1.01  --res_out_proof                         true
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Options
% 2.57/1.01  
% 2.57/1.01  --superposition_flag                    true
% 2.57/1.01  --sup_passive_queue_type                priority_queues
% 2.57/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.01  --demod_completeness_check              fast
% 2.57/1.01  --demod_use_ground                      true
% 2.57/1.01  --sup_to_prop_solver                    passive
% 2.57/1.01  --sup_prop_simpl_new                    true
% 2.57/1.01  --sup_prop_simpl_given                  true
% 2.57/1.01  --sup_fun_splitting                     false
% 2.57/1.01  --sup_smt_interval                      50000
% 2.57/1.01  
% 2.57/1.01  ------ Superposition Simplification Setup
% 2.57/1.01  
% 2.57/1.01  --sup_indices_passive                   []
% 2.57/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_full_bw                           [BwDemod]
% 2.57/1.01  --sup_immed_triv                        [TrivRules]
% 2.57/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_immed_bw_main                     []
% 2.57/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.01  
% 2.57/1.01  ------ Combination Options
% 2.57/1.01  
% 2.57/1.01  --comb_res_mult                         3
% 2.57/1.01  --comb_sup_mult                         2
% 2.57/1.01  --comb_inst_mult                        10
% 2.57/1.01  
% 2.57/1.01  ------ Debug Options
% 2.57/1.01  
% 2.57/1.01  --dbg_backtrace                         false
% 2.57/1.01  --dbg_dump_prop_clauses                 false
% 2.57/1.01  --dbg_dump_prop_clauses_file            -
% 2.57/1.01  --dbg_out_stat                          false
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  ------ Proving...
% 2.57/1.01  
% 2.57/1.01  
% 2.57/1.01  % SZS status Theorem for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/1.01  
% 2.57/1.01  fof(f15,conjecture,(
% 2.57/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f16,negated_conjecture,(
% 2.57/1.01    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 2.57/1.01    inference(negated_conjecture,[],[f15])).
% 2.57/1.01  
% 2.57/1.01  fof(f37,plain,(
% 2.57/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 2.57/1.01    inference(ennf_transformation,[],[f16])).
% 2.57/1.01  
% 2.57/1.01  fof(f38,plain,(
% 2.57/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 2.57/1.01    inference(flattening,[],[f37])).
% 2.57/1.01  
% 2.57/1.01  fof(f44,plain,(
% 2.57/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f43,plain,(
% 2.57/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f42,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f41,plain,(
% 2.57/1.01    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 2.57/1.01    introduced(choice_axiom,[])).
% 2.57/1.01  
% 2.57/1.01  fof(f45,plain,(
% 2.57/1.01    (((k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 2.57/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f44,f43,f42,f41])).
% 2.57/1.01  
% 2.57/1.01  fof(f71,plain,(
% 2.57/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f9,axiom,(
% 2.57/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f27,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.01    inference(ennf_transformation,[],[f9])).
% 2.57/1.01  
% 2.57/1.01  fof(f55,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f27])).
% 2.57/1.01  
% 2.57/1.01  fof(f74,plain,(
% 2.57/1.01    m1_subset_1(sK5,sK1)),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f13,axiom,(
% 2.57/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f33,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.01    inference(ennf_transformation,[],[f13])).
% 2.57/1.01  
% 2.57/1.01  fof(f34,plain,(
% 2.57/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.01    inference(flattening,[],[f33])).
% 2.57/1.01  
% 2.57/1.01  fof(f40,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.01    inference(nnf_transformation,[],[f34])).
% 2.57/1.01  
% 2.57/1.01  fof(f61,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f40])).
% 2.57/1.01  
% 2.57/1.01  fof(f10,axiom,(
% 2.57/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f28,plain,(
% 2.57/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.01    inference(ennf_transformation,[],[f10])).
% 2.57/1.01  
% 2.57/1.01  fof(f56,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f28])).
% 2.57/1.01  
% 2.57/1.01  fof(f70,plain,(
% 2.57/1.01    v1_funct_2(sK3,sK1,sK2)),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f5,axiom,(
% 2.57/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f22,plain,(
% 2.57/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.57/1.01    inference(ennf_transformation,[],[f5])).
% 2.57/1.01  
% 2.57/1.01  fof(f23,plain,(
% 2.57/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.57/1.01    inference(flattening,[],[f22])).
% 2.57/1.01  
% 2.57/1.01  fof(f50,plain,(
% 2.57/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f23])).
% 2.57/1.01  
% 2.57/1.01  fof(f8,axiom,(
% 2.57/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f25,plain,(
% 2.57/1.01    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.57/1.01    inference(ennf_transformation,[],[f8])).
% 2.57/1.01  
% 2.57/1.01  fof(f26,plain,(
% 2.57/1.01    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.57/1.01    inference(flattening,[],[f25])).
% 2.57/1.01  
% 2.57/1.01  fof(f54,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f26])).
% 2.57/1.01  
% 2.57/1.01  fof(f69,plain,(
% 2.57/1.01    v1_funct_1(sK3)),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f76,plain,(
% 2.57/1.01    k1_xboole_0 != sK1),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f1,axiom,(
% 2.57/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f18,plain,(
% 2.57/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.57/1.01    inference(ennf_transformation,[],[f1])).
% 2.57/1.01  
% 2.57/1.01  fof(f46,plain,(
% 2.57/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f18])).
% 2.57/1.01  
% 2.57/1.01  fof(f73,plain,(
% 2.57/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f72,plain,(
% 2.57/1.01    v1_funct_1(sK4)),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f75,plain,(
% 2.57/1.01    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f12,axiom,(
% 2.57/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f31,plain,(
% 2.57/1.01    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.57/1.01    inference(ennf_transformation,[],[f12])).
% 2.57/1.01  
% 2.57/1.01  fof(f32,plain,(
% 2.57/1.01    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.57/1.01    inference(flattening,[],[f31])).
% 2.57/1.01  
% 2.57/1.01  fof(f60,plain,(
% 2.57/1.01    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f32])).
% 2.57/1.01  
% 2.57/1.01  fof(f14,axiom,(
% 2.57/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f35,plain,(
% 2.57/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.57/1.01    inference(ennf_transformation,[],[f14])).
% 2.57/1.01  
% 2.57/1.01  fof(f36,plain,(
% 2.57/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.57/1.01    inference(flattening,[],[f35])).
% 2.57/1.01  
% 2.57/1.01  fof(f67,plain,(
% 2.57/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f36])).
% 2.57/1.01  
% 2.57/1.01  fof(f77,plain,(
% 2.57/1.01    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5)),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  fof(f6,axiom,(
% 2.57/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f39,plain,(
% 2.57/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.57/1.01    inference(nnf_transformation,[],[f6])).
% 2.57/1.01  
% 2.57/1.01  fof(f51,plain,(
% 2.57/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f39])).
% 2.57/1.01  
% 2.57/1.01  fof(f65,plain,(
% 2.57/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.01    inference(cnf_transformation,[],[f40])).
% 2.57/1.01  
% 2.57/1.01  fof(f80,plain,(
% 2.57/1.01    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.57/1.01    inference(equality_resolution,[],[f65])).
% 2.57/1.01  
% 2.57/1.01  fof(f2,axiom,(
% 2.57/1.01    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f47,plain,(
% 2.57/1.01    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f2])).
% 2.57/1.01  
% 2.57/1.01  fof(f4,axiom,(
% 2.57/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f17,plain,(
% 2.57/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 2.57/1.01    inference(unused_predicate_definition_removal,[],[f4])).
% 2.57/1.01  
% 2.57/1.01  fof(f21,plain,(
% 2.57/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 2.57/1.01    inference(ennf_transformation,[],[f17])).
% 2.57/1.01  
% 2.57/1.01  fof(f49,plain,(
% 2.57/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.57/1.01    inference(cnf_transformation,[],[f21])).
% 2.57/1.01  
% 2.57/1.01  fof(f3,axiom,(
% 2.57/1.01    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.57/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.01  
% 2.57/1.01  fof(f19,plain,(
% 2.57/1.01    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.57/1.01    inference(ennf_transformation,[],[f3])).
% 2.57/1.01  
% 2.57/1.01  fof(f20,plain,(
% 2.57/1.01    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.57/1.01    inference(flattening,[],[f19])).
% 2.57/1.01  
% 2.57/1.01  fof(f48,plain,(
% 2.57/1.01    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.57/1.01    inference(cnf_transformation,[],[f20])).
% 2.57/1.01  
% 2.57/1.01  fof(f68,plain,(
% 2.57/1.01    ~v1_xboole_0(sK2)),
% 2.57/1.01    inference(cnf_transformation,[],[f45])).
% 2.57/1.01  
% 2.57/1.01  cnf(c_28,negated_conjecture,
% 2.57/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.57/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2003,plain,
% 2.57/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_9,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | v1_relat_1(X0) ),
% 2.57/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2017,plain,
% 2.57/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.57/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2756,plain,
% 2.57/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2003,c_2017]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_25,negated_conjecture,
% 2.57/1.01      ( m1_subset_1(sK5,sK1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2006,plain,
% 2.57/1.01      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_20,plain,
% 2.57/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.57/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.57/1.01      | k1_xboole_0 = X2 ),
% 2.57/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2009,plain,
% 2.57/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 2.57/1.01      | k1_xboole_0 = X1
% 2.57/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3566,plain,
% 2.57/1.01      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2003,c_2009]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_10,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.57/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2016,plain,
% 2.57/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2914,plain,
% 2.57/1.01      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2003,c_2016]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3570,plain,
% 2.57/1.01      ( k1_relat_1(sK3) = sK1
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 2.57/1.01      inference(demodulation,[status(thm)],[c_3566,c_2914]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_29,negated_conjecture,
% 2.57/1.01      ( v1_funct_2(sK3,sK1,sK2) ),
% 2.57/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_34,plain,
% 2.57/1.01      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4469,plain,
% 2.57/1.01      ( sK2 = k1_xboole_0 | k1_relat_1(sK3) = sK1 ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_3570,c_34]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4470,plain,
% 2.57/1.01      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.57/1.01      inference(renaming,[status(thm)],[c_4469]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_8,plain,
% 2.57/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.57/1.01      | ~ v1_relat_1(X2)
% 2.57/1.01      | ~ v1_relat_1(X1)
% 2.57/1.01      | ~ v1_funct_1(X2)
% 2.57/1.01      | ~ v1_funct_1(X1)
% 2.57/1.01      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 2.57/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_399,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,X1)
% 2.57/1.01      | ~ v1_relat_1(X2)
% 2.57/1.01      | ~ v1_relat_1(X3)
% 2.57/1.01      | ~ v1_funct_1(X2)
% 2.57/1.01      | ~ v1_funct_1(X3)
% 2.57/1.01      | v1_xboole_0(X1)
% 2.57/1.01      | X4 != X0
% 2.57/1.01      | k1_funct_1(X2,k1_funct_1(X3,X4)) = k1_funct_1(k5_relat_1(X3,X2),X4)
% 2.57/1.01      | k1_relat_1(X3) != X1 ),
% 2.57/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_400,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_relat_1(X1))
% 2.57/1.01      | ~ v1_relat_1(X2)
% 2.57/1.01      | ~ v1_relat_1(X1)
% 2.57/1.01      | ~ v1_funct_1(X2)
% 2.57/1.01      | ~ v1_funct_1(X1)
% 2.57/1.01      | v1_xboole_0(k1_relat_1(X1))
% 2.57/1.01      | k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ),
% 2.57/1.01      inference(unflattening,[status(thm)],[c_399]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1997,plain,
% 2.57/1.01      ( k1_funct_1(X0,k1_funct_1(X1,X2)) = k1_funct_1(k5_relat_1(X1,X0),X2)
% 2.57/1.01      | m1_subset_1(X2,k1_relat_1(X1)) != iProver_top
% 2.57/1.01      | v1_relat_1(X0) != iProver_top
% 2.57/1.01      | v1_relat_1(X1) != iProver_top
% 2.57/1.01      | v1_funct_1(X0) != iProver_top
% 2.57/1.01      | v1_funct_1(X1) != iProver_top
% 2.57/1.01      | v1_xboole_0(k1_relat_1(X1)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4473,plain,
% 2.57/1.01      ( k1_funct_1(k5_relat_1(sK3,X0),X1) = k1_funct_1(X0,k1_funct_1(sK3,X1))
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | m1_subset_1(X1,sK1) != iProver_top
% 2.57/1.01      | v1_relat_1(X0) != iProver_top
% 2.57/1.01      | v1_relat_1(sK3) != iProver_top
% 2.57/1.01      | v1_funct_1(X0) != iProver_top
% 2.57/1.01      | v1_funct_1(sK3) != iProver_top
% 2.57/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_4470,c_1997]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_30,negated_conjecture,
% 2.57/1.01      ( v1_funct_1(sK3) ),
% 2.57/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_33,plain,
% 2.57/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_35,plain,
% 2.57/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2241,plain,
% 2.57/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.57/1.01      | v1_relat_1(sK3) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2242,plain,
% 2.57/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.57/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_2241]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4686,plain,
% 2.57/1.01      ( v1_funct_1(X0) != iProver_top
% 2.57/1.01      | k1_funct_1(k5_relat_1(sK3,X0),X1) = k1_funct_1(X0,k1_funct_1(sK3,X1))
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | m1_subset_1(X1,sK1) != iProver_top
% 2.57/1.01      | v1_relat_1(X0) != iProver_top
% 2.57/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_4473,c_33,c_35,c_2242]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4687,plain,
% 2.57/1.01      ( k1_funct_1(k5_relat_1(sK3,X0),X1) = k1_funct_1(X0,k1_funct_1(sK3,X1))
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | m1_subset_1(X1,sK1) != iProver_top
% 2.57/1.01      | v1_relat_1(X0) != iProver_top
% 2.57/1.01      | v1_funct_1(X0) != iProver_top
% 2.57/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.57/1.01      inference(renaming,[status(thm)],[c_4686]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4698,plain,
% 2.57/1.01      ( k1_funct_1(X0,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,X0),sK5)
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_relat_1(X0) != iProver_top
% 2.57/1.01      | v1_funct_1(X0) != iProver_top
% 2.57/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2006,c_4687]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4789,plain,
% 2.57/1.01      ( k1_funct_1(k5_relat_1(sK3,sK3),sK5) = k1_funct_1(sK3,k1_funct_1(sK3,sK5))
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_1(sK3) != iProver_top
% 2.57/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2756,c_4698]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_23,negated_conjecture,
% 2.57/1.01      ( k1_xboole_0 != sK1 ),
% 2.57/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_0,plain,
% 2.57/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2223,plain,
% 2.57/1.01      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2224,plain,
% 2.57/1.01      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_2223]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_26,negated_conjecture,
% 2.57/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 2.57/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2005,plain,
% 2.57/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2755,plain,
% 2.57/1.01      ( v1_relat_1(sK4) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2005,c_2017]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4788,plain,
% 2.57/1.01      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_1(sK4) != iProver_top
% 2.57/1.01      | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2755,c_4698]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_27,negated_conjecture,
% 2.57/1.01      ( v1_funct_1(sK4) ),
% 2.57/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_36,plain,
% 2.57/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2913,plain,
% 2.57/1.01      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2005,c_2016]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_24,negated_conjecture,
% 2.57/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 2.57/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2007,plain,
% 2.57/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3078,plain,
% 2.57/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) = iProver_top ),
% 2.57/1.01      inference(demodulation,[status(thm)],[c_2913,c_2007]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_14,plain,
% 2.57/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.57/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 2.57/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 2.57/1.01      | ~ v1_funct_1(X3)
% 2.57/1.01      | ~ v1_funct_1(X0)
% 2.57/1.01      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 2.57/1.01      | k1_xboole_0 = X2 ),
% 2.57/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2015,plain,
% 2.57/1.01      ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
% 2.57/1.01      | k1_xboole_0 = X1
% 2.57/1.01      | v1_funct_2(X3,X0,X1) != iProver_top
% 2.57/1.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.57/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.57/1.01      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 2.57/1.01      | v1_funct_1(X4) != iProver_top
% 2.57/1.01      | v1_funct_1(X3) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4325,plain,
% 2.57/1.01      ( k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) = k8_funct_2(X0,sK2,sK0,X1,sK4)
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(X1,X0,sK2) != iProver_top
% 2.57/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 2.57/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 2.57/1.01      | r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) != iProver_top
% 2.57/1.01      | v1_funct_1(X1) != iProver_top
% 2.57/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2913,c_2015]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_37,plain,
% 2.57/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4502,plain,
% 2.57/1.01      ( v1_funct_1(X1) != iProver_top
% 2.57/1.01      | r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) != iProver_top
% 2.57/1.01      | k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) = k8_funct_2(X0,sK2,sK0,X1,sK4)
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(X1,X0,sK2) != iProver_top
% 2.57/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_4325,c_36,c_37]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4503,plain,
% 2.57/1.01      ( k1_partfun1(X0,sK2,sK2,sK0,X1,sK4) = k8_funct_2(X0,sK2,sK0,X1,sK4)
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(X1,X0,sK2) != iProver_top
% 2.57/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 2.57/1.01      | r1_tarski(k2_relset_1(X0,sK2,X1),k1_relat_1(sK4)) != iProver_top
% 2.57/1.01      | v1_funct_1(X1) != iProver_top ),
% 2.57/1.01      inference(renaming,[status(thm)],[c_4502]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4514,plain,
% 2.57/1.01      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k8_funct_2(sK1,sK2,sK0,sK3,sK4)
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.57/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.57/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_3078,c_4503]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_21,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.57/1.01      | ~ v1_funct_1(X3)
% 2.57/1.01      | ~ v1_funct_1(X0)
% 2.57/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.57/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2008,plain,
% 2.57/1.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.57/1.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.57/1.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.57/1.01      | v1_funct_1(X4) != iProver_top
% 2.57/1.01      | v1_funct_1(X5) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3665,plain,
% 2.57/1.01      ( k1_partfun1(X0,X1,sK2,sK0,X2,sK4) = k5_relat_1(X2,sK4)
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.57/1.01      | v1_funct_1(X2) != iProver_top
% 2.57/1.01      | v1_funct_1(sK4) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2005,c_2008]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3839,plain,
% 2.57/1.01      ( v1_funct_1(X2) != iProver_top
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.57/1.01      | k1_partfun1(X0,X1,sK2,sK0,X2,sK4) = k5_relat_1(X2,sK4) ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_3665,c_36]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3840,plain,
% 2.57/1.01      ( k1_partfun1(X0,X1,sK2,sK0,X2,sK4) = k5_relat_1(X2,sK4)
% 2.57/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.57/1.01      | v1_funct_1(X2) != iProver_top ),
% 2.57/1.01      inference(renaming,[status(thm)],[c_3839]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3850,plain,
% 2.57/1.01      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 2.57/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2003,c_3840]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2315,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.57/1.01      | ~ v1_funct_1(X0)
% 2.57/1.01      | ~ v1_funct_1(sK3)
% 2.57/1.01      | k1_partfun1(X3,X4,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2542,plain,
% 2.57/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.57/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.57/1.01      | ~ v1_funct_1(sK3)
% 2.57/1.01      | ~ v1_funct_1(sK4)
% 2.57/1.01      | k1_partfun1(X0,X1,X2,X3,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_2315]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2717,plain,
% 2.57/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.57/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.57/1.01      | ~ v1_funct_1(sK3)
% 2.57/1.01      | ~ v1_funct_1(sK4)
% 2.57/1.01      | k1_partfun1(sK1,sK2,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_2542]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2903,plain,
% 2.57/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.57/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 2.57/1.01      | ~ v1_funct_1(sK3)
% 2.57/1.01      | ~ v1_funct_1(sK4)
% 2.57/1.01      | k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_2717]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_3957,plain,
% 2.57/1.01      ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_3850,c_30,c_28,c_27,c_26,c_2903]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4515,plain,
% 2.57/1.01      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 2.57/1.01      | sK2 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.57/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.57/1.01      | v1_funct_1(sK3) != iProver_top ),
% 2.57/1.01      inference(light_normalisation,[status(thm)],[c_4514,c_3957]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4518,plain,
% 2.57/1.01      ( sK2 = k1_xboole_0
% 2.57/1.01      | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_4515,c_33,c_34,c_35]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4519,plain,
% 2.57/1.01      ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
% 2.57/1.01      | sK2 = k1_xboole_0 ),
% 2.57/1.01      inference(renaming,[status(thm)],[c_4518]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_22,negated_conjecture,
% 2.57/1.01      ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) ),
% 2.57/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_4522,plain,
% 2.57/1.01      ( k1_funct_1(k5_relat_1(sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 2.57/1.01      | sK2 = k1_xboole_0 ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_4519,c_22]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5595,plain,
% 2.57/1.01      ( sK2 = k1_xboole_0 | v1_xboole_0(k1_relat_1(sK3)) = iProver_top ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_4788,c_36,c_4522]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5601,plain,
% 2.57/1.01      ( sK2 = k1_xboole_0 | v1_xboole_0(sK1) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_4470,c_5595]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5619,plain,
% 2.57/1.01      ( sK2 = k1_xboole_0 ),
% 2.57/1.01      inference(global_propositional_subsumption,
% 2.57/1.01                [status(thm)],
% 2.57/1.01                [c_4789,c_23,c_2224,c_5601]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_6,plain,
% 2.57/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.57/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2019,plain,
% 2.57/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.57/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2641,plain,
% 2.57/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_2003,c_2019]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5644,plain,
% 2.57/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 2.57/1.01      inference(demodulation,[status(thm)],[c_5619,c_2641]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5647,plain,
% 2.57/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 2.57/1.01      inference(demodulation,[status(thm)],[c_5619,c_2003]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_16,plain,
% 2.57/1.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.57/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.57/1.01      | k1_xboole_0 = X1
% 2.57/1.01      | k1_xboole_0 = X0 ),
% 2.57/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2013,plain,
% 2.57/1.01      ( k1_xboole_0 = X0
% 2.57/1.01      | k1_xboole_0 = X1
% 2.57/1.01      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 2.57/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 2.57/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_5890,plain,
% 2.57/1.01      ( sK1 = k1_xboole_0
% 2.57/1.01      | sK3 = k1_xboole_0
% 2.57/1.01      | v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top ),
% 2.57/1.01      inference(superposition,[status(thm)],[c_5647,c_2013]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1369,plain,( X0 = X0 ),theory(equality) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_1396,plain,
% 2.57/1.01      ( k1_xboole_0 = k1_xboole_0 ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_1369]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2474,plain,
% 2.57/1.01      ( sK1 = sK1 ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_1369]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2258,plain,
% 2.57/1.01      ( ~ v1_funct_2(X0,sK1,k1_xboole_0)
% 2.57/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.57/1.01      | k1_xboole_0 = X0
% 2.57/1.01      | k1_xboole_0 = sK1 ),
% 2.57/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.57/1.01  
% 2.57/1.01  cnf(c_2498,plain,
% 2.57/1.02      ( ~ v1_funct_2(sK3,sK1,k1_xboole_0)
% 2.57/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 2.57/1.02      | k1_xboole_0 = sK1
% 2.57/1.02      | k1_xboole_0 = sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_2258]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2503,plain,
% 2.57/1.02      ( k1_xboole_0 = sK1
% 2.57/1.02      | k1_xboole_0 = sK3
% 2.57/1.02      | v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top
% 2.57/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_2498]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2508,plain,
% 2.57/1.02      ( sK3 = sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_1369]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_1370,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2530,plain,
% 2.57/1.02      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_1370]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2531,plain,
% 2.57/1.02      ( sK2 != k1_xboole_0
% 2.57/1.02      | k1_xboole_0 = sK2
% 2.57/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_2530]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2653,plain,
% 2.57/1.02      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_1370]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3430,plain,
% 2.57/1.02      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_2653]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3431,plain,
% 2.57/1.02      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_3430]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_1380,plain,
% 2.57/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.57/1.02      | v1_funct_2(X3,X4,X5)
% 2.57/1.02      | X3 != X0
% 2.57/1.02      | X4 != X1
% 2.57/1.02      | X5 != X2 ),
% 2.57/1.02      theory(equality) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2307,plain,
% 2.57/1.02      ( v1_funct_2(X0,X1,X2)
% 2.57/1.02      | ~ v1_funct_2(sK3,sK1,sK2)
% 2.57/1.02      | X2 != sK2
% 2.57/1.02      | X1 != sK1
% 2.57/1.02      | X0 != sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_1380]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3998,plain,
% 2.57/1.02      ( v1_funct_2(X0,sK1,X1)
% 2.57/1.02      | ~ v1_funct_2(sK3,sK1,sK2)
% 2.57/1.02      | X1 != sK2
% 2.57/1.02      | X0 != sK3
% 2.57/1.02      | sK1 != sK1 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_2307]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4394,plain,
% 2.57/1.02      ( v1_funct_2(sK3,sK1,X0)
% 2.57/1.02      | ~ v1_funct_2(sK3,sK1,sK2)
% 2.57/1.02      | X0 != sK2
% 2.57/1.02      | sK1 != sK1
% 2.57/1.02      | sK3 != sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_3998]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4395,plain,
% 2.57/1.02      ( X0 != sK2
% 2.57/1.02      | sK1 != sK1
% 2.57/1.02      | sK3 != sK3
% 2.57/1.02      | v1_funct_2(sK3,sK1,X0) = iProver_top
% 2.57/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_4394]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4397,plain,
% 2.57/1.02      ( sK1 != sK1
% 2.57/1.02      | sK3 != sK3
% 2.57/1.02      | k1_xboole_0 != sK2
% 2.57/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 2.57/1.02      | v1_funct_2(sK3,sK1,k1_xboole_0) = iProver_top ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_4395]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5918,plain,
% 2.57/1.02      ( sK3 = k1_xboole_0 ),
% 2.57/1.02      inference(global_propositional_subsumption,
% 2.57/1.02                [status(thm)],
% 2.57/1.02                [c_5890,c_34,c_23,c_1396,c_2224,c_2474,c_2503,c_2508,
% 2.57/1.02                 c_2531,c_3431,c_4397,c_5601,c_5647]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_6203,plain,
% 2.57/1.02      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 2.57/1.02      inference(light_normalisation,[status(thm)],[c_5644,c_5918]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_1,plain,
% 2.57/1.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.57/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3,plain,
% 2.57/1.02      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.57/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2,plain,
% 2.57/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 2.57/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_381,plain,
% 2.57/1.02      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | k4_xboole_0(X0,X1) != X0 ),
% 2.57/1.02      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_1998,plain,
% 2.57/1.02      ( k4_xboole_0(X0,X1) != X0
% 2.57/1.02      | r1_tarski(X0,X1) != iProver_top
% 2.57/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2806,plain,
% 2.57/1.02      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.57/1.02      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_1,c_1998]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_6210,plain,
% 2.57/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_6203,c_2806]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_31,negated_conjecture,
% 2.57/1.02      ( ~ v1_xboole_0(sK2) ),
% 2.57/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2000,plain,
% 2.57/1.02      ( v1_xboole_0(sK2) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5649,plain,
% 2.57/1.02      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.57/1.02      inference(demodulation,[status(thm)],[c_5619,c_2000]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(contradiction,plain,
% 2.57/1.02      ( $false ),
% 2.57/1.02      inference(minisat,[status(thm)],[c_6210,c_5649]) ).
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/1.02  
% 2.57/1.02  ------                               Statistics
% 2.57/1.02  
% 2.57/1.02  ------ General
% 2.57/1.02  
% 2.57/1.02  abstr_ref_over_cycles:                  0
% 2.57/1.02  abstr_ref_under_cycles:                 0
% 2.57/1.02  gc_basic_clause_elim:                   0
% 2.57/1.02  forced_gc_time:                         0
% 2.57/1.02  parsing_time:                           0.007
% 2.57/1.02  unif_index_cands_time:                  0.
% 2.57/1.02  unif_index_add_time:                    0.
% 2.57/1.02  orderings_time:                         0.
% 2.57/1.02  out_proof_time:                         0.01
% 2.57/1.02  total_time:                             0.161
% 2.57/1.02  num_of_symbols:                         56
% 2.57/1.02  num_of_terms:                           6476
% 2.57/1.02  
% 2.57/1.02  ------ Preprocessing
% 2.57/1.02  
% 2.57/1.02  num_of_splits:                          0
% 2.57/1.02  num_of_split_atoms:                     0
% 2.57/1.02  num_of_reused_defs:                     0
% 2.57/1.02  num_eq_ax_congr_red:                    36
% 2.57/1.02  num_of_sem_filtered_clauses:            1
% 2.57/1.02  num_of_subtypes:                        0
% 2.57/1.02  monotx_restored_types:                  0
% 2.57/1.02  sat_num_of_epr_types:                   0
% 2.57/1.02  sat_num_of_non_cyclic_types:            0
% 2.57/1.02  sat_guarded_non_collapsed_types:        0
% 2.57/1.02  num_pure_diseq_elim:                    0
% 2.57/1.02  simp_replaced_by:                       0
% 2.57/1.02  res_preprocessed:                       143
% 2.57/1.02  prep_upred:                             0
% 2.57/1.02  prep_unflattend:                        104
% 2.57/1.02  smt_new_axioms:                         0
% 2.57/1.02  pred_elim_cands:                        6
% 2.57/1.02  pred_elim:                              2
% 2.57/1.02  pred_elim_cl:                           2
% 2.57/1.02  pred_elim_cycles:                       6
% 2.57/1.02  merged_defs:                            8
% 2.57/1.02  merged_defs_ncl:                        0
% 2.57/1.02  bin_hyper_res:                          8
% 2.57/1.02  prep_cycles:                            4
% 2.57/1.02  pred_elim_time:                         0.011
% 2.57/1.02  splitting_time:                         0.
% 2.57/1.02  sem_filter_time:                        0.
% 2.57/1.02  monotx_time:                            0.
% 2.57/1.02  subtype_inf_time:                       0.
% 2.57/1.02  
% 2.57/1.02  ------ Problem properties
% 2.57/1.02  
% 2.57/1.02  clauses:                                28
% 2.57/1.02  conjectures:                            10
% 2.57/1.02  epr:                                    8
% 2.57/1.02  horn:                                   21
% 2.57/1.02  ground:                                 10
% 2.57/1.02  unary:                                  11
% 2.57/1.02  binary:                                 6
% 2.57/1.02  lits:                                   72
% 2.57/1.02  lits_eq:                                19
% 2.57/1.02  fd_pure:                                0
% 2.57/1.02  fd_pseudo:                              0
% 2.57/1.02  fd_cond:                                5
% 2.57/1.02  fd_pseudo_cond:                         0
% 2.57/1.02  ac_symbols:                             0
% 2.57/1.02  
% 2.57/1.02  ------ Propositional Solver
% 2.57/1.02  
% 2.57/1.02  prop_solver_calls:                      29
% 2.57/1.02  prop_fast_solver_calls:                 1239
% 2.57/1.02  smt_solver_calls:                       0
% 2.57/1.02  smt_fast_solver_calls:                  0
% 2.57/1.02  prop_num_of_clauses:                    1709
% 2.57/1.02  prop_preprocess_simplified:             5725
% 2.57/1.02  prop_fo_subsumed:                       51
% 2.57/1.02  prop_solver_time:                       0.
% 2.57/1.02  smt_solver_time:                        0.
% 2.57/1.02  smt_fast_solver_time:                   0.
% 2.57/1.02  prop_fast_solver_time:                  0.
% 2.57/1.02  prop_unsat_core_time:                   0.
% 2.57/1.02  
% 2.57/1.02  ------ QBF
% 2.57/1.02  
% 2.57/1.02  qbf_q_res:                              0
% 2.57/1.02  qbf_num_tautologies:                    0
% 2.57/1.02  qbf_prep_cycles:                        0
% 2.57/1.02  
% 2.57/1.02  ------ BMC1
% 2.57/1.02  
% 2.57/1.02  bmc1_current_bound:                     -1
% 2.57/1.02  bmc1_last_solved_bound:                 -1
% 2.57/1.02  bmc1_unsat_core_size:                   -1
% 2.57/1.02  bmc1_unsat_core_parents_size:           -1
% 2.57/1.02  bmc1_merge_next_fun:                    0
% 2.57/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.57/1.02  
% 2.57/1.02  ------ Instantiation
% 2.57/1.02  
% 2.57/1.02  inst_num_of_clauses:                    603
% 2.57/1.02  inst_num_in_passive:                    202
% 2.57/1.02  inst_num_in_active:                     400
% 2.57/1.02  inst_num_in_unprocessed:                1
% 2.57/1.02  inst_num_of_loops:                      410
% 2.57/1.02  inst_num_of_learning_restarts:          0
% 2.57/1.02  inst_num_moves_active_passive:          6
% 2.57/1.02  inst_lit_activity:                      0
% 2.57/1.02  inst_lit_activity_moves:                0
% 2.57/1.02  inst_num_tautologies:                   0
% 2.57/1.02  inst_num_prop_implied:                  0
% 2.57/1.02  inst_num_existing_simplified:           0
% 2.57/1.02  inst_num_eq_res_simplified:             0
% 2.57/1.02  inst_num_child_elim:                    0
% 2.57/1.02  inst_num_of_dismatching_blockings:      31
% 2.57/1.02  inst_num_of_non_proper_insts:           495
% 2.57/1.02  inst_num_of_duplicates:                 0
% 2.57/1.02  inst_inst_num_from_inst_to_res:         0
% 2.57/1.02  inst_dismatching_checking_time:         0.
% 2.57/1.02  
% 2.57/1.02  ------ Resolution
% 2.57/1.02  
% 2.57/1.02  res_num_of_clauses:                     0
% 2.57/1.02  res_num_in_passive:                     0
% 2.57/1.02  res_num_in_active:                      0
% 2.57/1.02  res_num_of_loops:                       147
% 2.57/1.02  res_forward_subset_subsumed:            64
% 2.57/1.02  res_backward_subset_subsumed:           0
% 2.57/1.02  res_forward_subsumed:                   0
% 2.57/1.02  res_backward_subsumed:                  0
% 2.57/1.02  res_forward_subsumption_resolution:     1
% 2.57/1.02  res_backward_subsumption_resolution:    0
% 2.57/1.02  res_clause_to_clause_subsumption:       209
% 2.57/1.02  res_orphan_elimination:                 0
% 2.57/1.02  res_tautology_del:                      103
% 2.57/1.02  res_num_eq_res_simplified:              0
% 2.57/1.02  res_num_sel_changes:                    0
% 2.57/1.02  res_moves_from_active_to_pass:          0
% 2.57/1.02  
% 2.57/1.02  ------ Superposition
% 2.57/1.02  
% 2.57/1.02  sup_time_total:                         0.
% 2.57/1.02  sup_time_generating:                    0.
% 2.57/1.02  sup_time_sim_full:                      0.
% 2.57/1.02  sup_time_sim_immed:                     0.
% 2.57/1.02  
% 2.57/1.02  sup_num_of_clauses:                     65
% 2.57/1.02  sup_num_in_active:                      42
% 2.57/1.02  sup_num_in_passive:                     23
% 2.57/1.02  sup_num_of_loops:                       80
% 2.57/1.02  sup_fw_superposition:                   56
% 2.57/1.02  sup_bw_superposition:                   33
% 2.57/1.02  sup_immediate_simplified:               15
% 2.57/1.02  sup_given_eliminated:                   0
% 2.57/1.02  comparisons_done:                       0
% 2.57/1.02  comparisons_avoided:                    18
% 2.57/1.02  
% 2.57/1.02  ------ Simplifications
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  sim_fw_subset_subsumed:                 12
% 2.57/1.02  sim_bw_subset_subsumed:                 3
% 2.57/1.02  sim_fw_subsumed:                        1
% 2.57/1.02  sim_bw_subsumed:                        0
% 2.57/1.02  sim_fw_subsumption_res:                 0
% 2.57/1.02  sim_bw_subsumption_res:                 0
% 2.57/1.02  sim_tautology_del:                      2
% 2.57/1.02  sim_eq_tautology_del:                   10
% 2.57/1.02  sim_eq_res_simp:                        0
% 2.57/1.02  sim_fw_demodulated:                     2
% 2.57/1.02  sim_bw_demodulated:                     38
% 2.57/1.02  sim_light_normalised:                   3
% 2.57/1.02  sim_joinable_taut:                      0
% 2.57/1.02  sim_joinable_simp:                      0
% 2.57/1.02  sim_ac_normalised:                      0
% 2.57/1.02  sim_smt_subsumption:                    0
% 2.57/1.02  
%------------------------------------------------------------------------------
