%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:37 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 650 expanded)
%              Number of clauses        :  112 ( 218 expanded)
%              Number of leaves         :   21 ( 192 expanded)
%              Depth                    :   17
%              Number of atoms          :  588 (3974 expanded)
%              Number of equality atoms :  257 (1042 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5)
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6)
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK6,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
            ( k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5)
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
                ( k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5)
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
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
                  ( k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5)
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

fof(f51,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)
    & k1_xboole_0 != sK2
    & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))
    & m1_subset_1(sK6,sK2)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f41,f50,f49,f48,f47])).

fof(f79,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f42])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2007,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2009,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_416,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | X1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_417,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_2003,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X1,X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_2900,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(sK6,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2009,c_2003])).

cnf(c_39,plain,
    ( m1_subset_1(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2290,plain,
    ( r2_hidden(X0,sK2)
    | ~ m1_subset_1(X0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_2445,plain,
    ( r2_hidden(sK6,sK2)
    | ~ m1_subset_1(sK6,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2290])).

cnf(c_2446,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(sK6,sK2) = iProver_top
    | m1_subset_1(sK6,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2445])).

cnf(c_4599,plain,
    ( r2_hidden(sK6,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2900,c_39,c_24,c_2446])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2006,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2012,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4282,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_2012])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2019,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3058,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2006,c_2019])).

cnf(c_4286,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4282,c_3058])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,plain,
    ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7273,plain,
    ( sK3 = k1_xboole_0
    | k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4286,c_35])).

cnf(c_7274,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7273])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2022,plain,
    ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7277,plain,
    ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | sK3 = k1_xboole_0
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7274,c_2022])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2240,plain,
    ( m1_subset_1(sK0(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_431,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_32])).

cnf(c_432,plain,
    ( r2_hidden(X0,sK3)
    | ~ m1_subset_1(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_2241,plain,
    ( r2_hidden(sK0(sK3),sK3)
    | ~ m1_subset_1(sK0(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2273,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2274,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2273])).

cnf(c_1330,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2588,plain,
    ( r2_hidden(sK0(sK3),X0)
    | ~ r2_hidden(sK0(sK3),sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_5136,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(X0))
    | ~ r2_hidden(sK0(sK3),sK3)
    | k1_relat_1(X0) != sK3 ),
    inference(instantiation,[status(thm)],[c_2588])).

cnf(c_5141,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(k1_xboole_0))
    | ~ r2_hidden(sK0(sK3),sK3)
    | k1_relat_1(k1_xboole_0) != sK3 ),
    inference(instantiation,[status(thm)],[c_5136])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2026,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_450,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_9])).

cnf(c_454,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_12])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_2001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_2410,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2026,c_2001])).

cnf(c_2027,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2898,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2027,c_2003])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2021,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6707,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2898,c_2021])).

cnf(c_7107,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2410,c_6707])).

cnf(c_1326,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2516,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_7333,plain,
    ( k1_relat_1(X0) != X1
    | k1_relat_1(X0) = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_2516])).

cnf(c_7334,plain,
    ( k1_relat_1(k1_xboole_0) = sK3
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7333])).

cnf(c_5125,plain,
    ( ~ r2_hidden(sK0(sK3),X0)
    | ~ r1_tarski(X0,sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_12002,plain,
    ( ~ r2_hidden(sK0(sK3),k1_relat_1(X0))
    | ~ r1_tarski(k1_relat_1(X0),sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_5125])).

cnf(c_12005,plain,
    ( ~ r2_hidden(sK0(sK3),k1_relat_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_12002])).

cnf(c_12003,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0(sK3),X1)))
    | r1_tarski(k1_relat_1(X0),sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_12009,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(sK3),k1_xboole_0)))
    | r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) ),
    inference(instantiation,[status(thm)],[c_12003])).

cnf(c_2260,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3731,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_21440,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(sK3),k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_3731])).

cnf(c_28025,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7277,c_34,c_36,c_2240,c_2241,c_2274,c_5141,c_7107,c_7334,c_12005,c_12009,c_21440])).

cnf(c_28026,plain,
    ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
    | r2_hidden(X1,sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_28025])).

cnf(c_28035,plain,
    ( k1_funct_1(k5_relat_1(sK4,X0),sK6) = k1_funct_1(X0,k1_funct_1(sK4,sK6))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4599,c_28026])).

cnf(c_28917,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2007,c_28035])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2008,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3057,plain,
    ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2008,c_2019])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2010,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3361,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3057,c_2010])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2018,plain,
    ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
    | k1_xboole_0 = X1
    | v1_funct_2(X3,X0,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4392,plain,
    ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_2018])).

cnf(c_37,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8145,plain,
    ( v1_funct_1(X1) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4392,c_37,c_38])).

cnf(c_8146,plain,
    ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8145])).

cnf(c_8157,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3361,c_8146])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2011,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3433,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2008,c_2011])).

cnf(c_4015,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3433,c_37])).

cnf(c_4016,plain,
    ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4015])).

cnf(c_4028,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2006,c_4016])).

cnf(c_2384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2561,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2845,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK2,sK3,X0,X1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_2975,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2845])).

cnf(c_4098,plain,
    ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4028,c_31,c_29,c_28,c_27,c_2975])).

cnf(c_8158,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | sK3 = k1_xboole_0
    | v1_funct_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8157,c_4098])).

cnf(c_8161,plain,
    ( sK3 = k1_xboole_0
    | k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8158,c_34,c_35,c_36])).

cnf(c_8162,plain,
    ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8161])).

cnf(c_23,negated_conjecture,
    ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8165,plain,
    ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8162,c_23])).

cnf(c_2270,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2271,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2270])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28917,c_21440,c_12009,c_12005,c_8165,c_7334,c_7107,c_5141,c_2271,c_2241,c_2240,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.59/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.48  
% 7.59/1.48  ------  iProver source info
% 7.59/1.48  
% 7.59/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.48  git: non_committed_changes: false
% 7.59/1.48  git: last_make_outside_of_git: false
% 7.59/1.48  
% 7.59/1.48  ------ 
% 7.59/1.48  
% 7.59/1.48  ------ Input Options
% 7.59/1.48  
% 7.59/1.48  --out_options                           all
% 7.59/1.48  --tptp_safe_out                         true
% 7.59/1.48  --problem_path                          ""
% 7.59/1.48  --include_path                          ""
% 7.59/1.48  --clausifier                            res/vclausify_rel
% 7.59/1.48  --clausifier_options                    --mode clausify
% 7.59/1.48  --stdin                                 false
% 7.59/1.48  --stats_out                             all
% 7.59/1.48  
% 7.59/1.48  ------ General Options
% 7.59/1.48  
% 7.59/1.48  --fof                                   false
% 7.59/1.48  --time_out_real                         305.
% 7.59/1.48  --time_out_virtual                      -1.
% 7.59/1.48  --symbol_type_check                     false
% 7.59/1.48  --clausify_out                          false
% 7.59/1.48  --sig_cnt_out                           false
% 7.59/1.48  --trig_cnt_out                          false
% 7.59/1.48  --trig_cnt_out_tolerance                1.
% 7.59/1.48  --trig_cnt_out_sk_spl                   false
% 7.59/1.48  --abstr_cl_out                          false
% 7.59/1.48  
% 7.59/1.48  ------ Global Options
% 7.59/1.48  
% 7.59/1.48  --schedule                              default
% 7.59/1.48  --add_important_lit                     false
% 7.59/1.48  --prop_solver_per_cl                    1000
% 7.59/1.48  --min_unsat_core                        false
% 7.59/1.48  --soft_assumptions                      false
% 7.59/1.48  --soft_lemma_size                       3
% 7.59/1.48  --prop_impl_unit_size                   0
% 7.59/1.48  --prop_impl_unit                        []
% 7.59/1.48  --share_sel_clauses                     true
% 7.59/1.48  --reset_solvers                         false
% 7.59/1.48  --bc_imp_inh                            [conj_cone]
% 7.59/1.48  --conj_cone_tolerance                   3.
% 7.59/1.48  --extra_neg_conj                        none
% 7.59/1.48  --large_theory_mode                     true
% 7.59/1.48  --prolific_symb_bound                   200
% 7.59/1.48  --lt_threshold                          2000
% 7.59/1.48  --clause_weak_htbl                      true
% 7.59/1.48  --gc_record_bc_elim                     false
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing Options
% 7.59/1.48  
% 7.59/1.48  --preprocessing_flag                    true
% 7.59/1.48  --time_out_prep_mult                    0.1
% 7.59/1.48  --splitting_mode                        input
% 7.59/1.48  --splitting_grd                         true
% 7.59/1.48  --splitting_cvd                         false
% 7.59/1.48  --splitting_cvd_svl                     false
% 7.59/1.48  --splitting_nvd                         32
% 7.59/1.48  --sub_typing                            true
% 7.59/1.48  --prep_gs_sim                           true
% 7.59/1.48  --prep_unflatten                        true
% 7.59/1.48  --prep_res_sim                          true
% 7.59/1.48  --prep_upred                            true
% 7.59/1.48  --prep_sem_filter                       exhaustive
% 7.59/1.48  --prep_sem_filter_out                   false
% 7.59/1.48  --pred_elim                             true
% 7.59/1.48  --res_sim_input                         true
% 7.59/1.48  --eq_ax_congr_red                       true
% 7.59/1.48  --pure_diseq_elim                       true
% 7.59/1.48  --brand_transform                       false
% 7.59/1.48  --non_eq_to_eq                          false
% 7.59/1.48  --prep_def_merge                        true
% 7.59/1.48  --prep_def_merge_prop_impl              false
% 7.59/1.48  --prep_def_merge_mbd                    true
% 7.59/1.48  --prep_def_merge_tr_red                 false
% 7.59/1.48  --prep_def_merge_tr_cl                  false
% 7.59/1.48  --smt_preprocessing                     true
% 7.59/1.48  --smt_ac_axioms                         fast
% 7.59/1.48  --preprocessed_out                      false
% 7.59/1.48  --preprocessed_stats                    false
% 7.59/1.48  
% 7.59/1.48  ------ Abstraction refinement Options
% 7.59/1.48  
% 7.59/1.48  --abstr_ref                             []
% 7.59/1.48  --abstr_ref_prep                        false
% 7.59/1.48  --abstr_ref_until_sat                   false
% 7.59/1.48  --abstr_ref_sig_restrict                funpre
% 7.59/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.48  --abstr_ref_under                       []
% 7.59/1.48  
% 7.59/1.48  ------ SAT Options
% 7.59/1.48  
% 7.59/1.48  --sat_mode                              false
% 7.59/1.48  --sat_fm_restart_options                ""
% 7.59/1.48  --sat_gr_def                            false
% 7.59/1.48  --sat_epr_types                         true
% 7.59/1.48  --sat_non_cyclic_types                  false
% 7.59/1.48  --sat_finite_models                     false
% 7.59/1.48  --sat_fm_lemmas                         false
% 7.59/1.48  --sat_fm_prep                           false
% 7.59/1.48  --sat_fm_uc_incr                        true
% 7.59/1.48  --sat_out_model                         small
% 7.59/1.48  --sat_out_clauses                       false
% 7.59/1.48  
% 7.59/1.48  ------ QBF Options
% 7.59/1.48  
% 7.59/1.48  --qbf_mode                              false
% 7.59/1.48  --qbf_elim_univ                         false
% 7.59/1.48  --qbf_dom_inst                          none
% 7.59/1.48  --qbf_dom_pre_inst                      false
% 7.59/1.48  --qbf_sk_in                             false
% 7.59/1.48  --qbf_pred_elim                         true
% 7.59/1.48  --qbf_split                             512
% 7.59/1.48  
% 7.59/1.48  ------ BMC1 Options
% 7.59/1.48  
% 7.59/1.48  --bmc1_incremental                      false
% 7.59/1.48  --bmc1_axioms                           reachable_all
% 7.59/1.48  --bmc1_min_bound                        0
% 7.59/1.48  --bmc1_max_bound                        -1
% 7.59/1.48  --bmc1_max_bound_default                -1
% 7.59/1.48  --bmc1_symbol_reachability              true
% 7.59/1.48  --bmc1_property_lemmas                  false
% 7.59/1.48  --bmc1_k_induction                      false
% 7.59/1.48  --bmc1_non_equiv_states                 false
% 7.59/1.48  --bmc1_deadlock                         false
% 7.59/1.48  --bmc1_ucm                              false
% 7.59/1.48  --bmc1_add_unsat_core                   none
% 7.59/1.48  --bmc1_unsat_core_children              false
% 7.59/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.48  --bmc1_out_stat                         full
% 7.59/1.48  --bmc1_ground_init                      false
% 7.59/1.48  --bmc1_pre_inst_next_state              false
% 7.59/1.48  --bmc1_pre_inst_state                   false
% 7.59/1.48  --bmc1_pre_inst_reach_state             false
% 7.59/1.48  --bmc1_out_unsat_core                   false
% 7.59/1.48  --bmc1_aig_witness_out                  false
% 7.59/1.48  --bmc1_verbose                          false
% 7.59/1.48  --bmc1_dump_clauses_tptp                false
% 7.59/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.48  --bmc1_dump_file                        -
% 7.59/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.48  --bmc1_ucm_extend_mode                  1
% 7.59/1.48  --bmc1_ucm_init_mode                    2
% 7.59/1.48  --bmc1_ucm_cone_mode                    none
% 7.59/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.48  --bmc1_ucm_relax_model                  4
% 7.59/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.48  --bmc1_ucm_layered_model                none
% 7.59/1.48  --bmc1_ucm_max_lemma_size               10
% 7.59/1.48  
% 7.59/1.48  ------ AIG Options
% 7.59/1.48  
% 7.59/1.48  --aig_mode                              false
% 7.59/1.48  
% 7.59/1.48  ------ Instantiation Options
% 7.59/1.48  
% 7.59/1.48  --instantiation_flag                    true
% 7.59/1.48  --inst_sos_flag                         false
% 7.59/1.48  --inst_sos_phase                        true
% 7.59/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel_side                     num_symb
% 7.59/1.48  --inst_solver_per_active                1400
% 7.59/1.48  --inst_solver_calls_frac                1.
% 7.59/1.48  --inst_passive_queue_type               priority_queues
% 7.59/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.48  --inst_passive_queues_freq              [25;2]
% 7.59/1.48  --inst_dismatching                      true
% 7.59/1.48  --inst_eager_unprocessed_to_passive     true
% 7.59/1.48  --inst_prop_sim_given                   true
% 7.59/1.48  --inst_prop_sim_new                     false
% 7.59/1.48  --inst_subs_new                         false
% 7.59/1.48  --inst_eq_res_simp                      false
% 7.59/1.48  --inst_subs_given                       false
% 7.59/1.48  --inst_orphan_elimination               true
% 7.59/1.48  --inst_learning_loop_flag               true
% 7.59/1.48  --inst_learning_start                   3000
% 7.59/1.48  --inst_learning_factor                  2
% 7.59/1.48  --inst_start_prop_sim_after_learn       3
% 7.59/1.48  --inst_sel_renew                        solver
% 7.59/1.48  --inst_lit_activity_flag                true
% 7.59/1.48  --inst_restr_to_given                   false
% 7.59/1.48  --inst_activity_threshold               500
% 7.59/1.48  --inst_out_proof                        true
% 7.59/1.48  
% 7.59/1.48  ------ Resolution Options
% 7.59/1.48  
% 7.59/1.48  --resolution_flag                       true
% 7.59/1.48  --res_lit_sel                           adaptive
% 7.59/1.48  --res_lit_sel_side                      none
% 7.59/1.48  --res_ordering                          kbo
% 7.59/1.48  --res_to_prop_solver                    active
% 7.59/1.48  --res_prop_simpl_new                    false
% 7.59/1.48  --res_prop_simpl_given                  true
% 7.59/1.48  --res_passive_queue_type                priority_queues
% 7.59/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.48  --res_passive_queues_freq               [15;5]
% 7.59/1.48  --res_forward_subs                      full
% 7.59/1.48  --res_backward_subs                     full
% 7.59/1.48  --res_forward_subs_resolution           true
% 7.59/1.48  --res_backward_subs_resolution          true
% 7.59/1.48  --res_orphan_elimination                true
% 7.59/1.48  --res_time_limit                        2.
% 7.59/1.48  --res_out_proof                         true
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Options
% 7.59/1.48  
% 7.59/1.48  --superposition_flag                    true
% 7.59/1.48  --sup_passive_queue_type                priority_queues
% 7.59/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.48  --demod_completeness_check              fast
% 7.59/1.48  --demod_use_ground                      true
% 7.59/1.48  --sup_to_prop_solver                    passive
% 7.59/1.48  --sup_prop_simpl_new                    true
% 7.59/1.48  --sup_prop_simpl_given                  true
% 7.59/1.48  --sup_fun_splitting                     false
% 7.59/1.48  --sup_smt_interval                      50000
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Simplification Setup
% 7.59/1.48  
% 7.59/1.48  --sup_indices_passive                   []
% 7.59/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.48  --sup_full_bw                           [BwDemod]
% 7.59/1.48  --sup_immed_triv                        [TrivRules]
% 7.59/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.48  --sup_immed_bw_main                     []
% 7.59/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.48  
% 7.59/1.48  ------ Combination Options
% 7.59/1.48  
% 7.59/1.48  --comb_res_mult                         3
% 7.59/1.48  --comb_sup_mult                         2
% 7.59/1.48  --comb_inst_mult                        10
% 7.59/1.48  
% 7.59/1.48  ------ Debug Options
% 7.59/1.48  
% 7.59/1.48  --dbg_backtrace                         false
% 7.59/1.48  --dbg_dump_prop_clauses                 false
% 7.59/1.48  --dbg_dump_prop_clauses_file            -
% 7.59/1.48  --dbg_out_stat                          false
% 7.59/1.48  ------ Parsing...
% 7.59/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.48  ------ Proving...
% 7.59/1.48  ------ Problem Properties 
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  clauses                                 30
% 7.59/1.48  conjectures                             9
% 7.59/1.48  EPR                                     9
% 7.59/1.48  Horn                                    24
% 7.59/1.48  unary                                   11
% 7.59/1.48  binary                                  7
% 7.59/1.48  lits                                    74
% 7.59/1.48  lits eq                                 17
% 7.59/1.48  fd_pure                                 0
% 7.59/1.48  fd_pseudo                               0
% 7.59/1.48  fd_cond                                 5
% 7.59/1.48  fd_pseudo_cond                          0
% 7.59/1.48  AC symbols                              0
% 7.59/1.48  
% 7.59/1.48  ------ Schedule dynamic 5 is on 
% 7.59/1.48  
% 7.59/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  ------ 
% 7.59/1.48  Current options:
% 7.59/1.48  ------ 
% 7.59/1.48  
% 7.59/1.48  ------ Input Options
% 7.59/1.48  
% 7.59/1.48  --out_options                           all
% 7.59/1.48  --tptp_safe_out                         true
% 7.59/1.48  --problem_path                          ""
% 7.59/1.48  --include_path                          ""
% 7.59/1.48  --clausifier                            res/vclausify_rel
% 7.59/1.48  --clausifier_options                    --mode clausify
% 7.59/1.48  --stdin                                 false
% 7.59/1.48  --stats_out                             all
% 7.59/1.48  
% 7.59/1.48  ------ General Options
% 7.59/1.48  
% 7.59/1.48  --fof                                   false
% 7.59/1.48  --time_out_real                         305.
% 7.59/1.48  --time_out_virtual                      -1.
% 7.59/1.48  --symbol_type_check                     false
% 7.59/1.48  --clausify_out                          false
% 7.59/1.48  --sig_cnt_out                           false
% 7.59/1.48  --trig_cnt_out                          false
% 7.59/1.48  --trig_cnt_out_tolerance                1.
% 7.59/1.48  --trig_cnt_out_sk_spl                   false
% 7.59/1.48  --abstr_cl_out                          false
% 7.59/1.48  
% 7.59/1.48  ------ Global Options
% 7.59/1.48  
% 7.59/1.48  --schedule                              default
% 7.59/1.48  --add_important_lit                     false
% 7.59/1.48  --prop_solver_per_cl                    1000
% 7.59/1.48  --min_unsat_core                        false
% 7.59/1.48  --soft_assumptions                      false
% 7.59/1.48  --soft_lemma_size                       3
% 7.59/1.48  --prop_impl_unit_size                   0
% 7.59/1.48  --prop_impl_unit                        []
% 7.59/1.48  --share_sel_clauses                     true
% 7.59/1.48  --reset_solvers                         false
% 7.59/1.48  --bc_imp_inh                            [conj_cone]
% 7.59/1.48  --conj_cone_tolerance                   3.
% 7.59/1.48  --extra_neg_conj                        none
% 7.59/1.48  --large_theory_mode                     true
% 7.59/1.48  --prolific_symb_bound                   200
% 7.59/1.48  --lt_threshold                          2000
% 7.59/1.48  --clause_weak_htbl                      true
% 7.59/1.48  --gc_record_bc_elim                     false
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing Options
% 7.59/1.48  
% 7.59/1.48  --preprocessing_flag                    true
% 7.59/1.48  --time_out_prep_mult                    0.1
% 7.59/1.48  --splitting_mode                        input
% 7.59/1.48  --splitting_grd                         true
% 7.59/1.48  --splitting_cvd                         false
% 7.59/1.48  --splitting_cvd_svl                     false
% 7.59/1.48  --splitting_nvd                         32
% 7.59/1.48  --sub_typing                            true
% 7.59/1.48  --prep_gs_sim                           true
% 7.59/1.48  --prep_unflatten                        true
% 7.59/1.48  --prep_res_sim                          true
% 7.59/1.48  --prep_upred                            true
% 7.59/1.48  --prep_sem_filter                       exhaustive
% 7.59/1.48  --prep_sem_filter_out                   false
% 7.59/1.48  --pred_elim                             true
% 7.59/1.48  --res_sim_input                         true
% 7.59/1.48  --eq_ax_congr_red                       true
% 7.59/1.48  --pure_diseq_elim                       true
% 7.59/1.48  --brand_transform                       false
% 7.59/1.48  --non_eq_to_eq                          false
% 7.59/1.48  --prep_def_merge                        true
% 7.59/1.48  --prep_def_merge_prop_impl              false
% 7.59/1.48  --prep_def_merge_mbd                    true
% 7.59/1.48  --prep_def_merge_tr_red                 false
% 7.59/1.48  --prep_def_merge_tr_cl                  false
% 7.59/1.48  --smt_preprocessing                     true
% 7.59/1.48  --smt_ac_axioms                         fast
% 7.59/1.48  --preprocessed_out                      false
% 7.59/1.48  --preprocessed_stats                    false
% 7.59/1.48  
% 7.59/1.48  ------ Abstraction refinement Options
% 7.59/1.48  
% 7.59/1.48  --abstr_ref                             []
% 7.59/1.48  --abstr_ref_prep                        false
% 7.59/1.48  --abstr_ref_until_sat                   false
% 7.59/1.48  --abstr_ref_sig_restrict                funpre
% 7.59/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.59/1.48  --abstr_ref_under                       []
% 7.59/1.48  
% 7.59/1.48  ------ SAT Options
% 7.59/1.48  
% 7.59/1.48  --sat_mode                              false
% 7.59/1.48  --sat_fm_restart_options                ""
% 7.59/1.48  --sat_gr_def                            false
% 7.59/1.48  --sat_epr_types                         true
% 7.59/1.48  --sat_non_cyclic_types                  false
% 7.59/1.48  --sat_finite_models                     false
% 7.59/1.48  --sat_fm_lemmas                         false
% 7.59/1.48  --sat_fm_prep                           false
% 7.59/1.48  --sat_fm_uc_incr                        true
% 7.59/1.48  --sat_out_model                         small
% 7.59/1.48  --sat_out_clauses                       false
% 7.59/1.48  
% 7.59/1.48  ------ QBF Options
% 7.59/1.48  
% 7.59/1.48  --qbf_mode                              false
% 7.59/1.48  --qbf_elim_univ                         false
% 7.59/1.48  --qbf_dom_inst                          none
% 7.59/1.48  --qbf_dom_pre_inst                      false
% 7.59/1.48  --qbf_sk_in                             false
% 7.59/1.48  --qbf_pred_elim                         true
% 7.59/1.48  --qbf_split                             512
% 7.59/1.48  
% 7.59/1.48  ------ BMC1 Options
% 7.59/1.48  
% 7.59/1.48  --bmc1_incremental                      false
% 7.59/1.48  --bmc1_axioms                           reachable_all
% 7.59/1.48  --bmc1_min_bound                        0
% 7.59/1.48  --bmc1_max_bound                        -1
% 7.59/1.48  --bmc1_max_bound_default                -1
% 7.59/1.48  --bmc1_symbol_reachability              true
% 7.59/1.48  --bmc1_property_lemmas                  false
% 7.59/1.48  --bmc1_k_induction                      false
% 7.59/1.48  --bmc1_non_equiv_states                 false
% 7.59/1.48  --bmc1_deadlock                         false
% 7.59/1.48  --bmc1_ucm                              false
% 7.59/1.48  --bmc1_add_unsat_core                   none
% 7.59/1.48  --bmc1_unsat_core_children              false
% 7.59/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.59/1.48  --bmc1_out_stat                         full
% 7.59/1.48  --bmc1_ground_init                      false
% 7.59/1.48  --bmc1_pre_inst_next_state              false
% 7.59/1.48  --bmc1_pre_inst_state                   false
% 7.59/1.48  --bmc1_pre_inst_reach_state             false
% 7.59/1.48  --bmc1_out_unsat_core                   false
% 7.59/1.48  --bmc1_aig_witness_out                  false
% 7.59/1.48  --bmc1_verbose                          false
% 7.59/1.48  --bmc1_dump_clauses_tptp                false
% 7.59/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.59/1.48  --bmc1_dump_file                        -
% 7.59/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.59/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.59/1.48  --bmc1_ucm_extend_mode                  1
% 7.59/1.48  --bmc1_ucm_init_mode                    2
% 7.59/1.48  --bmc1_ucm_cone_mode                    none
% 7.59/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.59/1.48  --bmc1_ucm_relax_model                  4
% 7.59/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.59/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.59/1.48  --bmc1_ucm_layered_model                none
% 7.59/1.48  --bmc1_ucm_max_lemma_size               10
% 7.59/1.48  
% 7.59/1.48  ------ AIG Options
% 7.59/1.48  
% 7.59/1.48  --aig_mode                              false
% 7.59/1.48  
% 7.59/1.48  ------ Instantiation Options
% 7.59/1.48  
% 7.59/1.48  --instantiation_flag                    true
% 7.59/1.48  --inst_sos_flag                         false
% 7.59/1.48  --inst_sos_phase                        true
% 7.59/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.59/1.48  --inst_lit_sel_side                     none
% 7.59/1.48  --inst_solver_per_active                1400
% 7.59/1.48  --inst_solver_calls_frac                1.
% 7.59/1.48  --inst_passive_queue_type               priority_queues
% 7.59/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.59/1.48  --inst_passive_queues_freq              [25;2]
% 7.59/1.48  --inst_dismatching                      true
% 7.59/1.48  --inst_eager_unprocessed_to_passive     true
% 7.59/1.48  --inst_prop_sim_given                   true
% 7.59/1.48  --inst_prop_sim_new                     false
% 7.59/1.48  --inst_subs_new                         false
% 7.59/1.48  --inst_eq_res_simp                      false
% 7.59/1.48  --inst_subs_given                       false
% 7.59/1.48  --inst_orphan_elimination               true
% 7.59/1.48  --inst_learning_loop_flag               true
% 7.59/1.48  --inst_learning_start                   3000
% 7.59/1.48  --inst_learning_factor                  2
% 7.59/1.48  --inst_start_prop_sim_after_learn       3
% 7.59/1.48  --inst_sel_renew                        solver
% 7.59/1.48  --inst_lit_activity_flag                true
% 7.59/1.48  --inst_restr_to_given                   false
% 7.59/1.48  --inst_activity_threshold               500
% 7.59/1.48  --inst_out_proof                        true
% 7.59/1.48  
% 7.59/1.48  ------ Resolution Options
% 7.59/1.48  
% 7.59/1.48  --resolution_flag                       false
% 7.59/1.48  --res_lit_sel                           adaptive
% 7.59/1.48  --res_lit_sel_side                      none
% 7.59/1.48  --res_ordering                          kbo
% 7.59/1.48  --res_to_prop_solver                    active
% 7.59/1.48  --res_prop_simpl_new                    false
% 7.59/1.48  --res_prop_simpl_given                  true
% 7.59/1.48  --res_passive_queue_type                priority_queues
% 7.59/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.59/1.48  --res_passive_queues_freq               [15;5]
% 7.59/1.48  --res_forward_subs                      full
% 7.59/1.48  --res_backward_subs                     full
% 7.59/1.48  --res_forward_subs_resolution           true
% 7.59/1.48  --res_backward_subs_resolution          true
% 7.59/1.48  --res_orphan_elimination                true
% 7.59/1.48  --res_time_limit                        2.
% 7.59/1.48  --res_out_proof                         true
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Options
% 7.59/1.48  
% 7.59/1.48  --superposition_flag                    true
% 7.59/1.48  --sup_passive_queue_type                priority_queues
% 7.59/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.59/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.59/1.48  --demod_completeness_check              fast
% 7.59/1.48  --demod_use_ground                      true
% 7.59/1.48  --sup_to_prop_solver                    passive
% 7.59/1.48  --sup_prop_simpl_new                    true
% 7.59/1.48  --sup_prop_simpl_given                  true
% 7.59/1.48  --sup_fun_splitting                     false
% 7.59/1.48  --sup_smt_interval                      50000
% 7.59/1.48  
% 7.59/1.48  ------ Superposition Simplification Setup
% 7.59/1.48  
% 7.59/1.48  --sup_indices_passive                   []
% 7.59/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.59/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.59/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.48  --sup_full_bw                           [BwDemod]
% 7.59/1.48  --sup_immed_triv                        [TrivRules]
% 7.59/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.59/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.48  --sup_immed_bw_main                     []
% 7.59/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.59/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.59/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.59/1.48  
% 7.59/1.48  ------ Combination Options
% 7.59/1.48  
% 7.59/1.48  --comb_res_mult                         3
% 7.59/1.48  --comb_sup_mult                         2
% 7.59/1.48  --comb_inst_mult                        10
% 7.59/1.48  
% 7.59/1.48  ------ Debug Options
% 7.59/1.48  
% 7.59/1.48  --dbg_backtrace                         false
% 7.59/1.48  --dbg_dump_prop_clauses                 false
% 7.59/1.48  --dbg_dump_prop_clauses_file            -
% 7.59/1.48  --dbg_out_stat                          false
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  ------ Proving...
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  % SZS status Theorem for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  fof(f17,conjecture,(
% 7.59/1.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f18,negated_conjecture,(
% 7.59/1.48    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 7.59/1.48    inference(negated_conjecture,[],[f17])).
% 7.59/1.48  
% 7.59/1.48  fof(f40,plain,(
% 7.59/1.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 7.59/1.48    inference(ennf_transformation,[],[f18])).
% 7.59/1.48  
% 7.59/1.48  fof(f41,plain,(
% 7.59/1.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 7.59/1.48    inference(flattening,[],[f40])).
% 7.59/1.48  
% 7.59/1.48  fof(f50,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(X4,k1_funct_1(X3,sK6)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK6) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK6,X1))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f49,plain,(
% 7.59/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(sK5,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK5),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK5)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK5))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f48,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(sK4,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,sK4,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK4),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f47,plain,(
% 7.59/1.48    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,X3,X4),X5) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,X3),k1_relset_1(sK3,sK1,X4)) & m1_subset_1(X5,sK2)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X3,sK2,sK3) & v1_funct_1(X3)) & ~v1_xboole_0(sK3))),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f51,plain,(
% 7.59/1.48    (((k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) & k1_xboole_0 != sK2 & r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) & m1_subset_1(sK6,sK2)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)) & ~v1_xboole_0(sK3)),
% 7.59/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f41,f50,f49,f48,f47])).
% 7.59/1.48  
% 7.59/1.48  fof(f79,plain,(
% 7.59/1.48    v1_funct_1(sK5)),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f81,plain,(
% 7.59/1.48    m1_subset_1(sK6,sK2)),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f1,axiom,(
% 7.59/1.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f20,plain,(
% 7.59/1.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.59/1.48    inference(ennf_transformation,[],[f1])).
% 7.59/1.48  
% 7.59/1.48  fof(f52,plain,(
% 7.59/1.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f20])).
% 7.59/1.48  
% 7.59/1.48  fof(f5,axiom,(
% 7.59/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f23,plain,(
% 7.59/1.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.59/1.48    inference(ennf_transformation,[],[f5])).
% 7.59/1.48  
% 7.59/1.48  fof(f24,plain,(
% 7.59/1.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.59/1.48    inference(flattening,[],[f23])).
% 7.59/1.48  
% 7.59/1.48  fof(f56,plain,(
% 7.59/1.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f24])).
% 7.59/1.48  
% 7.59/1.48  fof(f83,plain,(
% 7.59/1.48    k1_xboole_0 != sK2),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f78,plain,(
% 7.59/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f15,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f36,plain,(
% 7.59/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.48    inference(ennf_transformation,[],[f15])).
% 7.59/1.48  
% 7.59/1.48  fof(f37,plain,(
% 7.59/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.48    inference(flattening,[],[f36])).
% 7.59/1.48  
% 7.59/1.48  fof(f46,plain,(
% 7.59/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.48    inference(nnf_transformation,[],[f37])).
% 7.59/1.48  
% 7.59/1.48  fof(f68,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f46])).
% 7.59/1.48  
% 7.59/1.48  fof(f13,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f33,plain,(
% 7.59/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.48    inference(ennf_transformation,[],[f13])).
% 7.59/1.48  
% 7.59/1.48  fof(f66,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f33])).
% 7.59/1.48  
% 7.59/1.48  fof(f77,plain,(
% 7.59/1.48    v1_funct_2(sK4,sK2,sK3)),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f9,axiom,(
% 7.59/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0))))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f28,plain,(
% 7.59/1.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.59/1.48    inference(ennf_transformation,[],[f9])).
% 7.59/1.48  
% 7.59/1.48  fof(f29,plain,(
% 7.59/1.48    ! [X0,X1] : (! [X2] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.59/1.48    inference(flattening,[],[f28])).
% 7.59/1.48  
% 7.59/1.48  fof(f62,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f29])).
% 7.59/1.48  
% 7.59/1.48  fof(f76,plain,(
% 7.59/1.48    v1_funct_1(sK4)),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f3,axiom,(
% 7.59/1.48    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f42,plain,(
% 7.59/1.48    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK0(X0),X0))),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f43,plain,(
% 7.59/1.48    ! [X0] : m1_subset_1(sK0(X0),X0)),
% 7.59/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3,f42])).
% 7.59/1.48  
% 7.59/1.48  fof(f54,plain,(
% 7.59/1.48    ( ! [X0] : (m1_subset_1(sK0(X0),X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f43])).
% 7.59/1.48  
% 7.59/1.48  fof(f75,plain,(
% 7.59/1.48    ~v1_xboole_0(sK3)),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f11,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f31,plain,(
% 7.59/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.48    inference(ennf_transformation,[],[f11])).
% 7.59/1.48  
% 7.59/1.48  fof(f64,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f31])).
% 7.59/1.48  
% 7.59/1.48  fof(f4,axiom,(
% 7.59/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f55,plain,(
% 7.59/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f4])).
% 7.59/1.48  
% 7.59/1.48  fof(f12,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f19,plain,(
% 7.59/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.59/1.48    inference(pure_predicate_removal,[],[f12])).
% 7.59/1.48  
% 7.59/1.48  fof(f32,plain,(
% 7.59/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.59/1.48    inference(ennf_transformation,[],[f19])).
% 7.59/1.48  
% 7.59/1.48  fof(f65,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f32])).
% 7.59/1.48  
% 7.59/1.48  fof(f8,axiom,(
% 7.59/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f27,plain,(
% 7.59/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.59/1.48    inference(ennf_transformation,[],[f8])).
% 7.59/1.48  
% 7.59/1.48  fof(f45,plain,(
% 7.59/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.59/1.48    inference(nnf_transformation,[],[f27])).
% 7.59/1.48  
% 7.59/1.48  fof(f60,plain,(
% 7.59/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f45])).
% 7.59/1.48  
% 7.59/1.48  fof(f10,axiom,(
% 7.59/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f30,plain,(
% 7.59/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.59/1.48    inference(ennf_transformation,[],[f10])).
% 7.59/1.48  
% 7.59/1.48  fof(f63,plain,(
% 7.59/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f30])).
% 7.59/1.48  
% 7.59/1.48  fof(f80,plain,(
% 7.59/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f82,plain,(
% 7.59/1.48    r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5))),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  fof(f14,axiom,(
% 7.59/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f34,plain,(
% 7.59/1.48    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.59/1.48    inference(ennf_transformation,[],[f14])).
% 7.59/1.48  
% 7.59/1.48  fof(f35,plain,(
% 7.59/1.48    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.59/1.48    inference(flattening,[],[f34])).
% 7.59/1.48  
% 7.59/1.48  fof(f67,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X3,X1] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f35])).
% 7.59/1.48  
% 7.59/1.48  fof(f16,axiom,(
% 7.59/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f38,plain,(
% 7.59/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.59/1.48    inference(ennf_transformation,[],[f16])).
% 7.59/1.48  
% 7.59/1.48  fof(f39,plain,(
% 7.59/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.59/1.48    inference(flattening,[],[f38])).
% 7.59/1.48  
% 7.59/1.48  fof(f74,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f39])).
% 7.59/1.48  
% 7.59/1.48  fof(f84,plain,(
% 7.59/1.48    k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6)),
% 7.59/1.48    inference(cnf_transformation,[],[f51])).
% 7.59/1.48  
% 7.59/1.48  cnf(c_28,negated_conjecture,
% 7.59/1.48      ( v1_funct_1(sK5) ),
% 7.59/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2007,plain,
% 7.59/1.48      ( v1_funct_1(sK5) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_26,negated_conjecture,
% 7.59/1.48      ( m1_subset_1(sK6,sK2) ),
% 7.59/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2009,plain,
% 7.59/1.48      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_0,plain,
% 7.59/1.48      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.59/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4,plain,
% 7.59/1.48      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 7.59/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_416,plain,
% 7.59/1.48      ( r2_hidden(X0,X1)
% 7.59/1.48      | ~ m1_subset_1(X0,X1)
% 7.59/1.48      | X1 != X2
% 7.59/1.48      | k1_xboole_0 = X2 ),
% 7.59/1.48      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_417,plain,
% 7.59/1.48      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | k1_xboole_0 = X1 ),
% 7.59/1.48      inference(unflattening,[status(thm)],[c_416]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2003,plain,
% 7.59/1.48      ( k1_xboole_0 = X0
% 7.59/1.48      | r2_hidden(X1,X0) = iProver_top
% 7.59/1.48      | m1_subset_1(X1,X0) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2900,plain,
% 7.59/1.48      ( sK2 = k1_xboole_0 | r2_hidden(sK6,sK2) = iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2009,c_2003]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_39,plain,
% 7.59/1.48      ( m1_subset_1(sK6,sK2) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_24,negated_conjecture,
% 7.59/1.48      ( k1_xboole_0 != sK2 ),
% 7.59/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2290,plain,
% 7.59/1.48      ( r2_hidden(X0,sK2) | ~ m1_subset_1(X0,sK2) | k1_xboole_0 = sK2 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_417]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2445,plain,
% 7.59/1.48      ( r2_hidden(sK6,sK2) | ~ m1_subset_1(sK6,sK2) | k1_xboole_0 = sK2 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2290]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2446,plain,
% 7.59/1.48      ( k1_xboole_0 = sK2
% 7.59/1.48      | r2_hidden(sK6,sK2) = iProver_top
% 7.59/1.48      | m1_subset_1(sK6,sK2) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_2445]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4599,plain,
% 7.59/1.48      ( r2_hidden(sK6,sK2) = iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2900,c_39,c_24,c_2446]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_29,negated_conjecture,
% 7.59/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 7.59/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2006,plain,
% 7.59/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_21,plain,
% 7.59/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.59/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.59/1.48      | k1_xboole_0 = X2 ),
% 7.59/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2012,plain,
% 7.59/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.59/1.48      | k1_xboole_0 = X1
% 7.59/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.59/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4282,plain,
% 7.59/1.48      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2006,c_2012]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_14,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2019,plain,
% 7.59/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.59/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3058,plain,
% 7.59/1.48      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2006,c_2019]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4286,plain,
% 7.59/1.48      ( k1_relat_1(sK4) = sK2
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | v1_funct_2(sK4,sK2,sK3) != iProver_top ),
% 7.59/1.48      inference(demodulation,[status(thm)],[c_4282,c_3058]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_30,negated_conjecture,
% 7.59/1.48      ( v1_funct_2(sK4,sK2,sK3) ),
% 7.59/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_35,plain,
% 7.59/1.48      ( v1_funct_2(sK4,sK2,sK3) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_7273,plain,
% 7.59/1.48      ( sK3 = k1_xboole_0 | k1_relat_1(sK4) = sK2 ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_4286,c_35]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_7274,plain,
% 7.59/1.48      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_7273]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_10,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.59/1.48      | ~ v1_funct_1(X2)
% 7.59/1.48      | ~ v1_funct_1(X1)
% 7.59/1.48      | ~ v1_relat_1(X1)
% 7.59/1.48      | ~ v1_relat_1(X2)
% 7.59/1.48      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2022,plain,
% 7.59/1.48      ( k1_funct_1(k5_relat_1(X0,X1),X2) = k1_funct_1(X1,k1_funct_1(X0,X2))
% 7.59/1.48      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 7.59/1.48      | v1_funct_1(X1) != iProver_top
% 7.59/1.48      | v1_funct_1(X0) != iProver_top
% 7.59/1.48      | v1_relat_1(X0) != iProver_top
% 7.59/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_7277,plain,
% 7.59/1.48      ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | r2_hidden(X1,sK2) != iProver_top
% 7.59/1.48      | v1_funct_1(X0) != iProver_top
% 7.59/1.48      | v1_funct_1(sK4) != iProver_top
% 7.59/1.48      | v1_relat_1(X0) != iProver_top
% 7.59/1.48      | v1_relat_1(sK4) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_7274,c_2022]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_31,negated_conjecture,
% 7.59/1.48      ( v1_funct_1(sK4) ),
% 7.59/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_34,plain,
% 7.59/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_36,plain,
% 7.59/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2,plain,
% 7.59/1.48      ( m1_subset_1(sK0(X0),X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2240,plain,
% 7.59/1.48      ( m1_subset_1(sK0(sK3),sK3) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_32,negated_conjecture,
% 7.59/1.48      ( ~ v1_xboole_0(sK3) ),
% 7.59/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_431,plain,
% 7.59/1.48      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | sK3 != X1 ),
% 7.59/1.48      inference(resolution_lifted,[status(thm)],[c_4,c_32]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_432,plain,
% 7.59/1.48      ( r2_hidden(X0,sK3) | ~ m1_subset_1(X0,sK3) ),
% 7.59/1.48      inference(unflattening,[status(thm)],[c_431]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2241,plain,
% 7.59/1.48      ( r2_hidden(sK0(sK3),sK3) | ~ m1_subset_1(sK0(sK3),sK3) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_432]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | v1_relat_1(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2273,plain,
% 7.59/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.59/1.48      | v1_relat_1(sK4) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2274,plain,
% 7.59/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.59/1.48      | v1_relat_1(sK4) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_2273]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1330,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | X2 != X1 ),
% 7.59/1.48      theory(equality) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2588,plain,
% 7.59/1.48      ( r2_hidden(sK0(sK3),X0) | ~ r2_hidden(sK0(sK3),sK3) | X0 != sK3 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_1330]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5136,plain,
% 7.59/1.48      ( r2_hidden(sK0(sK3),k1_relat_1(X0))
% 7.59/1.48      | ~ r2_hidden(sK0(sK3),sK3)
% 7.59/1.48      | k1_relat_1(X0) != sK3 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2588]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5141,plain,
% 7.59/1.48      ( r2_hidden(sK0(sK3),k1_relat_1(k1_xboole_0))
% 7.59/1.48      | ~ r2_hidden(sK0(sK3),sK3)
% 7.59/1.48      | k1_relat_1(k1_xboole_0) != sK3 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_5136]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3,plain,
% 7.59/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2026,plain,
% 7.59/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_13,plain,
% 7.59/1.48      ( v4_relat_1(X0,X1)
% 7.59/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.59/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_9,plain,
% 7.59/1.48      ( ~ v4_relat_1(X0,X1)
% 7.59/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.59/1.48      | ~ v1_relat_1(X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_450,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.59/1.48      | ~ v1_relat_1(X0) ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_13,c_9]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_454,plain,
% 7.59/1.48      ( r1_tarski(k1_relat_1(X0),X1)
% 7.59/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_450,c_12]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_455,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_454]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2001,plain,
% 7.59/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.59/1.48      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2410,plain,
% 7.59/1.48      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2026,c_2001]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2027,plain,
% 7.59/1.48      ( m1_subset_1(sK0(X0),X0) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2898,plain,
% 7.59/1.48      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2027,c_2003]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_11,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2021,plain,
% 7.59/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.59/1.48      | r1_tarski(X1,X0) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_6707,plain,
% 7.59/1.48      ( k1_xboole_0 = X0 | r1_tarski(X0,sK0(X0)) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2898,c_2021]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_7107,plain,
% 7.59/1.48      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2410,c_6707]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1326,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2516,plain,
% 7.59/1.48      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_1326]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_7333,plain,
% 7.59/1.48      ( k1_relat_1(X0) != X1 | k1_relat_1(X0) = sK3 | sK3 != X1 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2516]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_7334,plain,
% 7.59/1.48      ( k1_relat_1(k1_xboole_0) = sK3
% 7.59/1.48      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.59/1.48      | sK3 != k1_xboole_0 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_7333]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5125,plain,
% 7.59/1.48      ( ~ r2_hidden(sK0(sK3),X0) | ~ r1_tarski(X0,sK0(sK3)) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12002,plain,
% 7.59/1.48      ( ~ r2_hidden(sK0(sK3),k1_relat_1(X0))
% 7.59/1.48      | ~ r1_tarski(k1_relat_1(X0),sK0(sK3)) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_5125]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12005,plain,
% 7.59/1.48      ( ~ r2_hidden(sK0(sK3),k1_relat_1(k1_xboole_0))
% 7.59/1.48      | ~ r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_12002]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12003,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0(sK3),X1)))
% 7.59/1.48      | r1_tarski(k1_relat_1(X0),sK0(sK3)) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_455]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12009,plain,
% 7.59/1.48      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(sK3),k1_xboole_0)))
% 7.59/1.48      | r1_tarski(k1_relat_1(k1_xboole_0),sK0(sK3)) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_12003]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2260,plain,
% 7.59/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3731,plain,
% 7.59/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(X0),k1_xboole_0))) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2260]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_21440,plain,
% 7.59/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0(sK3),k1_xboole_0))) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_3731]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_28025,plain,
% 7.59/1.48      ( v1_relat_1(X0) != iProver_top
% 7.59/1.48      | k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 7.59/1.48      | r2_hidden(X1,sK2) != iProver_top
% 7.59/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_7277,c_34,c_36,c_2240,c_2241,c_2274,c_5141,c_7107,
% 7.59/1.48                 c_7334,c_12005,c_12009,c_21440]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_28026,plain,
% 7.59/1.48      ( k1_funct_1(X0,k1_funct_1(sK4,X1)) = k1_funct_1(k5_relat_1(sK4,X0),X1)
% 7.59/1.48      | r2_hidden(X1,sK2) != iProver_top
% 7.59/1.48      | v1_funct_1(X0) != iProver_top
% 7.59/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_28025]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_28035,plain,
% 7.59/1.48      ( k1_funct_1(k5_relat_1(sK4,X0),sK6) = k1_funct_1(X0,k1_funct_1(sK4,sK6))
% 7.59/1.48      | v1_funct_1(X0) != iProver_top
% 7.59/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_4599,c_28026]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_28917,plain,
% 7.59/1.48      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) = k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 7.59/1.48      | v1_relat_1(sK5) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2007,c_28035]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_27,negated_conjecture,
% 7.59/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.59/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2008,plain,
% 7.59/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3057,plain,
% 7.59/1.48      ( k1_relset_1(sK3,sK1,sK5) = k1_relat_1(sK5) ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2008,c_2019]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_25,negated_conjecture,
% 7.59/1.48      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2010,plain,
% 7.59/1.48      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relset_1(sK3,sK1,sK5)) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3361,plain,
% 7.59/1.48      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),k1_relat_1(sK5)) = iProver_top ),
% 7.59/1.48      inference(demodulation,[status(thm)],[c_3057,c_2010]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_15,plain,
% 7.59/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.59/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.59/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X4,X3))
% 7.59/1.48      | ~ v1_funct_1(X3)
% 7.59/1.48      | ~ v1_funct_1(X0)
% 7.59/1.48      | k1_partfun1(X1,X2,X2,X4,X0,X3) = k8_funct_2(X1,X2,X4,X0,X3)
% 7.59/1.48      | k1_xboole_0 = X2 ),
% 7.59/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2018,plain,
% 7.59/1.48      ( k1_partfun1(X0,X1,X1,X2,X3,X4) = k8_funct_2(X0,X1,X2,X3,X4)
% 7.59/1.48      | k1_xboole_0 = X1
% 7.59/1.48      | v1_funct_2(X3,X0,X1) != iProver_top
% 7.59/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.59/1.48      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 7.59/1.48      | v1_funct_1(X4) != iProver_top
% 7.59/1.48      | v1_funct_1(X3) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4392,plain,
% 7.59/1.48      ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | v1_funct_2(X1,X0,sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 7.59/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.59/1.48      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 7.59/1.48      | v1_funct_1(X1) != iProver_top
% 7.59/1.48      | v1_funct_1(sK5) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3057,c_2018]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_37,plain,
% 7.59/1.48      ( v1_funct_1(sK5) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_38,plain,
% 7.59/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8145,plain,
% 7.59/1.48      ( v1_funct_1(X1) != iProver_top
% 7.59/1.48      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 7.59/1.48      | k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | v1_funct_2(X1,X0,sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_4392,c_37,c_38]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8146,plain,
% 7.59/1.48      ( k1_partfun1(X0,sK3,sK3,sK1,X1,sK5) = k8_funct_2(X0,sK3,sK1,X1,sK5)
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | v1_funct_2(X1,X0,sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 7.59/1.48      | r1_tarski(k2_relset_1(X0,sK3,X1),k1_relat_1(sK5)) != iProver_top
% 7.59/1.48      | v1_funct_1(X1) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_8145]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8157,plain,
% 7.59/1.48      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k8_funct_2(sK2,sK3,sK1,sK4,sK5)
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.59/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_3361,c_8146]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_22,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.59/1.48      | ~ v1_funct_1(X3)
% 7.59/1.48      | ~ v1_funct_1(X0)
% 7.59/1.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2011,plain,
% 7.59/1.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.59/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.59/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.48      | v1_funct_1(X4) != iProver_top
% 7.59/1.48      | v1_funct_1(X5) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3433,plain,
% 7.59/1.48      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 7.59/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.48      | v1_funct_1(X2) != iProver_top
% 7.59/1.48      | v1_funct_1(sK5) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2008,c_2011]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4015,plain,
% 7.59/1.48      ( v1_funct_1(X2) != iProver_top
% 7.59/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.48      | k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_3433,c_37]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4016,plain,
% 7.59/1.48      ( k1_partfun1(X0,X1,sK3,sK1,X2,sK5) = k5_relat_1(X2,sK5)
% 7.59/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.59/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_4015]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4028,plain,
% 7.59/1.48      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 7.59/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_2006,c_4016]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2384,plain,
% 7.59/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.59/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.59/1.48      | ~ v1_funct_1(X0)
% 7.59/1.48      | ~ v1_funct_1(sK4)
% 7.59/1.48      | k1_partfun1(X3,X4,X1,X2,sK4,X0) = k5_relat_1(sK4,X0) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2561,plain,
% 7.59/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.59/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.59/1.48      | ~ v1_funct_1(sK4)
% 7.59/1.48      | ~ v1_funct_1(sK5)
% 7.59/1.48      | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2384]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2845,plain,
% 7.59/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.59/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.59/1.48      | ~ v1_funct_1(sK4)
% 7.59/1.48      | ~ v1_funct_1(sK5)
% 7.59/1.48      | k1_partfun1(sK2,sK3,X0,X1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2561]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2975,plain,
% 7.59/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 7.59/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.59/1.48      | ~ v1_funct_1(sK4)
% 7.59/1.48      | ~ v1_funct_1(sK5)
% 7.59/1.48      | k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_2845]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4098,plain,
% 7.59/1.48      ( k1_partfun1(sK2,sK3,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_4028,c_31,c_29,c_28,c_27,c_2975]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8158,plain,
% 7.59/1.48      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 7.59/1.48      | sK3 = k1_xboole_0
% 7.59/1.48      | v1_funct_2(sK4,sK2,sK3) != iProver_top
% 7.59/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 7.59/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.59/1.48      inference(light_normalisation,[status(thm)],[c_8157,c_4098]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8161,plain,
% 7.59/1.48      ( sK3 = k1_xboole_0
% 7.59/1.48      | k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_8158,c_34,c_35,c_36]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8162,plain,
% 7.59/1.48      ( k8_funct_2(sK2,sK3,sK1,sK4,sK5) = k5_relat_1(sK4,sK5)
% 7.59/1.48      | sK3 = k1_xboole_0 ),
% 7.59/1.48      inference(renaming,[status(thm)],[c_8161]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_23,negated_conjecture,
% 7.59/1.48      ( k1_funct_1(sK5,k1_funct_1(sK4,sK6)) != k1_funct_1(k8_funct_2(sK2,sK3,sK1,sK4,sK5),sK6) ),
% 7.59/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8165,plain,
% 7.59/1.48      ( k1_funct_1(k5_relat_1(sK4,sK5),sK6) != k1_funct_1(sK5,k1_funct_1(sK4,sK6))
% 7.59/1.48      | sK3 = k1_xboole_0 ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_8162,c_23]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2270,plain,
% 7.59/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.59/1.48      | v1_relat_1(sK5) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_12]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2271,plain,
% 7.59/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.59/1.48      | v1_relat_1(sK5) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_2270]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(contradiction,plain,
% 7.59/1.48      ( $false ),
% 7.59/1.48      inference(minisat,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_28917,c_21440,c_12009,c_12005,c_8165,c_7334,c_7107,
% 7.59/1.48                 c_5141,c_2271,c_2241,c_2240,c_38]) ).
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  ------                               Statistics
% 7.59/1.48  
% 7.59/1.48  ------ General
% 7.59/1.48  
% 7.59/1.48  abstr_ref_over_cycles:                  0
% 7.59/1.48  abstr_ref_under_cycles:                 0
% 7.59/1.48  gc_basic_clause_elim:                   0
% 7.59/1.48  forced_gc_time:                         0
% 7.59/1.48  parsing_time:                           0.009
% 7.59/1.48  unif_index_cands_time:                  0.
% 7.59/1.48  unif_index_add_time:                    0.
% 7.59/1.48  orderings_time:                         0.
% 7.59/1.48  out_proof_time:                         0.011
% 7.59/1.48  total_time:                             0.746
% 7.59/1.48  num_of_symbols:                         56
% 7.59/1.48  num_of_terms:                           23497
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing
% 7.59/1.48  
% 7.59/1.48  num_of_splits:                          0
% 7.59/1.48  num_of_split_atoms:                     0
% 7.59/1.48  num_of_reused_defs:                     0
% 7.59/1.48  num_eq_ax_congr_red:                    38
% 7.59/1.48  num_of_sem_filtered_clauses:            1
% 7.59/1.48  num_of_subtypes:                        0
% 7.59/1.48  monotx_restored_types:                  0
% 7.59/1.48  sat_num_of_epr_types:                   0
% 7.59/1.48  sat_num_of_non_cyclic_types:            0
% 7.59/1.48  sat_guarded_non_collapsed_types:        0
% 7.59/1.48  num_pure_diseq_elim:                    0
% 7.59/1.48  simp_replaced_by:                       0
% 7.59/1.48  res_preprocessed:                       150
% 7.59/1.48  prep_upred:                             0
% 7.59/1.48  prep_unflattend:                        88
% 7.59/1.48  smt_new_axioms:                         0
% 7.59/1.48  pred_elim_cands:                        6
% 7.59/1.48  pred_elim:                              2
% 7.59/1.48  pred_elim_cl:                           3
% 7.59/1.48  pred_elim_cycles:                       6
% 7.59/1.48  merged_defs:                            8
% 7.59/1.48  merged_defs_ncl:                        0
% 7.59/1.48  bin_hyper_res:                          8
% 7.59/1.48  prep_cycles:                            4
% 7.59/1.48  pred_elim_time:                         0.014
% 7.59/1.48  splitting_time:                         0.
% 7.59/1.48  sem_filter_time:                        0.
% 7.59/1.48  monotx_time:                            0.001
% 7.59/1.48  subtype_inf_time:                       0.
% 7.59/1.48  
% 7.59/1.48  ------ Problem properties
% 7.59/1.48  
% 7.59/1.48  clauses:                                30
% 7.59/1.48  conjectures:                            9
% 7.59/1.48  epr:                                    9
% 7.59/1.48  horn:                                   24
% 7.59/1.48  ground:                                 9
% 7.59/1.48  unary:                                  11
% 7.59/1.48  binary:                                 7
% 7.59/1.48  lits:                                   74
% 7.59/1.48  lits_eq:                                17
% 7.59/1.48  fd_pure:                                0
% 7.59/1.48  fd_pseudo:                              0
% 7.59/1.48  fd_cond:                                5
% 7.59/1.48  fd_pseudo_cond:                         0
% 7.59/1.48  ac_symbols:                             0
% 7.59/1.48  
% 7.59/1.48  ------ Propositional Solver
% 7.59/1.48  
% 7.59/1.48  prop_solver_calls:                      30
% 7.59/1.48  prop_fast_solver_calls:                 1797
% 7.59/1.48  smt_solver_calls:                       0
% 7.59/1.48  smt_fast_solver_calls:                  0
% 7.59/1.48  prop_num_of_clauses:                    10119
% 7.59/1.48  prop_preprocess_simplified:             18272
% 7.59/1.48  prop_fo_subsumed:                       51
% 7.59/1.48  prop_solver_time:                       0.
% 7.59/1.48  smt_solver_time:                        0.
% 7.59/1.48  smt_fast_solver_time:                   0.
% 7.59/1.48  prop_fast_solver_time:                  0.
% 7.59/1.48  prop_unsat_core_time:                   0.001
% 7.59/1.48  
% 7.59/1.48  ------ QBF
% 7.59/1.48  
% 7.59/1.48  qbf_q_res:                              0
% 7.59/1.48  qbf_num_tautologies:                    0
% 7.59/1.48  qbf_prep_cycles:                        0
% 7.59/1.48  
% 7.59/1.48  ------ BMC1
% 7.59/1.48  
% 7.59/1.48  bmc1_current_bound:                     -1
% 7.59/1.48  bmc1_last_solved_bound:                 -1
% 7.59/1.48  bmc1_unsat_core_size:                   -1
% 7.59/1.48  bmc1_unsat_core_parents_size:           -1
% 7.59/1.48  bmc1_merge_next_fun:                    0
% 7.59/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.59/1.48  
% 7.59/1.48  ------ Instantiation
% 7.59/1.48  
% 7.59/1.48  inst_num_of_clauses:                    2814
% 7.59/1.48  inst_num_in_passive:                    256
% 7.59/1.48  inst_num_in_active:                     1259
% 7.59/1.48  inst_num_in_unprocessed:                1304
% 7.59/1.48  inst_num_of_loops:                      1420
% 7.59/1.48  inst_num_of_learning_restarts:          0
% 7.59/1.48  inst_num_moves_active_passive:          158
% 7.59/1.48  inst_lit_activity:                      0
% 7.59/1.48  inst_lit_activity_moves:                0
% 7.59/1.48  inst_num_tautologies:                   0
% 7.59/1.48  inst_num_prop_implied:                  0
% 7.59/1.48  inst_num_existing_simplified:           0
% 7.59/1.48  inst_num_eq_res_simplified:             0
% 7.59/1.48  inst_num_child_elim:                    0
% 7.59/1.48  inst_num_of_dismatching_blockings:      2205
% 7.59/1.48  inst_num_of_non_proper_insts:           2996
% 7.59/1.48  inst_num_of_duplicates:                 0
% 7.59/1.48  inst_inst_num_from_inst_to_res:         0
% 7.59/1.48  inst_dismatching_checking_time:         0.
% 7.59/1.48  
% 7.59/1.48  ------ Resolution
% 7.59/1.48  
% 7.59/1.48  res_num_of_clauses:                     0
% 7.59/1.48  res_num_in_passive:                     0
% 7.59/1.48  res_num_in_active:                      0
% 7.59/1.48  res_num_of_loops:                       154
% 7.59/1.48  res_forward_subset_subsumed:            171
% 7.59/1.48  res_backward_subset_subsumed:           28
% 7.59/1.48  res_forward_subsumed:                   0
% 7.59/1.48  res_backward_subsumed:                  0
% 7.59/1.48  res_forward_subsumption_resolution:     0
% 7.59/1.48  res_backward_subsumption_resolution:    0
% 7.59/1.48  res_clause_to_clause_subsumption:       2297
% 7.59/1.48  res_orphan_elimination:                 0
% 7.59/1.48  res_tautology_del:                      208
% 7.59/1.48  res_num_eq_res_simplified:              0
% 7.59/1.48  res_num_sel_changes:                    0
% 7.59/1.48  res_moves_from_active_to_pass:          0
% 7.59/1.48  
% 7.59/1.48  ------ Superposition
% 7.59/1.48  
% 7.59/1.48  sup_time_total:                         0.
% 7.59/1.48  sup_time_generating:                    0.
% 7.59/1.48  sup_time_sim_full:                      0.
% 7.59/1.48  sup_time_sim_immed:                     0.
% 7.59/1.48  
% 7.59/1.48  sup_num_of_clauses:                     653
% 7.59/1.48  sup_num_in_active:                      283
% 7.59/1.48  sup_num_in_passive:                     370
% 7.59/1.48  sup_num_of_loops:                       283
% 7.59/1.48  sup_fw_superposition:                   581
% 7.59/1.48  sup_bw_superposition:                   273
% 7.59/1.48  sup_immediate_simplified:               130
% 7.59/1.48  sup_given_eliminated:                   0
% 7.59/1.48  comparisons_done:                       0
% 7.59/1.48  comparisons_avoided:                    42
% 7.59/1.48  
% 7.59/1.48  ------ Simplifications
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  sim_fw_subset_subsumed:                 25
% 7.59/1.48  sim_bw_subset_subsumed:                 0
% 7.59/1.48  sim_fw_subsumed:                        102
% 7.59/1.48  sim_bw_subsumed:                        0
% 7.59/1.48  sim_fw_subsumption_res:                 4
% 7.59/1.48  sim_bw_subsumption_res:                 0
% 7.59/1.48  sim_tautology_del:                      4
% 7.59/1.48  sim_eq_tautology_del:                   3
% 7.59/1.48  sim_eq_res_simp:                        0
% 7.59/1.48  sim_fw_demodulated:                     6
% 7.59/1.48  sim_bw_demodulated:                     1
% 7.59/1.48  sim_light_normalised:                   2
% 7.59/1.48  sim_joinable_taut:                      0
% 7.59/1.48  sim_joinable_simp:                      0
% 7.59/1.48  sim_ac_normalised:                      0
% 7.59/1.48  sim_smt_subsumption:                    0
% 7.59/1.48  
%------------------------------------------------------------------------------
