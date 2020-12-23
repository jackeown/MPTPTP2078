%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:53 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  185 (1656 expanded)
%              Number of clauses        :  114 ( 494 expanded)
%              Number of leaves         :   23 ( 547 expanded)
%              Depth                    :   22
%              Number of atoms          :  644 (11972 expanded)
%              Number of equality atoms :  306 (3319 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
          & k1_xboole_0 != X1
          & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
          & m1_subset_1(X5,X1) )
     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) != k7_partfun1(X0,X4,k1_funct_1(X3,sK5))
        & k1_xboole_0 != X1
        & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        & m1_subset_1(sK5,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
            ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) != k7_partfun1(X0,sK4,k1_funct_1(X3,X5))
            & k1_xboole_0 != X1
            & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4))
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
                ( k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK3,X5))
                & k1_xboole_0 != X1
                & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4))
                & m1_subset_1(X5,X1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
            & v1_funct_1(X4) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK3,X1,X2)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
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

fof(f46,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f45,f44,f43,f42])).

fof(f74,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f67,plain,(
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

fof(f68,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1673,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1693,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2547,plain,
    ( r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1673,c_1693])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1925,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1926,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1925])).

cnf(c_1955,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | r2_hidden(sK5,sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1956,plain,
    ( m1_subset_1(sK5,sK1) != iProver_top
    | r2_hidden(sK5,sK1) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_3009,plain,
    ( r2_hidden(sK5,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2547,c_37,c_22,c_1926,c_1956])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1672,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1686,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2300,plain,
    ( v5_relat_1(sK4,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_1686])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1670,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1678,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3892,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1670,c_1678])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1685,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2538,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1670,c_1685])).

cnf(c_3896,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3892,c_2538])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4104,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3896,c_33])).

cnf(c_4105,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4104])).

cnf(c_2537,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1672,c_1685])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1684,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2378,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1670,c_1684])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1674,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2427,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2378,c_1674])).

cnf(c_2757,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2537,c_2427])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1691,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3565,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2757,c_1691])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1931,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2313,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_2314,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2313])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2432,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2433,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_4560,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3565,c_34,c_2314,c_2433])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1688,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1677,plain,
    ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
    | v5_relat_1(X1,X0) != iProver_top
    | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4054,plain,
    ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | v5_relat_1(X1,X0) != iProver_top
    | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_1677])).

cnf(c_6532,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4560,c_4054])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2310,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_2311,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2310])).

cnf(c_2429,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2430,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2429])).

cnf(c_7091,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6532,c_32,c_34,c_35,c_36,c_2311,c_2314,c_2430,c_2433])).

cnf(c_7102,plain,
    ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
    | sK2 = k1_xboole_0
    | v5_relat_1(sK4,X0) != iProver_top
    | r2_hidden(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4105,c_7091])).

cnf(c_7151,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | sK2 = k1_xboole_0
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_7102])).

cnf(c_7658,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3009,c_7151])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_1675,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2460,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_1675])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1128,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1159,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_1129,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1982,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_1983,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_3656,plain,
    ( m1_subset_1(X2,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2460,c_31,c_32,c_33,c_34,c_22,c_1159,c_1983])).

cnf(c_3657,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
    | m1_subset_1(X2,sK1) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3656])).

cnf(c_3668,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_3657])).

cnf(c_3698,plain,
    ( m1_subset_1(X0,sK1) != iProver_top
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3668,c_35,c_36,c_2757])).

cnf(c_3699,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
    | m1_subset_1(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3698])).

cnf(c_3707,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1673,c_3699])).

cnf(c_21,negated_conjecture,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3814,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_3707,c_21])).

cnf(c_7726,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7658,c_3814])).

cnf(c_7774,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7726,c_1670])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1694,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1676,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3306,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_1693])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1687,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4612,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X3,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(X2,k3_funct_2(X1,X2,X0,X3)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3306,c_1687])).

cnf(c_5437,plain,
    ( v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1694,c_4612])).

cnf(c_8067,plain,
    ( v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,sK1) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7774,c_5437])).

cnf(c_2198,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_2659,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_3037,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_3038,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3037])).

cnf(c_1141,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2050,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | X0 != sK3
    | X2 != sK2
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_2528,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | X1 != sK2
    | X0 != sK1
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_3021,plain,
    ( v1_funct_2(sK3,X0,k1_xboole_0)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | X0 != sK1
    | sK3 != sK3
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_4742,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | v1_funct_2(sK3,sK1,k1_xboole_0)
    | sK3 != sK3
    | sK1 != sK1
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_3021])).

cnf(c_4743,plain,
    ( sK3 != sK3
    | sK1 != sK1
    | k1_xboole_0 != sK2
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK3,sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4742])).

cnf(c_1667,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7776,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7726,c_1667])).

cnf(c_9092,plain,
    ( m1_subset_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8067,c_32,c_33,c_22,c_1159,c_1926,c_2198,c_2659,c_3038,c_3814,c_4743,c_7658,c_7776])).

cnf(c_9100,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1673,c_9092])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.50/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.02  
% 3.50/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/1.02  
% 3.50/1.02  ------  iProver source info
% 3.50/1.02  
% 3.50/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.50/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/1.02  git: non_committed_changes: false
% 3.50/1.02  git: last_make_outside_of_git: false
% 3.50/1.02  
% 3.50/1.02  ------ 
% 3.50/1.02  
% 3.50/1.02  ------ Input Options
% 3.50/1.02  
% 3.50/1.02  --out_options                           all
% 3.50/1.02  --tptp_safe_out                         true
% 3.50/1.02  --problem_path                          ""
% 3.50/1.02  --include_path                          ""
% 3.50/1.02  --clausifier                            res/vclausify_rel
% 3.50/1.02  --clausifier_options                    --mode clausify
% 3.50/1.02  --stdin                                 false
% 3.50/1.02  --stats_out                             all
% 3.50/1.02  
% 3.50/1.02  ------ General Options
% 3.50/1.02  
% 3.50/1.02  --fof                                   false
% 3.50/1.02  --time_out_real                         305.
% 3.50/1.02  --time_out_virtual                      -1.
% 3.50/1.02  --symbol_type_check                     false
% 3.50/1.02  --clausify_out                          false
% 3.50/1.02  --sig_cnt_out                           false
% 3.50/1.02  --trig_cnt_out                          false
% 3.50/1.02  --trig_cnt_out_tolerance                1.
% 3.50/1.02  --trig_cnt_out_sk_spl                   false
% 3.50/1.02  --abstr_cl_out                          false
% 3.50/1.02  
% 3.50/1.02  ------ Global Options
% 3.50/1.02  
% 3.50/1.02  --schedule                              default
% 3.50/1.02  --add_important_lit                     false
% 3.50/1.02  --prop_solver_per_cl                    1000
% 3.50/1.02  --min_unsat_core                        false
% 3.50/1.02  --soft_assumptions                      false
% 3.50/1.02  --soft_lemma_size                       3
% 3.50/1.02  --prop_impl_unit_size                   0
% 3.50/1.02  --prop_impl_unit                        []
% 3.50/1.02  --share_sel_clauses                     true
% 3.50/1.02  --reset_solvers                         false
% 3.50/1.02  --bc_imp_inh                            [conj_cone]
% 3.50/1.02  --conj_cone_tolerance                   3.
% 3.50/1.02  --extra_neg_conj                        none
% 3.50/1.02  --large_theory_mode                     true
% 3.50/1.02  --prolific_symb_bound                   200
% 3.50/1.02  --lt_threshold                          2000
% 3.50/1.02  --clause_weak_htbl                      true
% 3.50/1.02  --gc_record_bc_elim                     false
% 3.50/1.02  
% 3.50/1.02  ------ Preprocessing Options
% 3.50/1.02  
% 3.50/1.02  --preprocessing_flag                    true
% 3.50/1.02  --time_out_prep_mult                    0.1
% 3.50/1.02  --splitting_mode                        input
% 3.50/1.02  --splitting_grd                         true
% 3.50/1.02  --splitting_cvd                         false
% 3.50/1.02  --splitting_cvd_svl                     false
% 3.50/1.02  --splitting_nvd                         32
% 3.50/1.02  --sub_typing                            true
% 3.50/1.02  --prep_gs_sim                           true
% 3.50/1.02  --prep_unflatten                        true
% 3.50/1.02  --prep_res_sim                          true
% 3.50/1.02  --prep_upred                            true
% 3.50/1.02  --prep_sem_filter                       exhaustive
% 3.50/1.02  --prep_sem_filter_out                   false
% 3.50/1.02  --pred_elim                             true
% 3.50/1.02  --res_sim_input                         true
% 3.50/1.02  --eq_ax_congr_red                       true
% 3.50/1.02  --pure_diseq_elim                       true
% 3.50/1.02  --brand_transform                       false
% 3.50/1.02  --non_eq_to_eq                          false
% 3.50/1.02  --prep_def_merge                        true
% 3.50/1.02  --prep_def_merge_prop_impl              false
% 3.50/1.02  --prep_def_merge_mbd                    true
% 3.50/1.02  --prep_def_merge_tr_red                 false
% 3.50/1.02  --prep_def_merge_tr_cl                  false
% 3.50/1.02  --smt_preprocessing                     true
% 3.50/1.02  --smt_ac_axioms                         fast
% 3.50/1.02  --preprocessed_out                      false
% 3.50/1.02  --preprocessed_stats                    false
% 3.50/1.02  
% 3.50/1.02  ------ Abstraction refinement Options
% 3.50/1.02  
% 3.50/1.02  --abstr_ref                             []
% 3.50/1.02  --abstr_ref_prep                        false
% 3.50/1.02  --abstr_ref_until_sat                   false
% 3.50/1.02  --abstr_ref_sig_restrict                funpre
% 3.50/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.02  --abstr_ref_under                       []
% 3.50/1.02  
% 3.50/1.02  ------ SAT Options
% 3.50/1.02  
% 3.50/1.02  --sat_mode                              false
% 3.50/1.02  --sat_fm_restart_options                ""
% 3.50/1.02  --sat_gr_def                            false
% 3.50/1.02  --sat_epr_types                         true
% 3.50/1.02  --sat_non_cyclic_types                  false
% 3.50/1.02  --sat_finite_models                     false
% 3.50/1.02  --sat_fm_lemmas                         false
% 3.50/1.02  --sat_fm_prep                           false
% 3.50/1.02  --sat_fm_uc_incr                        true
% 3.50/1.02  --sat_out_model                         small
% 3.50/1.02  --sat_out_clauses                       false
% 3.50/1.02  
% 3.50/1.02  ------ QBF Options
% 3.50/1.02  
% 3.50/1.02  --qbf_mode                              false
% 3.50/1.02  --qbf_elim_univ                         false
% 3.50/1.02  --qbf_dom_inst                          none
% 3.50/1.02  --qbf_dom_pre_inst                      false
% 3.50/1.02  --qbf_sk_in                             false
% 3.50/1.02  --qbf_pred_elim                         true
% 3.50/1.02  --qbf_split                             512
% 3.50/1.02  
% 3.50/1.02  ------ BMC1 Options
% 3.50/1.02  
% 3.50/1.02  --bmc1_incremental                      false
% 3.50/1.02  --bmc1_axioms                           reachable_all
% 3.50/1.02  --bmc1_min_bound                        0
% 3.50/1.02  --bmc1_max_bound                        -1
% 3.50/1.02  --bmc1_max_bound_default                -1
% 3.50/1.02  --bmc1_symbol_reachability              true
% 3.50/1.02  --bmc1_property_lemmas                  false
% 3.50/1.02  --bmc1_k_induction                      false
% 3.50/1.02  --bmc1_non_equiv_states                 false
% 3.50/1.02  --bmc1_deadlock                         false
% 3.50/1.02  --bmc1_ucm                              false
% 3.50/1.02  --bmc1_add_unsat_core                   none
% 3.50/1.02  --bmc1_unsat_core_children              false
% 3.50/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.02  --bmc1_out_stat                         full
% 3.50/1.02  --bmc1_ground_init                      false
% 3.50/1.02  --bmc1_pre_inst_next_state              false
% 3.50/1.02  --bmc1_pre_inst_state                   false
% 3.50/1.02  --bmc1_pre_inst_reach_state             false
% 3.50/1.02  --bmc1_out_unsat_core                   false
% 3.50/1.02  --bmc1_aig_witness_out                  false
% 3.50/1.02  --bmc1_verbose                          false
% 3.50/1.02  --bmc1_dump_clauses_tptp                false
% 3.50/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.02  --bmc1_dump_file                        -
% 3.50/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.02  --bmc1_ucm_extend_mode                  1
% 3.50/1.02  --bmc1_ucm_init_mode                    2
% 3.50/1.02  --bmc1_ucm_cone_mode                    none
% 3.50/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.02  --bmc1_ucm_relax_model                  4
% 3.50/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.02  --bmc1_ucm_layered_model                none
% 3.50/1.02  --bmc1_ucm_max_lemma_size               10
% 3.50/1.02  
% 3.50/1.02  ------ AIG Options
% 3.50/1.02  
% 3.50/1.02  --aig_mode                              false
% 3.50/1.02  
% 3.50/1.02  ------ Instantiation Options
% 3.50/1.02  
% 3.50/1.02  --instantiation_flag                    true
% 3.50/1.02  --inst_sos_flag                         false
% 3.50/1.02  --inst_sos_phase                        true
% 3.50/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.02  --inst_lit_sel_side                     num_symb
% 3.50/1.02  --inst_solver_per_active                1400
% 3.50/1.02  --inst_solver_calls_frac                1.
% 3.50/1.02  --inst_passive_queue_type               priority_queues
% 3.50/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.02  --inst_passive_queues_freq              [25;2]
% 3.50/1.02  --inst_dismatching                      true
% 3.50/1.02  --inst_eager_unprocessed_to_passive     true
% 3.50/1.02  --inst_prop_sim_given                   true
% 3.50/1.02  --inst_prop_sim_new                     false
% 3.50/1.02  --inst_subs_new                         false
% 3.50/1.02  --inst_eq_res_simp                      false
% 3.50/1.02  --inst_subs_given                       false
% 3.50/1.02  --inst_orphan_elimination               true
% 3.50/1.02  --inst_learning_loop_flag               true
% 3.50/1.02  --inst_learning_start                   3000
% 3.50/1.02  --inst_learning_factor                  2
% 3.50/1.02  --inst_start_prop_sim_after_learn       3
% 3.50/1.02  --inst_sel_renew                        solver
% 3.50/1.02  --inst_lit_activity_flag                true
% 3.50/1.02  --inst_restr_to_given                   false
% 3.50/1.02  --inst_activity_threshold               500
% 3.50/1.02  --inst_out_proof                        true
% 3.50/1.02  
% 3.50/1.02  ------ Resolution Options
% 3.50/1.02  
% 3.50/1.02  --resolution_flag                       true
% 3.50/1.02  --res_lit_sel                           adaptive
% 3.50/1.02  --res_lit_sel_side                      none
% 3.50/1.02  --res_ordering                          kbo
% 3.50/1.02  --res_to_prop_solver                    active
% 3.50/1.02  --res_prop_simpl_new                    false
% 3.50/1.02  --res_prop_simpl_given                  true
% 3.50/1.02  --res_passive_queue_type                priority_queues
% 3.50/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.02  --res_passive_queues_freq               [15;5]
% 3.50/1.02  --res_forward_subs                      full
% 3.50/1.02  --res_backward_subs                     full
% 3.50/1.02  --res_forward_subs_resolution           true
% 3.50/1.02  --res_backward_subs_resolution          true
% 3.50/1.02  --res_orphan_elimination                true
% 3.50/1.02  --res_time_limit                        2.
% 3.50/1.02  --res_out_proof                         true
% 3.50/1.02  
% 3.50/1.02  ------ Superposition Options
% 3.50/1.02  
% 3.50/1.02  --superposition_flag                    true
% 3.50/1.02  --sup_passive_queue_type                priority_queues
% 3.50/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.02  --demod_completeness_check              fast
% 3.50/1.02  --demod_use_ground                      true
% 3.50/1.02  --sup_to_prop_solver                    passive
% 3.50/1.02  --sup_prop_simpl_new                    true
% 3.50/1.02  --sup_prop_simpl_given                  true
% 3.50/1.02  --sup_fun_splitting                     false
% 3.50/1.02  --sup_smt_interval                      50000
% 3.50/1.02  
% 3.50/1.02  ------ Superposition Simplification Setup
% 3.50/1.02  
% 3.50/1.02  --sup_indices_passive                   []
% 3.50/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.02  --sup_full_bw                           [BwDemod]
% 3.50/1.02  --sup_immed_triv                        [TrivRules]
% 3.50/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.02  --sup_immed_bw_main                     []
% 3.50/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.02  
% 3.50/1.02  ------ Combination Options
% 3.50/1.02  
% 3.50/1.02  --comb_res_mult                         3
% 3.50/1.02  --comb_sup_mult                         2
% 3.50/1.02  --comb_inst_mult                        10
% 3.50/1.02  
% 3.50/1.02  ------ Debug Options
% 3.50/1.02  
% 3.50/1.02  --dbg_backtrace                         false
% 3.50/1.02  --dbg_dump_prop_clauses                 false
% 3.50/1.02  --dbg_dump_prop_clauses_file            -
% 3.50/1.02  --dbg_out_stat                          false
% 3.50/1.02  ------ Parsing...
% 3.50/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/1.02  
% 3.50/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.50/1.02  
% 3.50/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/1.02  
% 3.50/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/1.02  ------ Proving...
% 3.50/1.02  ------ Problem Properties 
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  clauses                                 31
% 3.50/1.02  conjectures                             10
% 3.50/1.02  EPR                                     10
% 3.50/1.02  Horn                                    24
% 3.50/1.02  unary                                   12
% 3.50/1.02  binary                                  5
% 3.50/1.02  lits                                    81
% 3.50/1.02  lits eq                                 17
% 3.50/1.02  fd_pure                                 0
% 3.50/1.02  fd_pseudo                               0
% 3.50/1.02  fd_cond                                 5
% 3.50/1.02  fd_pseudo_cond                          0
% 3.50/1.02  AC symbols                              0
% 3.50/1.02  
% 3.50/1.02  ------ Schedule dynamic 5 is on 
% 3.50/1.02  
% 3.50/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  ------ 
% 3.50/1.02  Current options:
% 3.50/1.02  ------ 
% 3.50/1.02  
% 3.50/1.02  ------ Input Options
% 3.50/1.02  
% 3.50/1.02  --out_options                           all
% 3.50/1.02  --tptp_safe_out                         true
% 3.50/1.02  --problem_path                          ""
% 3.50/1.02  --include_path                          ""
% 3.50/1.02  --clausifier                            res/vclausify_rel
% 3.50/1.02  --clausifier_options                    --mode clausify
% 3.50/1.02  --stdin                                 false
% 3.50/1.02  --stats_out                             all
% 3.50/1.02  
% 3.50/1.02  ------ General Options
% 3.50/1.02  
% 3.50/1.02  --fof                                   false
% 3.50/1.02  --time_out_real                         305.
% 3.50/1.02  --time_out_virtual                      -1.
% 3.50/1.02  --symbol_type_check                     false
% 3.50/1.02  --clausify_out                          false
% 3.50/1.02  --sig_cnt_out                           false
% 3.50/1.02  --trig_cnt_out                          false
% 3.50/1.02  --trig_cnt_out_tolerance                1.
% 3.50/1.02  --trig_cnt_out_sk_spl                   false
% 3.50/1.02  --abstr_cl_out                          false
% 3.50/1.02  
% 3.50/1.02  ------ Global Options
% 3.50/1.02  
% 3.50/1.02  --schedule                              default
% 3.50/1.02  --add_important_lit                     false
% 3.50/1.02  --prop_solver_per_cl                    1000
% 3.50/1.02  --min_unsat_core                        false
% 3.50/1.02  --soft_assumptions                      false
% 3.50/1.02  --soft_lemma_size                       3
% 3.50/1.02  --prop_impl_unit_size                   0
% 3.50/1.02  --prop_impl_unit                        []
% 3.50/1.02  --share_sel_clauses                     true
% 3.50/1.02  --reset_solvers                         false
% 3.50/1.02  --bc_imp_inh                            [conj_cone]
% 3.50/1.02  --conj_cone_tolerance                   3.
% 3.50/1.02  --extra_neg_conj                        none
% 3.50/1.02  --large_theory_mode                     true
% 3.50/1.02  --prolific_symb_bound                   200
% 3.50/1.02  --lt_threshold                          2000
% 3.50/1.02  --clause_weak_htbl                      true
% 3.50/1.02  --gc_record_bc_elim                     false
% 3.50/1.02  
% 3.50/1.02  ------ Preprocessing Options
% 3.50/1.02  
% 3.50/1.02  --preprocessing_flag                    true
% 3.50/1.02  --time_out_prep_mult                    0.1
% 3.50/1.02  --splitting_mode                        input
% 3.50/1.02  --splitting_grd                         true
% 3.50/1.02  --splitting_cvd                         false
% 3.50/1.02  --splitting_cvd_svl                     false
% 3.50/1.02  --splitting_nvd                         32
% 3.50/1.02  --sub_typing                            true
% 3.50/1.02  --prep_gs_sim                           true
% 3.50/1.02  --prep_unflatten                        true
% 3.50/1.02  --prep_res_sim                          true
% 3.50/1.02  --prep_upred                            true
% 3.50/1.02  --prep_sem_filter                       exhaustive
% 3.50/1.02  --prep_sem_filter_out                   false
% 3.50/1.02  --pred_elim                             true
% 3.50/1.02  --res_sim_input                         true
% 3.50/1.02  --eq_ax_congr_red                       true
% 3.50/1.02  --pure_diseq_elim                       true
% 3.50/1.02  --brand_transform                       false
% 3.50/1.02  --non_eq_to_eq                          false
% 3.50/1.02  --prep_def_merge                        true
% 3.50/1.02  --prep_def_merge_prop_impl              false
% 3.50/1.02  --prep_def_merge_mbd                    true
% 3.50/1.02  --prep_def_merge_tr_red                 false
% 3.50/1.02  --prep_def_merge_tr_cl                  false
% 3.50/1.02  --smt_preprocessing                     true
% 3.50/1.02  --smt_ac_axioms                         fast
% 3.50/1.02  --preprocessed_out                      false
% 3.50/1.02  --preprocessed_stats                    false
% 3.50/1.02  
% 3.50/1.02  ------ Abstraction refinement Options
% 3.50/1.02  
% 3.50/1.02  --abstr_ref                             []
% 3.50/1.02  --abstr_ref_prep                        false
% 3.50/1.02  --abstr_ref_until_sat                   false
% 3.50/1.02  --abstr_ref_sig_restrict                funpre
% 3.50/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/1.02  --abstr_ref_under                       []
% 3.50/1.02  
% 3.50/1.02  ------ SAT Options
% 3.50/1.02  
% 3.50/1.02  --sat_mode                              false
% 3.50/1.02  --sat_fm_restart_options                ""
% 3.50/1.02  --sat_gr_def                            false
% 3.50/1.02  --sat_epr_types                         true
% 3.50/1.02  --sat_non_cyclic_types                  false
% 3.50/1.02  --sat_finite_models                     false
% 3.50/1.02  --sat_fm_lemmas                         false
% 3.50/1.02  --sat_fm_prep                           false
% 3.50/1.02  --sat_fm_uc_incr                        true
% 3.50/1.02  --sat_out_model                         small
% 3.50/1.02  --sat_out_clauses                       false
% 3.50/1.02  
% 3.50/1.02  ------ QBF Options
% 3.50/1.02  
% 3.50/1.02  --qbf_mode                              false
% 3.50/1.02  --qbf_elim_univ                         false
% 3.50/1.02  --qbf_dom_inst                          none
% 3.50/1.02  --qbf_dom_pre_inst                      false
% 3.50/1.02  --qbf_sk_in                             false
% 3.50/1.02  --qbf_pred_elim                         true
% 3.50/1.02  --qbf_split                             512
% 3.50/1.02  
% 3.50/1.02  ------ BMC1 Options
% 3.50/1.02  
% 3.50/1.02  --bmc1_incremental                      false
% 3.50/1.02  --bmc1_axioms                           reachable_all
% 3.50/1.02  --bmc1_min_bound                        0
% 3.50/1.02  --bmc1_max_bound                        -1
% 3.50/1.02  --bmc1_max_bound_default                -1
% 3.50/1.02  --bmc1_symbol_reachability              true
% 3.50/1.02  --bmc1_property_lemmas                  false
% 3.50/1.02  --bmc1_k_induction                      false
% 3.50/1.02  --bmc1_non_equiv_states                 false
% 3.50/1.02  --bmc1_deadlock                         false
% 3.50/1.02  --bmc1_ucm                              false
% 3.50/1.02  --bmc1_add_unsat_core                   none
% 3.50/1.02  --bmc1_unsat_core_children              false
% 3.50/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/1.02  --bmc1_out_stat                         full
% 3.50/1.02  --bmc1_ground_init                      false
% 3.50/1.02  --bmc1_pre_inst_next_state              false
% 3.50/1.02  --bmc1_pre_inst_state                   false
% 3.50/1.02  --bmc1_pre_inst_reach_state             false
% 3.50/1.02  --bmc1_out_unsat_core                   false
% 3.50/1.02  --bmc1_aig_witness_out                  false
% 3.50/1.02  --bmc1_verbose                          false
% 3.50/1.02  --bmc1_dump_clauses_tptp                false
% 3.50/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.50/1.02  --bmc1_dump_file                        -
% 3.50/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.50/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.50/1.02  --bmc1_ucm_extend_mode                  1
% 3.50/1.02  --bmc1_ucm_init_mode                    2
% 3.50/1.02  --bmc1_ucm_cone_mode                    none
% 3.50/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.50/1.02  --bmc1_ucm_relax_model                  4
% 3.50/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.50/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/1.02  --bmc1_ucm_layered_model                none
% 3.50/1.02  --bmc1_ucm_max_lemma_size               10
% 3.50/1.02  
% 3.50/1.02  ------ AIG Options
% 3.50/1.02  
% 3.50/1.02  --aig_mode                              false
% 3.50/1.02  
% 3.50/1.02  ------ Instantiation Options
% 3.50/1.02  
% 3.50/1.02  --instantiation_flag                    true
% 3.50/1.02  --inst_sos_flag                         false
% 3.50/1.02  --inst_sos_phase                        true
% 3.50/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/1.02  --inst_lit_sel_side                     none
% 3.50/1.02  --inst_solver_per_active                1400
% 3.50/1.02  --inst_solver_calls_frac                1.
% 3.50/1.02  --inst_passive_queue_type               priority_queues
% 3.50/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/1.02  --inst_passive_queues_freq              [25;2]
% 3.50/1.02  --inst_dismatching                      true
% 3.50/1.02  --inst_eager_unprocessed_to_passive     true
% 3.50/1.02  --inst_prop_sim_given                   true
% 3.50/1.02  --inst_prop_sim_new                     false
% 3.50/1.02  --inst_subs_new                         false
% 3.50/1.02  --inst_eq_res_simp                      false
% 3.50/1.02  --inst_subs_given                       false
% 3.50/1.02  --inst_orphan_elimination               true
% 3.50/1.02  --inst_learning_loop_flag               true
% 3.50/1.02  --inst_learning_start                   3000
% 3.50/1.02  --inst_learning_factor                  2
% 3.50/1.02  --inst_start_prop_sim_after_learn       3
% 3.50/1.02  --inst_sel_renew                        solver
% 3.50/1.02  --inst_lit_activity_flag                true
% 3.50/1.02  --inst_restr_to_given                   false
% 3.50/1.02  --inst_activity_threshold               500
% 3.50/1.02  --inst_out_proof                        true
% 3.50/1.02  
% 3.50/1.02  ------ Resolution Options
% 3.50/1.02  
% 3.50/1.02  --resolution_flag                       false
% 3.50/1.02  --res_lit_sel                           adaptive
% 3.50/1.02  --res_lit_sel_side                      none
% 3.50/1.02  --res_ordering                          kbo
% 3.50/1.02  --res_to_prop_solver                    active
% 3.50/1.02  --res_prop_simpl_new                    false
% 3.50/1.02  --res_prop_simpl_given                  true
% 3.50/1.02  --res_passive_queue_type                priority_queues
% 3.50/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/1.02  --res_passive_queues_freq               [15;5]
% 3.50/1.02  --res_forward_subs                      full
% 3.50/1.02  --res_backward_subs                     full
% 3.50/1.02  --res_forward_subs_resolution           true
% 3.50/1.02  --res_backward_subs_resolution          true
% 3.50/1.02  --res_orphan_elimination                true
% 3.50/1.02  --res_time_limit                        2.
% 3.50/1.02  --res_out_proof                         true
% 3.50/1.02  
% 3.50/1.02  ------ Superposition Options
% 3.50/1.02  
% 3.50/1.02  --superposition_flag                    true
% 3.50/1.02  --sup_passive_queue_type                priority_queues
% 3.50/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.50/1.02  --demod_completeness_check              fast
% 3.50/1.02  --demod_use_ground                      true
% 3.50/1.02  --sup_to_prop_solver                    passive
% 3.50/1.02  --sup_prop_simpl_new                    true
% 3.50/1.02  --sup_prop_simpl_given                  true
% 3.50/1.02  --sup_fun_splitting                     false
% 3.50/1.02  --sup_smt_interval                      50000
% 3.50/1.02  
% 3.50/1.02  ------ Superposition Simplification Setup
% 3.50/1.02  
% 3.50/1.02  --sup_indices_passive                   []
% 3.50/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.02  --sup_full_bw                           [BwDemod]
% 3.50/1.02  --sup_immed_triv                        [TrivRules]
% 3.50/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.02  --sup_immed_bw_main                     []
% 3.50/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/1.02  
% 3.50/1.02  ------ Combination Options
% 3.50/1.02  
% 3.50/1.02  --comb_res_mult                         3
% 3.50/1.02  --comb_sup_mult                         2
% 3.50/1.02  --comb_inst_mult                        10
% 3.50/1.02  
% 3.50/1.02  ------ Debug Options
% 3.50/1.02  
% 3.50/1.02  --dbg_backtrace                         false
% 3.50/1.02  --dbg_dump_prop_clauses                 false
% 3.50/1.02  --dbg_dump_prop_clauses_file            -
% 3.50/1.02  --dbg_out_stat                          false
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  ------ Proving...
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  % SZS status Theorem for theBenchmark.p
% 3.50/1.02  
% 3.50/1.02   Resolution empty clause
% 3.50/1.02  
% 3.50/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/1.02  
% 3.50/1.02  fof(f16,conjecture,(
% 3.50/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f17,negated_conjecture,(
% 3.50/1.02    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 3.50/1.02    inference(negated_conjecture,[],[f16])).
% 3.50/1.02  
% 3.50/1.02  fof(f38,plain,(
% 3.50/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 3.50/1.02    inference(ennf_transformation,[],[f17])).
% 3.50/1.02  
% 3.50/1.02  fof(f39,plain,(
% 3.50/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 3.50/1.02    inference(flattening,[],[f38])).
% 3.50/1.02  
% 3.50/1.02  fof(f45,plain,(
% 3.50/1.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),sK5) != k7_partfun1(X0,X4,k1_funct_1(X3,sK5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(sK5,X1))) )),
% 3.50/1.02    introduced(choice_axiom,[])).
% 3.50/1.02  
% 3.50/1.02  fof(f44,plain,(
% 3.50/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,sK4),X5) != k7_partfun1(X0,sK4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,sK4)) & m1_subset_1(X5,X1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(sK4))) )),
% 3.50/1.02    introduced(choice_axiom,[])).
% 3.50/1.02  
% 3.50/1.02  fof(f43,plain,(
% 3.50/1.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,sK3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,sK3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK3,X1,X2) & v1_funct_1(sK3))) )),
% 3.50/1.02    introduced(choice_axiom,[])).
% 3.50/1.02  
% 3.50/1.02  fof(f42,plain,(
% 3.50/1.02    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 3.50/1.02    introduced(choice_axiom,[])).
% 3.50/1.02  
% 3.50/1.02  fof(f46,plain,(
% 3.50/1.02    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 3.50/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f45,f44,f43,f42])).
% 3.50/1.02  
% 3.50/1.02  fof(f74,plain,(
% 3.50/1.02    m1_subset_1(sK5,sK1)),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f3,axiom,(
% 3.50/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f20,plain,(
% 3.50/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.50/1.02    inference(ennf_transformation,[],[f3])).
% 3.50/1.02  
% 3.50/1.02  fof(f21,plain,(
% 3.50/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.50/1.02    inference(flattening,[],[f20])).
% 3.50/1.02  
% 3.50/1.02  fof(f49,plain,(
% 3.50/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f21])).
% 3.50/1.02  
% 3.50/1.02  fof(f76,plain,(
% 3.50/1.02    k1_xboole_0 != sK1),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f1,axiom,(
% 3.50/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f19,plain,(
% 3.50/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.50/1.02    inference(ennf_transformation,[],[f1])).
% 3.50/1.02  
% 3.50/1.02  fof(f47,plain,(
% 3.50/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f19])).
% 3.50/1.02  
% 3.50/1.02  fof(f73,plain,(
% 3.50/1.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f9,axiom,(
% 3.50/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f18,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.50/1.02    inference(pure_predicate_removal,[],[f9])).
% 3.50/1.02  
% 3.50/1.02  fof(f27,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.02    inference(ennf_transformation,[],[f18])).
% 3.50/1.02  
% 3.50/1.02  fof(f56,plain,(
% 3.50/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.02    inference(cnf_transformation,[],[f27])).
% 3.50/1.02  
% 3.50/1.02  fof(f71,plain,(
% 3.50/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f12,axiom,(
% 3.50/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f30,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.02    inference(ennf_transformation,[],[f12])).
% 3.50/1.02  
% 3.50/1.02  fof(f31,plain,(
% 3.50/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.02    inference(flattening,[],[f30])).
% 3.50/1.02  
% 3.50/1.02  fof(f41,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.02    inference(nnf_transformation,[],[f31])).
% 3.50/1.02  
% 3.50/1.02  fof(f59,plain,(
% 3.50/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.02    inference(cnf_transformation,[],[f41])).
% 3.50/1.02  
% 3.50/1.02  fof(f10,axiom,(
% 3.50/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f28,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.02    inference(ennf_transformation,[],[f10])).
% 3.50/1.02  
% 3.50/1.02  fof(f57,plain,(
% 3.50/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.02    inference(cnf_transformation,[],[f28])).
% 3.50/1.02  
% 3.50/1.02  fof(f70,plain,(
% 3.50/1.02    v1_funct_2(sK3,sK1,sK2)),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f11,axiom,(
% 3.50/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f29,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/1.02    inference(ennf_transformation,[],[f11])).
% 3.50/1.02  
% 3.50/1.02  fof(f58,plain,(
% 3.50/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/1.02    inference(cnf_transformation,[],[f29])).
% 3.50/1.02  
% 3.50/1.02  fof(f75,plain,(
% 3.50/1.02    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f5,axiom,(
% 3.50/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f23,plain,(
% 3.50/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.50/1.02    inference(ennf_transformation,[],[f5])).
% 3.50/1.02  
% 3.50/1.02  fof(f40,plain,(
% 3.50/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.50/1.02    inference(nnf_transformation,[],[f23])).
% 3.50/1.02  
% 3.50/1.02  fof(f52,plain,(
% 3.50/1.02    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f40])).
% 3.50/1.02  
% 3.50/1.02  fof(f4,axiom,(
% 3.50/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f22,plain,(
% 3.50/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.50/1.02    inference(ennf_transformation,[],[f4])).
% 3.50/1.02  
% 3.50/1.02  fof(f50,plain,(
% 3.50/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f22])).
% 3.50/1.02  
% 3.50/1.02  fof(f6,axiom,(
% 3.50/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f53,plain,(
% 3.50/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.50/1.02    inference(cnf_transformation,[],[f6])).
% 3.50/1.02  
% 3.50/1.02  fof(f7,axiom,(
% 3.50/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f24,plain,(
% 3.50/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.50/1.02    inference(ennf_transformation,[],[f7])).
% 3.50/1.02  
% 3.50/1.02  fof(f25,plain,(
% 3.50/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.50/1.02    inference(flattening,[],[f24])).
% 3.50/1.02  
% 3.50/1.02  fof(f54,plain,(
% 3.50/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f25])).
% 3.50/1.02  
% 3.50/1.02  fof(f13,axiom,(
% 3.50/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f32,plain,(
% 3.50/1.02    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.50/1.02    inference(ennf_transformation,[],[f13])).
% 3.50/1.02  
% 3.50/1.02  fof(f33,plain,(
% 3.50/1.02    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.50/1.02    inference(flattening,[],[f32])).
% 3.50/1.02  
% 3.50/1.02  fof(f65,plain,(
% 3.50/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f33])).
% 3.50/1.02  
% 3.50/1.02  fof(f69,plain,(
% 3.50/1.02    v1_funct_1(sK3)),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f72,plain,(
% 3.50/1.02    v1_funct_1(sK4)),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f15,axiom,(
% 3.50/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1))))))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f36,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 3.50/1.02    inference(ennf_transformation,[],[f15])).
% 3.50/1.02  
% 3.50/1.02  fof(f37,plain,(
% 3.50/1.02    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 3.50/1.02    inference(flattening,[],[f36])).
% 3.50/1.02  
% 3.50/1.02  fof(f67,plain,(
% 3.50/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(X4,k1_funct_1(X3,X5)) = k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f37])).
% 3.50/1.02  
% 3.50/1.02  fof(f68,plain,(
% 3.50/1.02    ~v1_xboole_0(sK2)),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f77,plain,(
% 3.50/1.02    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 3.50/1.02    inference(cnf_transformation,[],[f46])).
% 3.50/1.02  
% 3.50/1.02  fof(f2,axiom,(
% 3.50/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f48,plain,(
% 3.50/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f2])).
% 3.50/1.02  
% 3.50/1.02  fof(f14,axiom,(
% 3.50/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f34,plain,(
% 3.50/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 3.50/1.02    inference(ennf_transformation,[],[f14])).
% 3.50/1.02  
% 3.50/1.02  fof(f35,plain,(
% 3.50/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 3.50/1.02    inference(flattening,[],[f34])).
% 3.50/1.02  
% 3.50/1.02  fof(f66,plain,(
% 3.50/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f35])).
% 3.50/1.02  
% 3.50/1.02  fof(f8,axiom,(
% 3.50/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.50/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.50/1.02  
% 3.50/1.02  fof(f26,plain,(
% 3.50/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.50/1.02    inference(ennf_transformation,[],[f8])).
% 3.50/1.02  
% 3.50/1.02  fof(f55,plain,(
% 3.50/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.50/1.02    inference(cnf_transformation,[],[f26])).
% 3.50/1.02  
% 3.50/1.02  cnf(c_24,negated_conjecture,
% 3.50/1.02      ( m1_subset_1(sK5,sK1) ),
% 3.50/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1673,plain,
% 3.50/1.02      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2,plain,
% 3.50/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.50/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1693,plain,
% 3.50/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.50/1.02      | r2_hidden(X0,X1) = iProver_top
% 3.50/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2547,plain,
% 3.50/1.02      ( r2_hidden(sK5,sK1) = iProver_top | v1_xboole_0(sK1) = iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1673,c_1693]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_37,plain,
% 3.50/1.02      ( m1_subset_1(sK5,sK1) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_22,negated_conjecture,
% 3.50/1.02      ( k1_xboole_0 != sK1 ),
% 3.50/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_0,plain,
% 3.50/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.50/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1925,plain,
% 3.50/1.02      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1926,plain,
% 3.50/1.02      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_1925]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1955,plain,
% 3.50/1.02      ( ~ m1_subset_1(sK5,sK1) | r2_hidden(sK5,sK1) | v1_xboole_0(sK1) ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1956,plain,
% 3.50/1.02      ( m1_subset_1(sK5,sK1) != iProver_top
% 3.50/1.02      | r2_hidden(sK5,sK1) = iProver_top
% 3.50/1.02      | v1_xboole_0(sK1) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3009,plain,
% 3.50/1.02      ( r2_hidden(sK5,sK1) = iProver_top ),
% 3.50/1.02      inference(global_propositional_subsumption,
% 3.50/1.02                [status(thm)],
% 3.50/1.02                [c_2547,c_37,c_22,c_1926,c_1956]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_25,negated_conjecture,
% 3.50/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
% 3.50/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1672,plain,
% 3.50/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_9,plain,
% 3.50/1.02      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.50/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1686,plain,
% 3.50/1.02      ( v5_relat_1(X0,X1) = iProver_top
% 3.50/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2300,plain,
% 3.50/1.02      ( v5_relat_1(sK4,sK0) = iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1672,c_1686]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_27,negated_conjecture,
% 3.50/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.50/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1670,plain,
% 3.50/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_17,plain,
% 3.50/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.50/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.50/1.02      | k1_xboole_0 = X2 ),
% 3.50/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1678,plain,
% 3.50/1.02      ( k1_relset_1(X0,X1,X2) = X0
% 3.50/1.02      | k1_xboole_0 = X1
% 3.50/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.50/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3892,plain,
% 3.50/1.02      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 3.50/1.02      | sK2 = k1_xboole_0
% 3.50/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1670,c_1678]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_10,plain,
% 3.50/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.50/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1685,plain,
% 3.50/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.50/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2538,plain,
% 3.50/1.02      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1670,c_1685]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3896,plain,
% 3.50/1.02      ( k1_relat_1(sK3) = sK1
% 3.50/1.02      | sK2 = k1_xboole_0
% 3.50/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top ),
% 3.50/1.02      inference(demodulation,[status(thm)],[c_3892,c_2538]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_28,negated_conjecture,
% 3.50/1.02      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.50/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_33,plain,
% 3.50/1.02      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4104,plain,
% 3.50/1.02      ( sK2 = k1_xboole_0 | k1_relat_1(sK3) = sK1 ),
% 3.50/1.02      inference(global_propositional_subsumption,[status(thm)],[c_3896,c_33]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4105,plain,
% 3.50/1.02      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.50/1.02      inference(renaming,[status(thm)],[c_4104]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2537,plain,
% 3.50/1.02      ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1672,c_1685]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_11,plain,
% 3.50/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.50/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1684,plain,
% 3.50/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.50/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2378,plain,
% 3.50/1.02      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1670,c_1684]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_23,negated_conjecture,
% 3.50/1.02      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
% 3.50/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1674,plain,
% 3.50/1.02      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2427,plain,
% 3.50/1.02      ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) = iProver_top ),
% 3.50/1.02      inference(demodulation,[status(thm)],[c_2378,c_1674]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2757,plain,
% 3.50/1.02      ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) = iProver_top ),
% 3.50/1.02      inference(demodulation,[status(thm)],[c_2537,c_2427]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4,plain,
% 3.50/1.02      ( v5_relat_1(X0,X1) | ~ r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.50/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1691,plain,
% 3.50/1.02      ( v5_relat_1(X0,X1) = iProver_top
% 3.50/1.02      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.50/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3565,plain,
% 3.50/1.02      ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top
% 3.50/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_2757,c_1691]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_34,plain,
% 3.50/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3,plain,
% 3.50/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.50/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1931,plain,
% 3.50/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.02      | v1_relat_1(X0)
% 3.50/1.02      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2313,plain,
% 3.50/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.50/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 3.50/1.02      | v1_relat_1(sK3) ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1931]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2314,plain,
% 3.50/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.50/1.02      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.50/1.02      | v1_relat_1(sK3) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_2313]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_6,plain,
% 3.50/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.50/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2432,plain,
% 3.50/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2433,plain,
% 3.50/1.02      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_2432]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4560,plain,
% 3.50/1.02      ( v5_relat_1(sK3,k1_relat_1(sK4)) = iProver_top ),
% 3.50/1.02      inference(global_propositional_subsumption,
% 3.50/1.02                [status(thm)],
% 3.50/1.02                [c_3565,c_34,c_2314,c_2433]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7,plain,
% 3.50/1.02      ( ~ v5_relat_1(X0,X1)
% 3.50/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.50/1.02      | r2_hidden(k1_funct_1(X0,X2),X1)
% 3.50/1.02      | ~ v1_funct_1(X0)
% 3.50/1.02      | ~ v1_relat_1(X0) ),
% 3.50/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1688,plain,
% 3.50/1.02      ( v5_relat_1(X0,X1) != iProver_top
% 3.50/1.02      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.50/1.02      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 3.50/1.02      | v1_funct_1(X0) != iProver_top
% 3.50/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_18,plain,
% 3.50/1.02      ( ~ v5_relat_1(X0,X1)
% 3.50/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.50/1.02      | ~ v1_funct_1(X0)
% 3.50/1.02      | ~ v1_relat_1(X0)
% 3.50/1.02      | k7_partfun1(X1,X0,X2) = k1_funct_1(X0,X2) ),
% 3.50/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1677,plain,
% 3.50/1.02      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
% 3.50/1.02      | v5_relat_1(X1,X0) != iProver_top
% 3.50/1.02      | r2_hidden(X2,k1_relat_1(X1)) != iProver_top
% 3.50/1.02      | v1_funct_1(X1) != iProver_top
% 3.50/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4054,plain,
% 3.50/1.02      ( k7_partfun1(X0,X1,k1_funct_1(X2,X3)) = k1_funct_1(X1,k1_funct_1(X2,X3))
% 3.50/1.02      | v5_relat_1(X1,X0) != iProver_top
% 3.50/1.02      | v5_relat_1(X2,k1_relat_1(X1)) != iProver_top
% 3.50/1.02      | r2_hidden(X3,k1_relat_1(X2)) != iProver_top
% 3.50/1.02      | v1_funct_1(X2) != iProver_top
% 3.50/1.02      | v1_funct_1(X1) != iProver_top
% 3.50/1.02      | v1_relat_1(X2) != iProver_top
% 3.50/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1688,c_1677]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_6532,plain,
% 3.50/1.02      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 3.50/1.02      | v5_relat_1(sK4,X0) != iProver_top
% 3.50/1.02      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top
% 3.50/1.02      | v1_funct_1(sK4) != iProver_top
% 3.50/1.02      | v1_funct_1(sK3) != iProver_top
% 3.50/1.02      | v1_relat_1(sK4) != iProver_top
% 3.50/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_4560,c_4054]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_29,negated_conjecture,
% 3.50/1.02      ( v1_funct_1(sK3) ),
% 3.50/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_32,plain,
% 3.50/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_26,negated_conjecture,
% 3.50/1.02      ( v1_funct_1(sK4) ),
% 3.50/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_35,plain,
% 3.50/1.02      ( v1_funct_1(sK4) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_36,plain,
% 3.50/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2310,plain,
% 3.50/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
% 3.50/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
% 3.50/1.02      | v1_relat_1(sK4) ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1931]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2311,plain,
% 3.50/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 3.50/1.02      | v1_relat_1(k2_zfmisc_1(sK2,sK0)) != iProver_top
% 3.50/1.02      | v1_relat_1(sK4) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_2310]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2429,plain,
% 3.50/1.02      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2430,plain,
% 3.50/1.02      ( v1_relat_1(k2_zfmisc_1(sK2,sK0)) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_2429]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7091,plain,
% 3.50/1.02      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 3.50/1.02      | v5_relat_1(sK4,X0) != iProver_top
% 3.50/1.02      | r2_hidden(X1,k1_relat_1(sK3)) != iProver_top ),
% 3.50/1.02      inference(global_propositional_subsumption,
% 3.50/1.02                [status(thm)],
% 3.50/1.02                [c_6532,c_32,c_34,c_35,c_36,c_2311,c_2314,c_2430,c_2433]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7102,plain,
% 3.50/1.02      ( k7_partfun1(X0,sK4,k1_funct_1(sK3,X1)) = k1_funct_1(sK4,k1_funct_1(sK3,X1))
% 3.50/1.02      | sK2 = k1_xboole_0
% 3.50/1.02      | v5_relat_1(sK4,X0) != iProver_top
% 3.50/1.02      | r2_hidden(X1,sK1) != iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_4105,c_7091]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7151,plain,
% 3.50/1.02      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,X0)) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.50/1.02      | sK2 = k1_xboole_0
% 3.50/1.02      | r2_hidden(X0,sK1) != iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_2300,c_7102]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7658,plain,
% 3.50/1.02      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
% 3.50/1.02      | sK2 = k1_xboole_0 ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_3009,c_7151]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_20,plain,
% 3.50/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.50/1.02      | ~ m1_subset_1(X3,X1)
% 3.50/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
% 3.50/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.02      | ~ r1_tarski(k2_relset_1(X1,X2,X0),k1_relset_1(X2,X5,X4))
% 3.50/1.02      | ~ v1_funct_1(X4)
% 3.50/1.02      | ~ v1_funct_1(X0)
% 3.50/1.02      | v1_xboole_0(X2)
% 3.50/1.02      | k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(X4,k1_funct_1(X0,X3))
% 3.50/1.02      | k1_xboole_0 = X1 ),
% 3.50/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1675,plain,
% 3.50/1.02      ( k1_funct_1(k8_funct_2(X0,X1,X2,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
% 3.50/1.02      | k1_xboole_0 = X0
% 3.50/1.02      | v1_funct_2(X3,X0,X1) != iProver_top
% 3.50/1.02      | m1_subset_1(X5,X0) != iProver_top
% 3.50/1.02      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/1.02      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.50/1.02      | r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) != iProver_top
% 3.50/1.02      | v1_funct_1(X4) != iProver_top
% 3.50/1.02      | v1_funct_1(X3) != iProver_top
% 3.50/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2460,plain,
% 3.50/1.02      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 3.50/1.02      | sK1 = k1_xboole_0
% 3.50/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.50/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 3.50/1.02      | m1_subset_1(X2,sK1) != iProver_top
% 3.50/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.50/1.02      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
% 3.50/1.02      | v1_funct_1(X1) != iProver_top
% 3.50/1.02      | v1_funct_1(sK3) != iProver_top
% 3.50/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_2378,c_1675]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_30,negated_conjecture,
% 3.50/1.02      ( ~ v1_xboole_0(sK2) ),
% 3.50/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_31,plain,
% 3.50/1.02      ( v1_xboole_0(sK2) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1128,plain,( X0 = X0 ),theory(equality) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1159,plain,
% 3.50/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1128]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1129,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1982,plain,
% 3.50/1.02      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1129]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1983,plain,
% 3.50/1.02      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1982]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3656,plain,
% 3.50/1.02      ( m1_subset_1(X2,sK1) != iProver_top
% 3.50/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 3.50/1.02      | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 3.50/1.02      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
% 3.50/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.50/1.02      inference(global_propositional_subsumption,
% 3.50/1.02                [status(thm)],
% 3.50/1.02                [c_2460,c_31,c_32,c_33,c_34,c_22,c_1159,c_1983]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3657,plain,
% 3.50/1.02      ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
% 3.50/1.02      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) != iProver_top
% 3.50/1.02      | m1_subset_1(X2,sK1) != iProver_top
% 3.50/1.02      | r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) != iProver_top
% 3.50/1.02      | v1_funct_1(X1) != iProver_top ),
% 3.50/1.02      inference(renaming,[status(thm)],[c_3656]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3668,plain,
% 3.50/1.02      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.50/1.02      | m1_subset_1(X0,sK1) != iProver_top
% 3.50/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) != iProver_top
% 3.50/1.02      | r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) != iProver_top
% 3.50/1.02      | v1_funct_1(sK4) != iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_2537,c_3657]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3698,plain,
% 3.50/1.02      ( m1_subset_1(X0,sK1) != iProver_top
% 3.50/1.02      | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ),
% 3.50/1.02      inference(global_propositional_subsumption,
% 3.50/1.02                [status(thm)],
% 3.50/1.02                [c_3668,c_35,c_36,c_2757]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3699,plain,
% 3.50/1.02      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
% 3.50/1.02      | m1_subset_1(X0,sK1) != iProver_top ),
% 3.50/1.02      inference(renaming,[status(thm)],[c_3698]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3707,plain,
% 3.50/1.02      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1673,c_3699]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_21,negated_conjecture,
% 3.50/1.02      ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
% 3.50/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3814,plain,
% 3.50/1.02      ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
% 3.50/1.02      inference(demodulation,[status(thm)],[c_3707,c_21]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7726,plain,
% 3.50/1.02      ( sK2 = k1_xboole_0 ),
% 3.50/1.02      inference(global_propositional_subsumption,[status(thm)],[c_7658,c_3814]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7774,plain,
% 3.50/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.50/1.02      inference(demodulation,[status(thm)],[c_7726,c_1670]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1,plain,
% 3.50/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 3.50/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1694,plain,
% 3.50/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_19,plain,
% 3.50/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.50/1.02      | ~ m1_subset_1(X3,X1)
% 3.50/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/1.02      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2)
% 3.50/1.02      | ~ v1_funct_1(X0)
% 3.50/1.02      | v1_xboole_0(X1) ),
% 3.50/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1676,plain,
% 3.50/1.02      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.50/1.02      | m1_subset_1(X3,X1) != iProver_top
% 3.50/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/1.02      | m1_subset_1(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 3.50/1.02      | v1_funct_1(X0) != iProver_top
% 3.50/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3306,plain,
% 3.50/1.02      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.50/1.02      | m1_subset_1(X3,X1) != iProver_top
% 3.50/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/1.02      | r2_hidden(k3_funct_2(X1,X2,X0,X3),X2) = iProver_top
% 3.50/1.02      | v1_funct_1(X0) != iProver_top
% 3.50/1.02      | v1_xboole_0(X2) = iProver_top
% 3.50/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1676,c_1693]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_8,plain,
% 3.50/1.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.50/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1687,plain,
% 3.50/1.02      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4612,plain,
% 3.50/1.02      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.50/1.02      | m1_subset_1(X3,X1) != iProver_top
% 3.50/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/1.02      | r1_tarski(X2,k3_funct_2(X1,X2,X0,X3)) != iProver_top
% 3.50/1.02      | v1_funct_1(X0) != iProver_top
% 3.50/1.02      | v1_xboole_0(X2) = iProver_top
% 3.50/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_3306,c_1687]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_5437,plain,
% 3.50/1.02      ( v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.50/1.02      | m1_subset_1(X2,X1) != iProver_top
% 3.50/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
% 3.50/1.02      | v1_funct_1(X0) != iProver_top
% 3.50/1.02      | v1_xboole_0(X1) = iProver_top
% 3.50/1.02      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1694,c_4612]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_8067,plain,
% 3.50/1.02      ( v1_funct_2(sK3,sK1,k1_xboole_0) != iProver_top
% 3.50/1.02      | m1_subset_1(X0,sK1) != iProver_top
% 3.50/1.02      | v1_funct_1(sK3) != iProver_top
% 3.50/1.02      | v1_xboole_0(sK1) = iProver_top
% 3.50/1.02      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_7774,c_5437]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2198,plain,
% 3.50/1.02      ( sK3 = sK3 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1128]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2659,plain,
% 3.50/1.02      ( sK1 = sK1 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1128]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3037,plain,
% 3.50/1.02      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1129]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3038,plain,
% 3.50/1.02      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 != k1_xboole_0 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_3037]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1141,plain,
% 3.50/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.50/1.02      | v1_funct_2(X3,X4,X5)
% 3.50/1.02      | X3 != X0
% 3.50/1.02      | X4 != X1
% 3.50/1.02      | X5 != X2 ),
% 3.50/1.02      theory(equality) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2050,plain,
% 3.50/1.02      ( v1_funct_2(X0,X1,X2)
% 3.50/1.02      | ~ v1_funct_2(sK3,sK1,sK2)
% 3.50/1.02      | X0 != sK3
% 3.50/1.02      | X2 != sK2
% 3.50/1.02      | X1 != sK1 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_1141]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_2528,plain,
% 3.50/1.02      ( v1_funct_2(sK3,X0,X1)
% 3.50/1.02      | ~ v1_funct_2(sK3,sK1,sK2)
% 3.50/1.02      | X1 != sK2
% 3.50/1.02      | X0 != sK1
% 3.50/1.02      | sK3 != sK3 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_2050]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_3021,plain,
% 3.50/1.02      ( v1_funct_2(sK3,X0,k1_xboole_0)
% 3.50/1.02      | ~ v1_funct_2(sK3,sK1,sK2)
% 3.50/1.02      | X0 != sK1
% 3.50/1.02      | sK3 != sK3
% 3.50/1.02      | k1_xboole_0 != sK2 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_2528]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4742,plain,
% 3.50/1.02      ( ~ v1_funct_2(sK3,sK1,sK2)
% 3.50/1.02      | v1_funct_2(sK3,sK1,k1_xboole_0)
% 3.50/1.02      | sK3 != sK3
% 3.50/1.02      | sK1 != sK1
% 3.50/1.02      | k1_xboole_0 != sK2 ),
% 3.50/1.02      inference(instantiation,[status(thm)],[c_3021]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_4743,plain,
% 3.50/1.02      ( sK3 != sK3
% 3.50/1.02      | sK1 != sK1
% 3.50/1.02      | k1_xboole_0 != sK2
% 3.50/1.02      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.50/1.02      | v1_funct_2(sK3,sK1,k1_xboole_0) = iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_4742]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_1667,plain,
% 3.50/1.02      ( v1_xboole_0(sK2) != iProver_top ),
% 3.50/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_7776,plain,
% 3.50/1.02      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.50/1.02      inference(demodulation,[status(thm)],[c_7726,c_1667]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_9092,plain,
% 3.50/1.02      ( m1_subset_1(X0,sK1) != iProver_top ),
% 3.50/1.02      inference(global_propositional_subsumption,
% 3.50/1.02                [status(thm)],
% 3.50/1.02                [c_8067,c_32,c_33,c_22,c_1159,c_1926,c_2198,c_2659,c_3038,
% 3.50/1.02                 c_3814,c_4743,c_7658,c_7776]) ).
% 3.50/1.02  
% 3.50/1.02  cnf(c_9100,plain,
% 3.50/1.02      ( $false ),
% 3.50/1.02      inference(superposition,[status(thm)],[c_1673,c_9092]) ).
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/1.02  
% 3.50/1.02  ------                               Statistics
% 3.50/1.02  
% 3.50/1.02  ------ General
% 3.50/1.02  
% 3.50/1.02  abstr_ref_over_cycles:                  0
% 3.50/1.02  abstr_ref_under_cycles:                 0
% 3.50/1.02  gc_basic_clause_elim:                   0
% 3.50/1.02  forced_gc_time:                         0
% 3.50/1.02  parsing_time:                           0.009
% 3.50/1.02  unif_index_cands_time:                  0.
% 3.50/1.02  unif_index_add_time:                    0.
% 3.50/1.02  orderings_time:                         0.
% 3.50/1.02  out_proof_time:                         0.012
% 3.50/1.02  total_time:                             0.272
% 3.50/1.02  num_of_symbols:                         56
% 3.50/1.02  num_of_terms:                           10043
% 3.50/1.02  
% 3.50/1.02  ------ Preprocessing
% 3.50/1.02  
% 3.50/1.02  num_of_splits:                          0
% 3.50/1.02  num_of_split_atoms:                     0
% 3.50/1.02  num_of_reused_defs:                     0
% 3.50/1.02  num_eq_ax_congr_red:                    16
% 3.50/1.02  num_of_sem_filtered_clauses:            1
% 3.50/1.02  num_of_subtypes:                        0
% 3.50/1.02  monotx_restored_types:                  0
% 3.50/1.02  sat_num_of_epr_types:                   0
% 3.50/1.02  sat_num_of_non_cyclic_types:            0
% 3.50/1.02  sat_guarded_non_collapsed_types:        0
% 3.50/1.02  num_pure_diseq_elim:                    0
% 3.50/1.02  simp_replaced_by:                       0
% 3.50/1.02  res_preprocessed:                       126
% 3.50/1.02  prep_upred:                             0
% 3.50/1.02  prep_unflattend:                        61
% 3.50/1.02  smt_new_axioms:                         0
% 3.50/1.02  pred_elim_cands:                        8
% 3.50/1.02  pred_elim:                              0
% 3.50/1.02  pred_elim_cl:                           0
% 3.50/1.02  pred_elim_cycles:                       4
% 3.50/1.02  merged_defs:                            0
% 3.50/1.02  merged_defs_ncl:                        0
% 3.50/1.02  bin_hyper_res:                          0
% 3.50/1.02  prep_cycles:                            3
% 3.50/1.02  pred_elim_time:                         0.012
% 3.50/1.02  splitting_time:                         0.
% 3.50/1.02  sem_filter_time:                        0.
% 3.50/1.02  monotx_time:                            0.
% 3.50/1.02  subtype_inf_time:                       0.
% 3.50/1.02  
% 3.50/1.02  ------ Problem properties
% 3.50/1.02  
% 3.50/1.02  clauses:                                31
% 3.50/1.02  conjectures:                            10
% 3.50/1.02  epr:                                    10
% 3.50/1.02  horn:                                   24
% 3.50/1.02  ground:                                 10
% 3.50/1.02  unary:                                  12
% 3.50/1.02  binary:                                 5
% 3.50/1.02  lits:                                   81
% 3.50/1.02  lits_eq:                                17
% 3.50/1.02  fd_pure:                                0
% 3.50/1.02  fd_pseudo:                              0
% 3.50/1.02  fd_cond:                                5
% 3.50/1.02  fd_pseudo_cond:                         0
% 3.50/1.02  ac_symbols:                             0
% 3.50/1.02  
% 3.50/1.02  ------ Propositional Solver
% 3.50/1.02  
% 3.50/1.02  prop_solver_calls:                      26
% 3.50/1.02  prop_fast_solver_calls:                 1487
% 3.50/1.02  smt_solver_calls:                       0
% 3.50/1.02  smt_fast_solver_calls:                  0
% 3.50/1.02  prop_num_of_clauses:                    2642
% 3.50/1.02  prop_preprocess_simplified:             6281
% 3.50/1.02  prop_fo_subsumed:                       68
% 3.50/1.02  prop_solver_time:                       0.
% 3.50/1.02  smt_solver_time:                        0.
% 3.50/1.02  smt_fast_solver_time:                   0.
% 3.50/1.02  prop_fast_solver_time:                  0.
% 3.50/1.02  prop_unsat_core_time:                   0.
% 3.50/1.02  
% 3.50/1.02  ------ QBF
% 3.50/1.02  
% 3.50/1.02  qbf_q_res:                              0
% 3.50/1.02  qbf_num_tautologies:                    0
% 3.50/1.02  qbf_prep_cycles:                        0
% 3.50/1.02  
% 3.50/1.02  ------ BMC1
% 3.50/1.02  
% 3.50/1.02  bmc1_current_bound:                     -1
% 3.50/1.02  bmc1_last_solved_bound:                 -1
% 3.50/1.02  bmc1_unsat_core_size:                   -1
% 3.50/1.02  bmc1_unsat_core_parents_size:           -1
% 3.50/1.02  bmc1_merge_next_fun:                    0
% 3.50/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.50/1.02  
% 3.50/1.02  ------ Instantiation
% 3.50/1.02  
% 3.50/1.02  inst_num_of_clauses:                    745
% 3.50/1.02  inst_num_in_passive:                    143
% 3.50/1.02  inst_num_in_active:                     584
% 3.50/1.02  inst_num_in_unprocessed:                18
% 3.50/1.02  inst_num_of_loops:                      650
% 3.50/1.02  inst_num_of_learning_restarts:          0
% 3.50/1.02  inst_num_moves_active_passive:          61
% 3.50/1.02  inst_lit_activity:                      0
% 3.50/1.02  inst_lit_activity_moves:                0
% 3.50/1.02  inst_num_tautologies:                   0
% 3.50/1.02  inst_num_prop_implied:                  0
% 3.50/1.02  inst_num_existing_simplified:           0
% 3.50/1.02  inst_num_eq_res_simplified:             0
% 3.50/1.02  inst_num_child_elim:                    0
% 3.50/1.02  inst_num_of_dismatching_blockings:      138
% 3.50/1.02  inst_num_of_non_proper_insts:           751
% 3.50/1.02  inst_num_of_duplicates:                 0
% 3.50/1.02  inst_inst_num_from_inst_to_res:         0
% 3.50/1.02  inst_dismatching_checking_time:         0.
% 3.50/1.02  
% 3.50/1.02  ------ Resolution
% 3.50/1.02  
% 3.50/1.02  res_num_of_clauses:                     0
% 3.50/1.02  res_num_in_passive:                     0
% 3.50/1.02  res_num_in_active:                      0
% 3.50/1.02  res_num_of_loops:                       129
% 3.50/1.02  res_forward_subset_subsumed:            90
% 3.50/1.02  res_backward_subset_subsumed:           0
% 3.50/1.02  res_forward_subsumed:                   0
% 3.50/1.02  res_backward_subsumed:                  0
% 3.50/1.02  res_forward_subsumption_resolution:     2
% 3.50/1.02  res_backward_subsumption_resolution:    0
% 3.50/1.02  res_clause_to_clause_subsumption:       653
% 3.50/1.02  res_orphan_elimination:                 0
% 3.50/1.02  res_tautology_del:                      127
% 3.50/1.02  res_num_eq_res_simplified:              0
% 3.50/1.02  res_num_sel_changes:                    0
% 3.50/1.02  res_moves_from_active_to_pass:          0
% 3.50/1.02  
% 3.50/1.02  ------ Superposition
% 3.50/1.02  
% 3.50/1.02  sup_time_total:                         0.
% 3.50/1.02  sup_time_generating:                    0.
% 3.50/1.02  sup_time_sim_full:                      0.
% 3.50/1.02  sup_time_sim_immed:                     0.
% 3.50/1.02  
% 3.50/1.02  sup_num_of_clauses:                     128
% 3.50/1.02  sup_num_in_active:                      61
% 3.50/1.02  sup_num_in_passive:                     67
% 3.50/1.02  sup_num_of_loops:                       128
% 3.50/1.02  sup_fw_superposition:                   103
% 3.50/1.02  sup_bw_superposition:                   52
% 3.50/1.02  sup_immediate_simplified:               14
% 3.50/1.02  sup_given_eliminated:                   0
% 3.50/1.02  comparisons_done:                       0
% 3.50/1.02  comparisons_avoided:                    80
% 3.50/1.02  
% 3.50/1.02  ------ Simplifications
% 3.50/1.02  
% 3.50/1.02  
% 3.50/1.02  sim_fw_subset_subsumed:                 8
% 3.50/1.02  sim_bw_subset_subsumed:                 3
% 3.50/1.02  sim_fw_subsumed:                        4
% 3.50/1.02  sim_bw_subsumed:                        0
% 3.50/1.02  sim_fw_subsumption_res:                 0
% 3.50/1.02  sim_bw_subsumption_res:                 0
% 3.50/1.02  sim_tautology_del:                      1
% 3.50/1.02  sim_eq_tautology_del:                   27
% 3.50/1.02  sim_eq_res_simp:                        0
% 3.50/1.02  sim_fw_demodulated:                     2
% 3.50/1.02  sim_bw_demodulated:                     65
% 3.50/1.02  sim_light_normalised:                   3
% 3.50/1.02  sim_joinable_taut:                      0
% 3.50/1.02  sim_joinable_simp:                      0
% 3.50/1.02  sim_ac_normalised:                      0
% 3.50/1.02  sim_smt_subsumption:                    0
% 3.50/1.02  
%------------------------------------------------------------------------------
