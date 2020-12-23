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
% DateTime   : Thu Dec  3 12:10:03 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 537 expanded)
%              Number of clauses        :   77 ( 176 expanded)
%              Number of leaves         :   19 ( 107 expanded)
%              Depth                    :   22
%              Number of atoms          :  501 (2397 expanded)
%              Number of equality atoms :  192 ( 643 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK7,X4) != sK4
          | ~ m1_subset_1(X4,sK5) )
      & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ! [X4] :
        ( k1_funct_1(sK7,X4) != sK4
        | ~ m1_subset_1(X4,sK5) )
    & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f35,f48])).

fof(f77,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f49])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) != sK4
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_785,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_788,plain,
    ( k8_relset_1(X0,X1,X2,X1) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1235,plain,
    ( k8_relset_1(sK5,sK6,sK7,sK6) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_788])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1236,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | k8_relset_1(sK5,sK6,sK7,sK6) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1235])).

cnf(c_1755,plain,
    ( k8_relset_1(sK5,sK6,sK7,sK6) = sK5
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1235,c_29,c_28,c_1236])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_790,plain,
    ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2099,plain,
    ( k7_relset_1(sK5,sK6,sK7,k8_relset_1(sK5,sK6,sK7,sK6)) = k2_relset_1(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_785,c_790])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_793,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1519,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_785,c_793])).

cnf(c_2100,plain,
    ( k7_relset_1(sK5,sK6,sK7,k8_relset_1(sK5,sK6,sK7,sK6)) = k2_relat_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_2099,c_1519])).

cnf(c_2418,plain,
    ( k7_relset_1(sK5,sK6,sK7,sK5) = k2_relat_1(sK7)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1755,c_2100])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_792,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2003,plain,
    ( k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_785,c_792])).

cnf(c_2424,plain,
    ( k9_relat_1(sK7,sK5) = k2_relat_1(sK7)
    | sK6 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2418,c_2003])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_809,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_811,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2077,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | m1_subset_1(sK0(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_811])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_786,plain,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1628,plain,
    ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1519,c_786])).

cnf(c_2419,plain,
    ( k9_relat_1(sK7,k8_relset_1(sK5,sK6,sK7,sK6)) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2100,c_2003])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_808,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_798,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3014,plain,
    ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_808,c_798])).

cnf(c_6697,plain,
    ( k1_funct_1(sK7,sK0(X0,k8_relset_1(sK5,sK6,sK7,sK6),sK7)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2419,c_3014])).

cnf(c_30,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_32,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1078,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1079,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_6810,plain,
    ( k1_funct_1(sK7,sK0(X0,k8_relset_1(sK5,sK6,sK7,sK6),sK7)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6697,c_30,c_32,c_1079])).

cnf(c_6825,plain,
    ( k1_funct_1(sK7,sK0(sK4,k8_relset_1(sK5,sK6,sK7,sK6),sK7)) = sK4 ),
    inference(superposition,[status(thm)],[c_1628,c_6810])).

cnf(c_25,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK7,X0) != sK4 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_787,plain,
    ( k1_funct_1(sK7,X0) != sK4
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7085,plain,
    ( m1_subset_1(sK0(sK4,k8_relset_1(sK5,sK6,sK7,sK6),sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6825,c_787])).

cnf(c_7115,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK0(sK4,sK5,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_7085])).

cnf(c_7232,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_7115])).

cnf(c_7439,plain,
    ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7232,c_32,c_1079])).

cnf(c_7440,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7439])).

cnf(c_7445,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_7440])).

cnf(c_8241,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7445,c_1628])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_794,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1317,plain,
    ( v5_relat_1(sK7,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_794])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_802,plain,
    ( k1_funct_1(X0,sK3(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3099,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1628,c_802])).

cnf(c_1634,plain,
    ( r2_hidden(sK4,k2_relat_1(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1628])).

cnf(c_2496,plain,
    ( ~ r2_hidden(sK4,k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3248,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3099,c_29,c_27,c_1078,c_1634,c_2496])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_800,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4052,plain,
    ( v5_relat_1(sK7,X0) != iProver_top
    | r2_hidden(sK3(sK7,sK4),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3248,c_800])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2497,plain,
    ( r2_hidden(sK3(sK7,sK4),k1_relat_1(sK7))
    | ~ r2_hidden(sK4,k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2498,plain,
    ( r2_hidden(sK3(sK7,sK4),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2497])).

cnf(c_4501,plain,
    ( v5_relat_1(sK7,X0) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4052,c_30,c_32,c_1079,c_1628,c_2498])).

cnf(c_4509,plain,
    ( r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1317,c_4501])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_796,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4513,plain,
    ( r1_tarski(sK6,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4509,c_796])).

cnf(c_8247,plain,
    ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8241,c_4513])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1350,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1353,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8247,c_1353])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.49/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/0.99  
% 3.49/0.99  ------  iProver source info
% 3.49/0.99  
% 3.49/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.49/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/0.99  git: non_committed_changes: false
% 3.49/0.99  git: last_make_outside_of_git: false
% 3.49/0.99  
% 3.49/0.99  ------ 
% 3.49/0.99  ------ Parsing...
% 3.49/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/0.99  
% 3.49/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/0.99  ------ Proving...
% 3.49/0.99  ------ Problem Properties 
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  clauses                                 30
% 3.49/0.99  conjectures                             5
% 3.49/0.99  EPR                                     5
% 3.49/0.99  Horn                                    27
% 3.49/0.99  unary                                   5
% 3.49/0.99  binary                                  9
% 3.49/0.99  lits                                    91
% 3.49/0.99  lits eq                                 15
% 3.49/0.99  fd_pure                                 0
% 3.49/0.99  fd_pseudo                               0
% 3.49/0.99  fd_cond                                 0
% 3.49/0.99  fd_pseudo_cond                          4
% 3.49/0.99  AC symbols                              0
% 3.49/0.99  
% 3.49/0.99  ------ Input Options Time Limit: Unbounded
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  ------ 
% 3.49/0.99  Current options:
% 3.49/0.99  ------ 
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  ------ Proving...
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  % SZS status Theorem for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  fof(f15,conjecture,(
% 3.49/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f16,negated_conjecture,(
% 3.49/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.49/0.99    inference(negated_conjecture,[],[f15])).
% 3.49/0.99  
% 3.49/0.99  fof(f34,plain,(
% 3.49/0.99    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.49/0.99    inference(ennf_transformation,[],[f16])).
% 3.49/0.99  
% 3.49/0.99  fof(f35,plain,(
% 3.49/0.99    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.49/0.99    inference(flattening,[],[f34])).
% 3.49/0.99  
% 3.49/0.99  fof(f48,plain,(
% 3.49/0.99    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f49,plain,(
% 3.49/0.99    ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 3.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f35,f48])).
% 3.49/0.99  
% 3.49/0.99  fof(f77,plain,(
% 3.49/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.49/0.99    inference(cnf_transformation,[],[f49])).
% 3.49/0.99  
% 3.49/0.99  fof(f14,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f32,plain,(
% 3.49/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.49/0.99    inference(ennf_transformation,[],[f14])).
% 3.49/0.99  
% 3.49/0.99  fof(f33,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.49/0.99    inference(flattening,[],[f32])).
% 3.49/0.99  
% 3.49/0.99  fof(f73,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f33])).
% 3.49/0.99  
% 3.49/0.99  fof(f75,plain,(
% 3.49/0.99    v1_funct_1(sK7)),
% 3.49/0.99    inference(cnf_transformation,[],[f49])).
% 3.49/0.99  
% 3.49/0.99  fof(f76,plain,(
% 3.49/0.99    v1_funct_2(sK7,sK5,sK6)),
% 3.49/0.99    inference(cnf_transformation,[],[f49])).
% 3.49/0.99  
% 3.49/0.99  fof(f13,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f31,plain,(
% 3.49/0.99    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.49/0.99    inference(ennf_transformation,[],[f13])).
% 3.49/0.99  
% 3.49/0.99  fof(f71,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f31])).
% 3.49/0.99  
% 3.49/0.99  fof(f11,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f29,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f11])).
% 3.49/0.99  
% 3.49/0.99  fof(f69,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f29])).
% 3.49/0.99  
% 3.49/0.99  fof(f12,axiom,(
% 3.49/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f30,plain,(
% 3.49/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f12])).
% 3.49/0.99  
% 3.49/0.99  fof(f70,plain,(
% 3.49/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f30])).
% 3.49/0.99  
% 3.49/0.99  fof(f4,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f19,plain,(
% 3.49/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(ennf_transformation,[],[f4])).
% 3.49/0.99  
% 3.49/0.99  fof(f36,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(nnf_transformation,[],[f19])).
% 3.49/0.99  
% 3.49/0.99  fof(f37,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(rectify,[],[f36])).
% 3.49/0.99  
% 3.49/0.99  fof(f38,plain,(
% 3.49/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f39,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.49/0.99  
% 3.49/0.99  fof(f54,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f39])).
% 3.49/0.99  
% 3.49/0.99  fof(f3,axiom,(
% 3.49/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f18,plain,(
% 3.49/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.49/0.99    inference(ennf_transformation,[],[f3])).
% 3.49/0.99  
% 3.49/0.99  fof(f51,plain,(
% 3.49/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f18])).
% 3.49/0.99  
% 3.49/0.99  fof(f78,plain,(
% 3.49/0.99    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))),
% 3.49/0.99    inference(cnf_transformation,[],[f49])).
% 3.49/0.99  
% 3.49/0.99  fof(f53,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f39])).
% 3.49/0.99  
% 3.49/0.99  fof(f7,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f24,plain,(
% 3.49/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.49/0.99    inference(ennf_transformation,[],[f7])).
% 3.49/0.99  
% 3.49/0.99  fof(f25,plain,(
% 3.49/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(flattening,[],[f24])).
% 3.49/0.99  
% 3.49/0.99  fof(f46,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(nnf_transformation,[],[f25])).
% 3.49/0.99  
% 3.49/0.99  fof(f47,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.49/0.99    inference(flattening,[],[f46])).
% 3.49/0.99  
% 3.49/0.99  fof(f64,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f47])).
% 3.49/0.99  
% 3.49/0.99  fof(f9,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f27,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f9])).
% 3.49/0.99  
% 3.49/0.99  fof(f67,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f27])).
% 3.49/0.99  
% 3.49/0.99  fof(f79,plain,(
% 3.49/0.99    ( ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f49])).
% 3.49/0.99  
% 3.49/0.99  fof(f10,axiom,(
% 3.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f17,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.49/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.49/0.99  
% 3.49/0.99  fof(f28,plain,(
% 3.49/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/0.99    inference(ennf_transformation,[],[f17])).
% 3.49/0.99  
% 3.49/0.99  fof(f68,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/0.99    inference(cnf_transformation,[],[f28])).
% 3.49/0.99  
% 3.49/0.99  fof(f5,axiom,(
% 3.49/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f20,plain,(
% 3.49/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.49/0.99    inference(ennf_transformation,[],[f5])).
% 3.49/0.99  
% 3.49/0.99  fof(f21,plain,(
% 3.49/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/0.99    inference(flattening,[],[f20])).
% 3.49/0.99  
% 3.49/0.99  fof(f40,plain,(
% 3.49/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/0.99    inference(nnf_transformation,[],[f21])).
% 3.49/0.99  
% 3.49/0.99  fof(f41,plain,(
% 3.49/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/0.99    inference(rectify,[],[f40])).
% 3.49/0.99  
% 3.49/0.99  fof(f44,plain,(
% 3.49/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f43,plain,(
% 3.49/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f42,plain,(
% 3.49/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.49/0.99    introduced(choice_axiom,[])).
% 3.49/0.99  
% 3.49/0.99  fof(f45,plain,(
% 3.49/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.49/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 3.49/0.99  
% 3.49/0.99  fof(f57,plain,(
% 3.49/0.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f45])).
% 3.49/0.99  
% 3.49/0.99  fof(f82,plain,(
% 3.49/0.99    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/0.99    inference(equality_resolution,[],[f57])).
% 3.49/0.99  
% 3.49/0.99  fof(f6,axiom,(
% 3.49/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f22,plain,(
% 3.49/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.49/0.99    inference(ennf_transformation,[],[f6])).
% 3.49/0.99  
% 3.49/0.99  fof(f23,plain,(
% 3.49/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.49/0.99    inference(flattening,[],[f22])).
% 3.49/0.99  
% 3.49/0.99  fof(f62,plain,(
% 3.49/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f23])).
% 3.49/0.99  
% 3.49/0.99  fof(f56,plain,(
% 3.49/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f45])).
% 3.49/0.99  
% 3.49/0.99  fof(f83,plain,(
% 3.49/0.99    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.49/0.99    inference(equality_resolution,[],[f56])).
% 3.49/0.99  
% 3.49/0.99  fof(f8,axiom,(
% 3.49/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f26,plain,(
% 3.49/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.49/0.99    inference(ennf_transformation,[],[f8])).
% 3.49/0.99  
% 3.49/0.99  fof(f66,plain,(
% 3.49/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f26])).
% 3.49/0.99  
% 3.49/0.99  fof(f2,axiom,(
% 3.49/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.49/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.99  
% 3.49/0.99  fof(f50,plain,(
% 3.49/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.49/0.99    inference(cnf_transformation,[],[f2])).
% 3.49/0.99  
% 3.49/0.99  cnf(c_27,negated_conjecture,
% 3.49/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.49/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_785,plain,
% 3.49/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_24,plain,
% 3.49/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | ~ v1_funct_1(X0)
% 3.49/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.49/0.99      | k1_xboole_0 = X2 ),
% 3.49/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_788,plain,
% 3.49/0.99      ( k8_relset_1(X0,X1,X2,X1) = X0
% 3.49/0.99      | k1_xboole_0 = X1
% 3.49/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.49/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.49/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1235,plain,
% 3.49/0.99      ( k8_relset_1(sK5,sK6,sK7,sK6) = sK5
% 3.49/0.99      | sK6 = k1_xboole_0
% 3.49/0.99      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 3.49/0.99      | v1_funct_1(sK7) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_785,c_788]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_29,negated_conjecture,
% 3.49/0.99      ( v1_funct_1(sK7) ),
% 3.49/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_28,negated_conjecture,
% 3.49/0.99      ( v1_funct_2(sK7,sK5,sK6) ),
% 3.49/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1236,plain,
% 3.49/0.99      ( ~ v1_funct_2(sK7,sK5,sK6)
% 3.49/0.99      | ~ v1_funct_1(sK7)
% 3.49/0.99      | k8_relset_1(sK5,sK6,sK7,sK6) = sK5
% 3.49/0.99      | sK6 = k1_xboole_0 ),
% 3.49/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1235]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1755,plain,
% 3.49/0.99      ( k8_relset_1(sK5,sK6,sK7,sK6) = sK5 | sK6 = k1_xboole_0 ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_1235,c_29,c_28,c_1236]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_22,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_790,plain,
% 3.49/0.99      ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
% 3.49/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2099,plain,
% 3.49/0.99      ( k7_relset_1(sK5,sK6,sK7,k8_relset_1(sK5,sK6,sK7,sK6)) = k2_relset_1(sK5,sK6,sK7) ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_785,c_790]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_19,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_793,plain,
% 3.49/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.49/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1519,plain,
% 3.49/0.99      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_785,c_793]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2100,plain,
% 3.49/0.99      ( k7_relset_1(sK5,sK6,sK7,k8_relset_1(sK5,sK6,sK7,sK6)) = k2_relat_1(sK7) ),
% 3.49/0.99      inference(light_normalisation,[status(thm)],[c_2099,c_1519]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2418,plain,
% 3.49/0.99      ( k7_relset_1(sK5,sK6,sK7,sK5) = k2_relat_1(sK7)
% 3.49/0.99      | sK6 = k1_xboole_0 ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1755,c_2100]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_20,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.49/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_792,plain,
% 3.49/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.49/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2003,plain,
% 3.49/0.99      ( k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_785,c_792]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2424,plain,
% 3.49/0.99      ( k9_relat_1(sK7,sK5) = k2_relat_1(sK7) | sK6 = k1_xboole_0 ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_2418,c_2003]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3,plain,
% 3.49/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.49/0.99      | r2_hidden(sK0(X0,X2,X1),X2)
% 3.49/0.99      | ~ v1_relat_1(X1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_809,plain,
% 3.49/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.49/0.99      | r2_hidden(sK0(X0,X2,X1),X2) = iProver_top
% 3.49/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1,plain,
% 3.49/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_811,plain,
% 3.49/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.49/0.99      | m1_subset_1(X0,X1) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2077,plain,
% 3.49/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.49/0.99      | m1_subset_1(sK0(X0,X2,X1),X2) = iProver_top
% 3.49/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_809,c_811]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_26,negated_conjecture,
% 3.49/0.99      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
% 3.49/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_786,plain,
% 3.49/0.99      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1628,plain,
% 3.49/0.99      ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_1519,c_786]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2419,plain,
% 3.49/0.99      ( k9_relat_1(sK7,k8_relset_1(sK5,sK6,sK7,sK6)) = k2_relat_1(sK7) ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_2100,c_2003]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4,plain,
% 3.49/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.49/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.49/0.99      | ~ v1_relat_1(X1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_808,plain,
% 3.49/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.49/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.49/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_14,plain,
% 3.49/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.49/0.99      | ~ v1_funct_1(X2)
% 3.49/0.99      | ~ v1_relat_1(X2)
% 3.49/0.99      | k1_funct_1(X2,X0) = X1 ),
% 3.49/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_798,plain,
% 3.49/0.99      ( k1_funct_1(X0,X1) = X2
% 3.49/0.99      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 3.49/0.99      | v1_funct_1(X0) != iProver_top
% 3.49/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3014,plain,
% 3.49/0.99      ( k1_funct_1(X0,sK0(X1,X2,X0)) = X1
% 3.49/0.99      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 3.49/0.99      | v1_funct_1(X0) != iProver_top
% 3.49/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_808,c_798]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_6697,plain,
% 3.49/0.99      ( k1_funct_1(sK7,sK0(X0,k8_relset_1(sK5,sK6,sK7,sK6),sK7)) = X0
% 3.49/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.49/0.99      | v1_funct_1(sK7) != iProver_top
% 3.49/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_2419,c_3014]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_30,plain,
% 3.49/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_32,plain,
% 3.49/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_17,plain,
% 3.49/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/0.99      | v1_relat_1(X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1078,plain,
% 3.49/0.99      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.49/0.99      | v1_relat_1(sK7) ),
% 3.49/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1079,plain,
% 3.49/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.49/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_6810,plain,
% 3.49/0.99      ( k1_funct_1(sK7,sK0(X0,k8_relset_1(sK5,sK6,sK7,sK6),sK7)) = X0
% 3.49/0.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_6697,c_30,c_32,c_1079]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_6825,plain,
% 3.49/0.99      ( k1_funct_1(sK7,sK0(sK4,k8_relset_1(sK5,sK6,sK7,sK6),sK7)) = sK4 ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1628,c_6810]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_25,negated_conjecture,
% 3.49/0.99      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK7,X0) != sK4 ),
% 3.49/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_787,plain,
% 3.49/0.99      ( k1_funct_1(sK7,X0) != sK4 | m1_subset_1(X0,sK5) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_7085,plain,
% 3.49/0.99      ( m1_subset_1(sK0(sK4,k8_relset_1(sK5,sK6,sK7,sK6),sK7),sK5) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_6825,c_787]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_7115,plain,
% 3.49/0.99      ( sK6 = k1_xboole_0
% 3.49/0.99      | m1_subset_1(sK0(sK4,sK5,sK7),sK5) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1755,c_7085]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_7232,plain,
% 3.49/0.99      ( sK6 = k1_xboole_0
% 3.49/0.99      | r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top
% 3.49/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_2077,c_7115]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_7439,plain,
% 3.49/0.99      ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top
% 3.49/0.99      | sK6 = k1_xboole_0 ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_7232,c_32,c_1079]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_7440,plain,
% 3.49/0.99      ( sK6 = k1_xboole_0
% 3.49/0.99      | r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top ),
% 3.49/0.99      inference(renaming,[status(thm)],[c_7439]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_7445,plain,
% 3.49/0.99      ( sK6 = k1_xboole_0
% 3.49/0.99      | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_2424,c_7440]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_8241,plain,
% 3.49/0.99      ( sK6 = k1_xboole_0 ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_7445,c_1628]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_18,plain,
% 3.49/0.99      ( v5_relat_1(X0,X1)
% 3.49/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.49/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_794,plain,
% 3.49/0.99      ( v5_relat_1(X0,X1) = iProver_top
% 3.49/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1317,plain,
% 3.49/0.99      ( v5_relat_1(sK7,sK6) = iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_785,c_794]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_10,plain,
% 3.49/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.49/0.99      | ~ v1_funct_1(X1)
% 3.49/0.99      | ~ v1_relat_1(X1)
% 3.49/0.99      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 3.49/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_802,plain,
% 3.49/0.99      ( k1_funct_1(X0,sK3(X0,X1)) = X1
% 3.49/0.99      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.49/0.99      | v1_funct_1(X0) != iProver_top
% 3.49/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3099,plain,
% 3.49/0.99      ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4
% 3.49/0.99      | v1_funct_1(sK7) != iProver_top
% 3.49/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1628,c_802]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1634,plain,
% 3.49/0.99      ( r2_hidden(sK4,k2_relat_1(sK7)) ),
% 3.49/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1628]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2496,plain,
% 3.49/0.99      ( ~ r2_hidden(sK4,k2_relat_1(sK7))
% 3.49/0.99      | ~ v1_funct_1(sK7)
% 3.49/0.99      | ~ v1_relat_1(sK7)
% 3.49/0.99      | k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
% 3.49/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_3248,plain,
% 3.49/0.99      ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_3099,c_29,c_27,c_1078,c_1634,c_2496]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_12,plain,
% 3.49/0.99      ( ~ v5_relat_1(X0,X1)
% 3.49/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 3.49/0.99      | r2_hidden(k1_funct_1(X0,X2),X1)
% 3.49/0.99      | ~ v1_funct_1(X0)
% 3.49/0.99      | ~ v1_relat_1(X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_800,plain,
% 3.49/0.99      ( v5_relat_1(X0,X1) != iProver_top
% 3.49/0.99      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 3.49/0.99      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 3.49/0.99      | v1_funct_1(X0) != iProver_top
% 3.49/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4052,plain,
% 3.49/0.99      ( v5_relat_1(sK7,X0) != iProver_top
% 3.49/0.99      | r2_hidden(sK3(sK7,sK4),k1_relat_1(sK7)) != iProver_top
% 3.49/0.99      | r2_hidden(sK4,X0) = iProver_top
% 3.49/0.99      | v1_funct_1(sK7) != iProver_top
% 3.49/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_3248,c_800]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_11,plain,
% 3.49/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.49/0.99      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 3.49/0.99      | ~ v1_funct_1(X1)
% 3.49/0.99      | ~ v1_relat_1(X1) ),
% 3.49/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2497,plain,
% 3.49/0.99      ( r2_hidden(sK3(sK7,sK4),k1_relat_1(sK7))
% 3.49/0.99      | ~ r2_hidden(sK4,k2_relat_1(sK7))
% 3.49/0.99      | ~ v1_funct_1(sK7)
% 3.49/0.99      | ~ v1_relat_1(sK7) ),
% 3.49/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_2498,plain,
% 3.49/0.99      ( r2_hidden(sK3(sK7,sK4),k1_relat_1(sK7)) = iProver_top
% 3.49/0.99      | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top
% 3.49/0.99      | v1_funct_1(sK7) != iProver_top
% 3.49/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_2497]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4501,plain,
% 3.49/0.99      ( v5_relat_1(sK7,X0) != iProver_top
% 3.49/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 3.49/0.99      inference(global_propositional_subsumption,
% 3.49/0.99                [status(thm)],
% 3.49/0.99                [c_4052,c_30,c_32,c_1079,c_1628,c_2498]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4509,plain,
% 3.49/0.99      ( r2_hidden(sK4,sK6) = iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_1317,c_4501]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_16,plain,
% 3.49/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_796,plain,
% 3.49/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.49/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_4513,plain,
% 3.49/0.99      ( r1_tarski(sK6,sK4) != iProver_top ),
% 3.49/0.99      inference(superposition,[status(thm)],[c_4509,c_796]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_8247,plain,
% 3.49/0.99      ( r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.49/0.99      inference(demodulation,[status(thm)],[c_8241,c_4513]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_0,plain,
% 3.49/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.49/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1350,plain,
% 3.49/0.99      ( r1_tarski(k1_xboole_0,sK4) ),
% 3.49/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(c_1353,plain,
% 3.49/0.99      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.49/0.99      inference(predicate_to_equality,[status(thm)],[c_1350]) ).
% 3.49/0.99  
% 3.49/0.99  cnf(contradiction,plain,
% 3.49/0.99      ( $false ),
% 3.49/0.99      inference(minisat,[status(thm)],[c_8247,c_1353]) ).
% 3.49/0.99  
% 3.49/0.99  
% 3.49/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/0.99  
% 3.49/0.99  ------                               Statistics
% 3.49/0.99  
% 3.49/0.99  ------ Selected
% 3.49/0.99  
% 3.49/0.99  total_time:                             0.269
% 3.49/0.99  
%------------------------------------------------------------------------------
