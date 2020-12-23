%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:00 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 492 expanded)
%              Number of clauses        :   95 ( 166 expanded)
%              Number of leaves         :   23 ( 110 expanded)
%              Depth                    :   24
%              Number of atoms          :  580 (2256 expanded)
%              Number of equality atoms :  211 ( 482 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f54,plain,(
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

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f33,f56,f55])).

fof(f93,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f57])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f83])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2560,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2543,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_868,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X2
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_37])).

cnf(c_869,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_868])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_871,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_869,c_36])).

cnf(c_2536,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2540,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3392,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2536,c_2540])).

cnf(c_3561,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_871,c_3392])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2541,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3857,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(X0,X1,sK7),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3561,c_2541])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2549,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4270,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK3(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3857,c_2549])).

cnf(c_41,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2815,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3010,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_3011,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3010])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5022,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5023,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5022])).

cnf(c_6020,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | m1_subset_1(sK3(X0,X1,sK7),sK4) = iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4270,c_41,c_3011,c_5023])).

cnf(c_6021,plain,
    ( sK5 = k1_xboole_0
    | m1_subset_1(sK3(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6020])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2539,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2925,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_2536,c_2539])).

cnf(c_35,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2537,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3062,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2925,c_2537])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2542,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_521,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_522,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_2533,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_4625,plain,
    ( k1_funct_1(sK7,sK3(X0,X1,sK7)) = X0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_2533])).

cnf(c_4906,plain,
    ( k1_funct_1(sK7,sK3(sK8,sK6,sK7)) = sK8
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3062,c_4625])).

cnf(c_4940,plain,
    ( ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK8,sK6,sK7)) = sK8 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4906])).

cnf(c_5029,plain,
    ( k1_funct_1(sK7,sK3(sK8,sK6,sK7)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4906,c_36,c_3010,c_4940,c_5022])).

cnf(c_34,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2538,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5034,plain,
    ( m1_subset_1(sK3(sK8,sK6,sK7),sK4) != iProver_top
    | r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5029,c_2538])).

cnf(c_6030,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6021,c_5034])).

cnf(c_6050,plain,
    ( r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6030,c_3062])).

cnf(c_6051,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_6050])).

cnf(c_6056,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_6051])).

cnf(c_6153,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6056,c_41,c_3011,c_3062,c_5023])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2548,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4698,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2536,c_2548])).

cnf(c_943,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != X1
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_36])).

cnf(c_944,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(unflattening,[status(thm)],[c_943])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_950,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_944,c_13])).

cnf(c_952,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_4826,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4698,c_952])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2551,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4833,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_2551])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2556,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5325,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4833,c_2556])).

cnf(c_6156,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,k1_xboole_0)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6153,c_5325])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_6193,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6156,c_10])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_614,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_615,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_616,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_6466,plain,
    ( r2_hidden(X0,sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6193,c_616])).

cnf(c_6473,plain,
    ( v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2560,c_6466])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_506,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_507,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_2534,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_2559,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3485,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_2559])).

cnf(c_16,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2828,plain,
    ( v1_relat_1(sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2829,plain,
    ( v1_relat_1(sK7) = iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2828])).

cnf(c_3661,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3485,c_2829])).

cnf(c_3860,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2541,c_3661])).

cnf(c_4395,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_2829])).

cnf(c_4405,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3062,c_4395])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6473,c_4405])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.10/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.99  
% 3.10/0.99  ------  iProver source info
% 3.10/0.99  
% 3.10/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.99  git: non_committed_changes: false
% 3.10/0.99  git: last_make_outside_of_git: false
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options
% 3.10/0.99  
% 3.10/0.99  --out_options                           all
% 3.10/0.99  --tptp_safe_out                         true
% 3.10/0.99  --problem_path                          ""
% 3.10/0.99  --include_path                          ""
% 3.10/0.99  --clausifier                            res/vclausify_rel
% 3.10/0.99  --clausifier_options                    --mode clausify
% 3.10/0.99  --stdin                                 false
% 3.10/0.99  --stats_out                             all
% 3.10/0.99  
% 3.10/0.99  ------ General Options
% 3.10/0.99  
% 3.10/0.99  --fof                                   false
% 3.10/0.99  --time_out_real                         305.
% 3.10/0.99  --time_out_virtual                      -1.
% 3.10/0.99  --symbol_type_check                     false
% 3.10/0.99  --clausify_out                          false
% 3.10/0.99  --sig_cnt_out                           false
% 3.10/0.99  --trig_cnt_out                          false
% 3.10/0.99  --trig_cnt_out_tolerance                1.
% 3.10/0.99  --trig_cnt_out_sk_spl                   false
% 3.10/0.99  --abstr_cl_out                          false
% 3.10/0.99  
% 3.10/0.99  ------ Global Options
% 3.10/0.99  
% 3.10/0.99  --schedule                              default
% 3.10/0.99  --add_important_lit                     false
% 3.10/0.99  --prop_solver_per_cl                    1000
% 3.10/0.99  --min_unsat_core                        false
% 3.10/0.99  --soft_assumptions                      false
% 3.10/0.99  --soft_lemma_size                       3
% 3.10/0.99  --prop_impl_unit_size                   0
% 3.10/0.99  --prop_impl_unit                        []
% 3.10/0.99  --share_sel_clauses                     true
% 3.10/0.99  --reset_solvers                         false
% 3.10/0.99  --bc_imp_inh                            [conj_cone]
% 3.10/0.99  --conj_cone_tolerance                   3.
% 3.10/0.99  --extra_neg_conj                        none
% 3.10/0.99  --large_theory_mode                     true
% 3.10/0.99  --prolific_symb_bound                   200
% 3.10/0.99  --lt_threshold                          2000
% 3.10/0.99  --clause_weak_htbl                      true
% 3.10/0.99  --gc_record_bc_elim                     false
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing Options
% 3.10/0.99  
% 3.10/0.99  --preprocessing_flag                    true
% 3.10/0.99  --time_out_prep_mult                    0.1
% 3.10/0.99  --splitting_mode                        input
% 3.10/0.99  --splitting_grd                         true
% 3.10/0.99  --splitting_cvd                         false
% 3.10/0.99  --splitting_cvd_svl                     false
% 3.10/0.99  --splitting_nvd                         32
% 3.10/0.99  --sub_typing                            true
% 3.10/0.99  --prep_gs_sim                           true
% 3.10/0.99  --prep_unflatten                        true
% 3.10/0.99  --prep_res_sim                          true
% 3.10/0.99  --prep_upred                            true
% 3.10/0.99  --prep_sem_filter                       exhaustive
% 3.10/0.99  --prep_sem_filter_out                   false
% 3.10/0.99  --pred_elim                             true
% 3.10/0.99  --res_sim_input                         true
% 3.10/0.99  --eq_ax_congr_red                       true
% 3.10/0.99  --pure_diseq_elim                       true
% 3.10/0.99  --brand_transform                       false
% 3.10/0.99  --non_eq_to_eq                          false
% 3.10/0.99  --prep_def_merge                        true
% 3.10/0.99  --prep_def_merge_prop_impl              false
% 3.10/0.99  --prep_def_merge_mbd                    true
% 3.10/0.99  --prep_def_merge_tr_red                 false
% 3.10/0.99  --prep_def_merge_tr_cl                  false
% 3.10/0.99  --smt_preprocessing                     true
% 3.10/0.99  --smt_ac_axioms                         fast
% 3.10/0.99  --preprocessed_out                      false
% 3.10/0.99  --preprocessed_stats                    false
% 3.10/0.99  
% 3.10/0.99  ------ Abstraction refinement Options
% 3.10/0.99  
% 3.10/0.99  --abstr_ref                             []
% 3.10/0.99  --abstr_ref_prep                        false
% 3.10/0.99  --abstr_ref_until_sat                   false
% 3.10/0.99  --abstr_ref_sig_restrict                funpre
% 3.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.99  --abstr_ref_under                       []
% 3.10/0.99  
% 3.10/0.99  ------ SAT Options
% 3.10/0.99  
% 3.10/0.99  --sat_mode                              false
% 3.10/0.99  --sat_fm_restart_options                ""
% 3.10/0.99  --sat_gr_def                            false
% 3.10/0.99  --sat_epr_types                         true
% 3.10/0.99  --sat_non_cyclic_types                  false
% 3.10/0.99  --sat_finite_models                     false
% 3.10/0.99  --sat_fm_lemmas                         false
% 3.10/0.99  --sat_fm_prep                           false
% 3.10/0.99  --sat_fm_uc_incr                        true
% 3.10/0.99  --sat_out_model                         small
% 3.10/0.99  --sat_out_clauses                       false
% 3.10/0.99  
% 3.10/0.99  ------ QBF Options
% 3.10/0.99  
% 3.10/0.99  --qbf_mode                              false
% 3.10/0.99  --qbf_elim_univ                         false
% 3.10/0.99  --qbf_dom_inst                          none
% 3.10/0.99  --qbf_dom_pre_inst                      false
% 3.10/0.99  --qbf_sk_in                             false
% 3.10/0.99  --qbf_pred_elim                         true
% 3.10/0.99  --qbf_split                             512
% 3.10/0.99  
% 3.10/0.99  ------ BMC1 Options
% 3.10/0.99  
% 3.10/0.99  --bmc1_incremental                      false
% 3.10/0.99  --bmc1_axioms                           reachable_all
% 3.10/0.99  --bmc1_min_bound                        0
% 3.10/0.99  --bmc1_max_bound                        -1
% 3.10/0.99  --bmc1_max_bound_default                -1
% 3.10/0.99  --bmc1_symbol_reachability              true
% 3.10/0.99  --bmc1_property_lemmas                  false
% 3.10/0.99  --bmc1_k_induction                      false
% 3.10/0.99  --bmc1_non_equiv_states                 false
% 3.10/0.99  --bmc1_deadlock                         false
% 3.10/0.99  --bmc1_ucm                              false
% 3.10/0.99  --bmc1_add_unsat_core                   none
% 3.10/0.99  --bmc1_unsat_core_children              false
% 3.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.99  --bmc1_out_stat                         full
% 3.10/0.99  --bmc1_ground_init                      false
% 3.10/0.99  --bmc1_pre_inst_next_state              false
% 3.10/0.99  --bmc1_pre_inst_state                   false
% 3.10/0.99  --bmc1_pre_inst_reach_state             false
% 3.10/0.99  --bmc1_out_unsat_core                   false
% 3.10/0.99  --bmc1_aig_witness_out                  false
% 3.10/0.99  --bmc1_verbose                          false
% 3.10/0.99  --bmc1_dump_clauses_tptp                false
% 3.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.99  --bmc1_dump_file                        -
% 3.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.99  --bmc1_ucm_extend_mode                  1
% 3.10/0.99  --bmc1_ucm_init_mode                    2
% 3.10/0.99  --bmc1_ucm_cone_mode                    none
% 3.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.99  --bmc1_ucm_relax_model                  4
% 3.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.99  --bmc1_ucm_layered_model                none
% 3.10/0.99  --bmc1_ucm_max_lemma_size               10
% 3.10/0.99  
% 3.10/0.99  ------ AIG Options
% 3.10/0.99  
% 3.10/0.99  --aig_mode                              false
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation Options
% 3.10/0.99  
% 3.10/0.99  --instantiation_flag                    true
% 3.10/0.99  --inst_sos_flag                         false
% 3.10/0.99  --inst_sos_phase                        true
% 3.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel_side                     num_symb
% 3.10/0.99  --inst_solver_per_active                1400
% 3.10/0.99  --inst_solver_calls_frac                1.
% 3.10/0.99  --inst_passive_queue_type               priority_queues
% 3.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.99  --inst_passive_queues_freq              [25;2]
% 3.10/0.99  --inst_dismatching                      true
% 3.10/0.99  --inst_eager_unprocessed_to_passive     true
% 3.10/0.99  --inst_prop_sim_given                   true
% 3.10/0.99  --inst_prop_sim_new                     false
% 3.10/0.99  --inst_subs_new                         false
% 3.10/0.99  --inst_eq_res_simp                      false
% 3.10/0.99  --inst_subs_given                       false
% 3.10/0.99  --inst_orphan_elimination               true
% 3.10/0.99  --inst_learning_loop_flag               true
% 3.10/0.99  --inst_learning_start                   3000
% 3.10/0.99  --inst_learning_factor                  2
% 3.10/0.99  --inst_start_prop_sim_after_learn       3
% 3.10/0.99  --inst_sel_renew                        solver
% 3.10/0.99  --inst_lit_activity_flag                true
% 3.10/0.99  --inst_restr_to_given                   false
% 3.10/0.99  --inst_activity_threshold               500
% 3.10/0.99  --inst_out_proof                        true
% 3.10/0.99  
% 3.10/0.99  ------ Resolution Options
% 3.10/0.99  
% 3.10/0.99  --resolution_flag                       true
% 3.10/0.99  --res_lit_sel                           adaptive
% 3.10/0.99  --res_lit_sel_side                      none
% 3.10/0.99  --res_ordering                          kbo
% 3.10/0.99  --res_to_prop_solver                    active
% 3.10/0.99  --res_prop_simpl_new                    false
% 3.10/0.99  --res_prop_simpl_given                  true
% 3.10/0.99  --res_passive_queue_type                priority_queues
% 3.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.99  --res_passive_queues_freq               [15;5]
% 3.10/0.99  --res_forward_subs                      full
% 3.10/0.99  --res_backward_subs                     full
% 3.10/0.99  --res_forward_subs_resolution           true
% 3.10/0.99  --res_backward_subs_resolution          true
% 3.10/0.99  --res_orphan_elimination                true
% 3.10/0.99  --res_time_limit                        2.
% 3.10/0.99  --res_out_proof                         true
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Options
% 3.10/0.99  
% 3.10/0.99  --superposition_flag                    true
% 3.10/0.99  --sup_passive_queue_type                priority_queues
% 3.10/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.99  --demod_completeness_check              fast
% 3.10/0.99  --demod_use_ground                      true
% 3.10/0.99  --sup_to_prop_solver                    passive
% 3.10/0.99  --sup_prop_simpl_new                    true
% 3.10/0.99  --sup_prop_simpl_given                  true
% 3.10/0.99  --sup_fun_splitting                     false
% 3.10/0.99  --sup_smt_interval                      50000
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Simplification Setup
% 3.10/0.99  
% 3.10/0.99  --sup_indices_passive                   []
% 3.10/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_full_bw                           [BwDemod]
% 3.10/0.99  --sup_immed_triv                        [TrivRules]
% 3.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_immed_bw_main                     []
% 3.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  
% 3.10/0.99  ------ Combination Options
% 3.10/0.99  
% 3.10/0.99  --comb_res_mult                         3
% 3.10/0.99  --comb_sup_mult                         2
% 3.10/0.99  --comb_inst_mult                        10
% 3.10/0.99  
% 3.10/0.99  ------ Debug Options
% 3.10/0.99  
% 3.10/0.99  --dbg_backtrace                         false
% 3.10/0.99  --dbg_dump_prop_clauses                 false
% 3.10/0.99  --dbg_dump_prop_clauses_file            -
% 3.10/0.99  --dbg_out_stat                          false
% 3.10/0.99  ------ Parsing...
% 3.10/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.99  ------ Proving...
% 3.10/0.99  ------ Problem Properties 
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  clauses                                 34
% 3.10/0.99  conjectures                             3
% 3.10/0.99  EPR                                     6
% 3.10/0.99  Horn                                    27
% 3.10/0.99  unary                                   7
% 3.10/0.99  binary                                  11
% 3.10/0.99  lits                                    80
% 3.10/0.99  lits eq                                 18
% 3.10/0.99  fd_pure                                 0
% 3.10/0.99  fd_pseudo                               0
% 3.10/0.99  fd_cond                                 1
% 3.10/0.99  fd_pseudo_cond                          3
% 3.10/0.99  AC symbols                              0
% 3.10/0.99  
% 3.10/0.99  ------ Schedule dynamic 5 is on 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  Current options:
% 3.10/0.99  ------ 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options
% 3.10/0.99  
% 3.10/0.99  --out_options                           all
% 3.10/0.99  --tptp_safe_out                         true
% 3.10/0.99  --problem_path                          ""
% 3.10/0.99  --include_path                          ""
% 3.10/0.99  --clausifier                            res/vclausify_rel
% 3.10/0.99  --clausifier_options                    --mode clausify
% 3.10/0.99  --stdin                                 false
% 3.10/0.99  --stats_out                             all
% 3.10/0.99  
% 3.10/0.99  ------ General Options
% 3.10/0.99  
% 3.10/0.99  --fof                                   false
% 3.10/0.99  --time_out_real                         305.
% 3.10/0.99  --time_out_virtual                      -1.
% 3.10/0.99  --symbol_type_check                     false
% 3.10/0.99  --clausify_out                          false
% 3.10/0.99  --sig_cnt_out                           false
% 3.10/0.99  --trig_cnt_out                          false
% 3.10/0.99  --trig_cnt_out_tolerance                1.
% 3.10/0.99  --trig_cnt_out_sk_spl                   false
% 3.10/0.99  --abstr_cl_out                          false
% 3.10/0.99  
% 3.10/0.99  ------ Global Options
% 3.10/0.99  
% 3.10/0.99  --schedule                              default
% 3.10/0.99  --add_important_lit                     false
% 3.10/0.99  --prop_solver_per_cl                    1000
% 3.10/0.99  --min_unsat_core                        false
% 3.10/0.99  --soft_assumptions                      false
% 3.10/0.99  --soft_lemma_size                       3
% 3.10/0.99  --prop_impl_unit_size                   0
% 3.10/0.99  --prop_impl_unit                        []
% 3.10/0.99  --share_sel_clauses                     true
% 3.10/0.99  --reset_solvers                         false
% 3.10/0.99  --bc_imp_inh                            [conj_cone]
% 3.10/0.99  --conj_cone_tolerance                   3.
% 3.10/0.99  --extra_neg_conj                        none
% 3.10/0.99  --large_theory_mode                     true
% 3.10/0.99  --prolific_symb_bound                   200
% 3.10/0.99  --lt_threshold                          2000
% 3.10/0.99  --clause_weak_htbl                      true
% 3.10/0.99  --gc_record_bc_elim                     false
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing Options
% 3.10/0.99  
% 3.10/0.99  --preprocessing_flag                    true
% 3.10/0.99  --time_out_prep_mult                    0.1
% 3.10/0.99  --splitting_mode                        input
% 3.10/0.99  --splitting_grd                         true
% 3.10/0.99  --splitting_cvd                         false
% 3.10/0.99  --splitting_cvd_svl                     false
% 3.10/0.99  --splitting_nvd                         32
% 3.10/0.99  --sub_typing                            true
% 3.10/0.99  --prep_gs_sim                           true
% 3.10/0.99  --prep_unflatten                        true
% 3.10/0.99  --prep_res_sim                          true
% 3.10/0.99  --prep_upred                            true
% 3.10/0.99  --prep_sem_filter                       exhaustive
% 3.10/0.99  --prep_sem_filter_out                   false
% 3.10/0.99  --pred_elim                             true
% 3.10/0.99  --res_sim_input                         true
% 3.10/0.99  --eq_ax_congr_red                       true
% 3.10/0.99  --pure_diseq_elim                       true
% 3.10/0.99  --brand_transform                       false
% 3.10/0.99  --non_eq_to_eq                          false
% 3.10/0.99  --prep_def_merge                        true
% 3.10/0.99  --prep_def_merge_prop_impl              false
% 3.10/0.99  --prep_def_merge_mbd                    true
% 3.10/0.99  --prep_def_merge_tr_red                 false
% 3.10/0.99  --prep_def_merge_tr_cl                  false
% 3.10/0.99  --smt_preprocessing                     true
% 3.10/0.99  --smt_ac_axioms                         fast
% 3.10/0.99  --preprocessed_out                      false
% 3.10/0.99  --preprocessed_stats                    false
% 3.10/0.99  
% 3.10/0.99  ------ Abstraction refinement Options
% 3.10/0.99  
% 3.10/0.99  --abstr_ref                             []
% 3.10/0.99  --abstr_ref_prep                        false
% 3.10/0.99  --abstr_ref_until_sat                   false
% 3.10/0.99  --abstr_ref_sig_restrict                funpre
% 3.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.99  --abstr_ref_under                       []
% 3.10/0.99  
% 3.10/0.99  ------ SAT Options
% 3.10/0.99  
% 3.10/0.99  --sat_mode                              false
% 3.10/0.99  --sat_fm_restart_options                ""
% 3.10/0.99  --sat_gr_def                            false
% 3.10/0.99  --sat_epr_types                         true
% 3.10/0.99  --sat_non_cyclic_types                  false
% 3.10/0.99  --sat_finite_models                     false
% 3.10/0.99  --sat_fm_lemmas                         false
% 3.10/0.99  --sat_fm_prep                           false
% 3.10/0.99  --sat_fm_uc_incr                        true
% 3.10/0.99  --sat_out_model                         small
% 3.10/0.99  --sat_out_clauses                       false
% 3.10/0.99  
% 3.10/0.99  ------ QBF Options
% 3.10/0.99  
% 3.10/0.99  --qbf_mode                              false
% 3.10/0.99  --qbf_elim_univ                         false
% 3.10/0.99  --qbf_dom_inst                          none
% 3.10/0.99  --qbf_dom_pre_inst                      false
% 3.10/0.99  --qbf_sk_in                             false
% 3.10/0.99  --qbf_pred_elim                         true
% 3.10/0.99  --qbf_split                             512
% 3.10/0.99  
% 3.10/0.99  ------ BMC1 Options
% 3.10/0.99  
% 3.10/0.99  --bmc1_incremental                      false
% 3.10/0.99  --bmc1_axioms                           reachable_all
% 3.10/0.99  --bmc1_min_bound                        0
% 3.10/0.99  --bmc1_max_bound                        -1
% 3.10/0.99  --bmc1_max_bound_default                -1
% 3.10/0.99  --bmc1_symbol_reachability              true
% 3.10/0.99  --bmc1_property_lemmas                  false
% 3.10/0.99  --bmc1_k_induction                      false
% 3.10/0.99  --bmc1_non_equiv_states                 false
% 3.10/0.99  --bmc1_deadlock                         false
% 3.10/0.99  --bmc1_ucm                              false
% 3.10/0.99  --bmc1_add_unsat_core                   none
% 3.10/0.99  --bmc1_unsat_core_children              false
% 3.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.99  --bmc1_out_stat                         full
% 3.10/0.99  --bmc1_ground_init                      false
% 3.10/0.99  --bmc1_pre_inst_next_state              false
% 3.10/0.99  --bmc1_pre_inst_state                   false
% 3.10/0.99  --bmc1_pre_inst_reach_state             false
% 3.10/0.99  --bmc1_out_unsat_core                   false
% 3.10/0.99  --bmc1_aig_witness_out                  false
% 3.10/0.99  --bmc1_verbose                          false
% 3.10/0.99  --bmc1_dump_clauses_tptp                false
% 3.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.99  --bmc1_dump_file                        -
% 3.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.99  --bmc1_ucm_extend_mode                  1
% 3.10/0.99  --bmc1_ucm_init_mode                    2
% 3.10/0.99  --bmc1_ucm_cone_mode                    none
% 3.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.99  --bmc1_ucm_relax_model                  4
% 3.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.99  --bmc1_ucm_layered_model                none
% 3.10/0.99  --bmc1_ucm_max_lemma_size               10
% 3.10/0.99  
% 3.10/0.99  ------ AIG Options
% 3.10/0.99  
% 3.10/0.99  --aig_mode                              false
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation Options
% 3.10/0.99  
% 3.10/0.99  --instantiation_flag                    true
% 3.10/0.99  --inst_sos_flag                         false
% 3.10/0.99  --inst_sos_phase                        true
% 3.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel_side                     none
% 3.10/0.99  --inst_solver_per_active                1400
% 3.10/0.99  --inst_solver_calls_frac                1.
% 3.10/0.99  --inst_passive_queue_type               priority_queues
% 3.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.99  --inst_passive_queues_freq              [25;2]
% 3.10/0.99  --inst_dismatching                      true
% 3.10/0.99  --inst_eager_unprocessed_to_passive     true
% 3.10/0.99  --inst_prop_sim_given                   true
% 3.10/0.99  --inst_prop_sim_new                     false
% 3.10/0.99  --inst_subs_new                         false
% 3.10/0.99  --inst_eq_res_simp                      false
% 3.10/0.99  --inst_subs_given                       false
% 3.10/0.99  --inst_orphan_elimination               true
% 3.10/0.99  --inst_learning_loop_flag               true
% 3.10/0.99  --inst_learning_start                   3000
% 3.10/0.99  --inst_learning_factor                  2
% 3.10/0.99  --inst_start_prop_sim_after_learn       3
% 3.10/0.99  --inst_sel_renew                        solver
% 3.10/0.99  --inst_lit_activity_flag                true
% 3.10/0.99  --inst_restr_to_given                   false
% 3.10/0.99  --inst_activity_threshold               500
% 3.10/0.99  --inst_out_proof                        true
% 3.10/0.99  
% 3.10/0.99  ------ Resolution Options
% 3.10/0.99  
% 3.10/0.99  --resolution_flag                       false
% 3.10/0.99  --res_lit_sel                           adaptive
% 3.10/0.99  --res_lit_sel_side                      none
% 3.10/0.99  --res_ordering                          kbo
% 3.10/0.99  --res_to_prop_solver                    active
% 3.10/0.99  --res_prop_simpl_new                    false
% 3.10/0.99  --res_prop_simpl_given                  true
% 3.10/0.99  --res_passive_queue_type                priority_queues
% 3.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.99  --res_passive_queues_freq               [15;5]
% 3.10/0.99  --res_forward_subs                      full
% 3.10/0.99  --res_backward_subs                     full
% 3.10/0.99  --res_forward_subs_resolution           true
% 3.10/0.99  --res_backward_subs_resolution          true
% 3.10/0.99  --res_orphan_elimination                true
% 3.10/0.99  --res_time_limit                        2.
% 3.10/0.99  --res_out_proof                         true
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Options
% 3.10/0.99  
% 3.10/0.99  --superposition_flag                    true
% 3.10/0.99  --sup_passive_queue_type                priority_queues
% 3.10/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.99  --demod_completeness_check              fast
% 3.10/0.99  --demod_use_ground                      true
% 3.10/0.99  --sup_to_prop_solver                    passive
% 3.10/0.99  --sup_prop_simpl_new                    true
% 3.10/0.99  --sup_prop_simpl_given                  true
% 3.10/0.99  --sup_fun_splitting                     false
% 3.10/0.99  --sup_smt_interval                      50000
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Simplification Setup
% 3.10/0.99  
% 3.10/0.99  --sup_indices_passive                   []
% 3.10/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_full_bw                           [BwDemod]
% 3.10/0.99  --sup_immed_triv                        [TrivRules]
% 3.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_immed_bw_main                     []
% 3.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  
% 3.10/0.99  ------ Combination Options
% 3.10/0.99  
% 3.10/0.99  --comb_res_mult                         3
% 3.10/0.99  --comb_sup_mult                         2
% 3.10/0.99  --comb_inst_mult                        10
% 3.10/0.99  
% 3.10/0.99  ------ Debug Options
% 3.10/0.99  
% 3.10/0.99  --dbg_backtrace                         false
% 3.10/0.99  --dbg_dump_prop_clauses                 false
% 3.10/0.99  --dbg_dump_prop_clauses_file            -
% 3.10/0.99  --dbg_out_stat                          false
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ Proving...
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS status Theorem for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  fof(f1,axiom,(
% 3.10/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f34,plain,(
% 3.10/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.10/1.00    inference(nnf_transformation,[],[f1])).
% 3.10/1.00  
% 3.10/1.00  fof(f35,plain,(
% 3.10/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/1.00    inference(rectify,[],[f34])).
% 3.10/1.00  
% 3.10/1.00  fof(f36,plain,(
% 3.10/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f37,plain,(
% 3.10/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.10/1.00  
% 3.10/1.00  fof(f59,plain,(
% 3.10/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f37])).
% 3.10/1.00  
% 3.10/1.00  fof(f12,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f25,plain,(
% 3.10/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(ennf_transformation,[],[f12])).
% 3.10/1.00  
% 3.10/1.00  fof(f48,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(nnf_transformation,[],[f25])).
% 3.10/1.00  
% 3.10/1.00  fof(f49,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(rectify,[],[f48])).
% 3.10/1.00  
% 3.10/1.00  fof(f50,plain,(
% 3.10/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f51,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f49,f50])).
% 3.10/1.00  
% 3.10/1.00  fof(f79,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f51])).
% 3.10/1.00  
% 3.10/1.00  fof(f16,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f30,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f16])).
% 3.10/1.00  
% 3.10/1.00  fof(f31,plain,(
% 3.10/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(flattening,[],[f30])).
% 3.10/1.00  
% 3.10/1.00  fof(f54,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(nnf_transformation,[],[f31])).
% 3.10/1.00  
% 3.10/1.00  fof(f86,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f54])).
% 3.10/1.00  
% 3.10/1.00  fof(f17,conjecture,(
% 3.10/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f18,negated_conjecture,(
% 3.10/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.10/1.00    inference(negated_conjecture,[],[f17])).
% 3.10/1.00  
% 3.10/1.00  fof(f32,plain,(
% 3.10/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.10/1.00    inference(ennf_transformation,[],[f18])).
% 3.10/1.00  
% 3.10/1.00  fof(f33,plain,(
% 3.10/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.10/1.00    inference(flattening,[],[f32])).
% 3.10/1.00  
% 3.10/1.00  fof(f56,plain,(
% 3.10/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f55,plain,(
% 3.10/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f57,plain,(
% 3.10/1.00    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f33,f56,f55])).
% 3.10/1.00  
% 3.10/1.00  fof(f93,plain,(
% 3.10/1.00    v1_funct_2(sK7,sK4,sK5)),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f94,plain,(
% 3.10/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f14,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f28,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f14])).
% 3.10/1.00  
% 3.10/1.00  fof(f84,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f28])).
% 3.10/1.00  
% 3.10/1.00  fof(f77,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f51])).
% 3.10/1.00  
% 3.10/1.00  fof(f7,axiom,(
% 3.10/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f20,plain,(
% 3.10/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.10/1.00    inference(ennf_transformation,[],[f7])).
% 3.10/1.00  
% 3.10/1.00  fof(f72,plain,(
% 3.10/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f20])).
% 3.10/1.00  
% 3.10/1.00  fof(f10,axiom,(
% 3.10/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f24,plain,(
% 3.10/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f10])).
% 3.10/1.00  
% 3.10/1.00  fof(f75,plain,(
% 3.10/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f24])).
% 3.10/1.00  
% 3.10/1.00  fof(f11,axiom,(
% 3.10/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f76,plain,(
% 3.10/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f11])).
% 3.10/1.00  
% 3.10/1.00  fof(f15,axiom,(
% 3.10/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f29,plain,(
% 3.10/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/1.00    inference(ennf_transformation,[],[f15])).
% 3.10/1.00  
% 3.10/1.00  fof(f85,plain,(
% 3.10/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f29])).
% 3.10/1.00  
% 3.10/1.00  fof(f95,plain,(
% 3.10/1.00    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f78,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f51])).
% 3.10/1.00  
% 3.10/1.00  fof(f13,axiom,(
% 3.10/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f26,plain,(
% 3.10/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.10/1.00    inference(ennf_transformation,[],[f13])).
% 3.10/1.00  
% 3.10/1.00  fof(f27,plain,(
% 3.10/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(flattening,[],[f26])).
% 3.10/1.00  
% 3.10/1.00  fof(f52,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(nnf_transformation,[],[f27])).
% 3.10/1.00  
% 3.10/1.00  fof(f53,plain,(
% 3.10/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.10/1.00    inference(flattening,[],[f52])).
% 3.10/1.00  
% 3.10/1.00  fof(f82,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f53])).
% 3.10/1.00  
% 3.10/1.00  fof(f92,plain,(
% 3.10/1.00    v1_funct_1(sK7)),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f96,plain,(
% 3.10/1.00    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f57])).
% 3.10/1.00  
% 3.10/1.00  fof(f8,axiom,(
% 3.10/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f21,plain,(
% 3.10/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.10/1.00    inference(ennf_transformation,[],[f8])).
% 3.10/1.00  
% 3.10/1.00  fof(f22,plain,(
% 3.10/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.10/1.00    inference(flattening,[],[f21])).
% 3.10/1.00  
% 3.10/1.00  fof(f73,plain,(
% 3.10/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f22])).
% 3.10/1.00  
% 3.10/1.00  fof(f6,axiom,(
% 3.10/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f71,plain,(
% 3.10/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.10/1.00    inference(cnf_transformation,[],[f6])).
% 3.10/1.00  
% 3.10/1.00  fof(f4,axiom,(
% 3.10/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f42,plain,(
% 3.10/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.10/1.00    inference(nnf_transformation,[],[f4])).
% 3.10/1.00  
% 3.10/1.00  fof(f43,plain,(
% 3.10/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.10/1.00    inference(rectify,[],[f42])).
% 3.10/1.00  
% 3.10/1.00  fof(f44,plain,(
% 3.10/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f45,plain,(
% 3.10/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 3.10/1.00  
% 3.10/1.00  fof(f64,plain,(
% 3.10/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.10/1.00    inference(cnf_transformation,[],[f45])).
% 3.10/1.00  
% 3.10/1.00  fof(f98,plain,(
% 3.10/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.10/1.00    inference(equality_resolution,[],[f64])).
% 3.10/1.00  
% 3.10/1.00  fof(f2,axiom,(
% 3.10/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f19,plain,(
% 3.10/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.10/1.00    inference(ennf_transformation,[],[f2])).
% 3.10/1.00  
% 3.10/1.00  fof(f38,plain,(
% 3.10/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/1.00    inference(nnf_transformation,[],[f19])).
% 3.10/1.00  
% 3.10/1.00  fof(f39,plain,(
% 3.10/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/1.00    inference(rectify,[],[f38])).
% 3.10/1.00  
% 3.10/1.00  fof(f40,plain,(
% 3.10/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.10/1.00    introduced(choice_axiom,[])).
% 3.10/1.00  
% 3.10/1.00  fof(f41,plain,(
% 3.10/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.10/1.00  
% 3.10/1.00  fof(f60,plain,(
% 3.10/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f41])).
% 3.10/1.00  
% 3.10/1.00  fof(f5,axiom,(
% 3.10/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f46,plain,(
% 3.10/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/1.00    inference(nnf_transformation,[],[f5])).
% 3.10/1.00  
% 3.10/1.00  fof(f47,plain,(
% 3.10/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/1.00    inference(flattening,[],[f46])).
% 3.10/1.00  
% 3.10/1.00  fof(f70,plain,(
% 3.10/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.10/1.00    inference(cnf_transformation,[],[f47])).
% 3.10/1.00  
% 3.10/1.00  fof(f99,plain,(
% 3.10/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.10/1.00    inference(equality_resolution,[],[f70])).
% 3.10/1.00  
% 3.10/1.00  fof(f58,plain,(
% 3.10/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f37])).
% 3.10/1.00  
% 3.10/1.00  fof(f3,axiom,(
% 3.10/1.00    v1_xboole_0(k1_xboole_0)),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f63,plain,(
% 3.10/1.00    v1_xboole_0(k1_xboole_0)),
% 3.10/1.00    inference(cnf_transformation,[],[f3])).
% 3.10/1.00  
% 3.10/1.00  fof(f83,plain,(
% 3.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f53])).
% 3.10/1.00  
% 3.10/1.00  fof(f101,plain,(
% 3.10/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.10/1.00    inference(equality_resolution,[],[f83])).
% 3.10/1.00  
% 3.10/1.00  fof(f9,axiom,(
% 3.10/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.10/1.00  
% 3.10/1.00  fof(f23,plain,(
% 3.10/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.10/1.00    inference(ennf_transformation,[],[f9])).
% 3.10/1.00  
% 3.10/1.00  fof(f74,plain,(
% 3.10/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.10/1.00    inference(cnf_transformation,[],[f23])).
% 3.10/1.00  
% 3.10/1.00  cnf(c_0,plain,
% 3.10/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2560,plain,
% 3.10/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.10/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_20,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.00      | r2_hidden(sK3(X0,X2,X1),X2)
% 3.10/1.00      | ~ v1_relat_1(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2543,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.10/1.00      | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
% 3.10/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_33,plain,
% 3.10/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.10/1.00      | k1_xboole_0 = X2 ),
% 3.10/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_37,negated_conjecture,
% 3.10/1.00      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.10/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_868,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.10/1.00      | sK5 != X2
% 3.10/1.00      | sK4 != X1
% 3.10/1.00      | sK7 != X0
% 3.10/1.00      | k1_xboole_0 = X2 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_37]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_869,plain,
% 3.10/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.10/1.00      | k1_relset_1(sK4,sK5,sK7) = sK4
% 3.10/1.00      | k1_xboole_0 = sK5 ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_868]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_36,negated_conjecture,
% 3.10/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.10/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_871,plain,
% 3.10/1.00      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_869,c_36]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2536,plain,
% 3.10/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_26,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2540,plain,
% 3.10/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.10/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3392,plain,
% 3.10/1.00      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2536,c_2540]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3561,plain,
% 3.10/1.00      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_871,c_3392]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_22,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.00      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
% 3.10/1.00      | ~ v1_relat_1(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2541,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.10/1.00      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.10/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3857,plain,
% 3.10/1.00      ( sK5 = k1_xboole_0
% 3.10/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.00      | r2_hidden(sK3(X0,X1,sK7),sK4) = iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3561,c_2541]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_14,plain,
% 3.10/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2549,plain,
% 3.10/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.10/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4270,plain,
% 3.10/1.00      ( sK5 = k1_xboole_0
% 3.10/1.00      | m1_subset_1(sK3(X0,X1,sK7),sK4) = iProver_top
% 3.10/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3857,c_2549]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_41,plain,
% 3.10/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_17,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.10/1.00      | ~ v1_relat_1(X1)
% 3.10/1.00      | v1_relat_1(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2815,plain,
% 3.10/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 3.10/1.00      | ~ v1_relat_1(X0)
% 3.10/1.00      | v1_relat_1(sK7) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3010,plain,
% 3.10/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.10/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 3.10/1.00      | v1_relat_1(sK7) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_2815]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3011,plain,
% 3.10/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.10/1.00      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.10/1.00      | v1_relat_1(sK7) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_3010]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_18,plain,
% 3.10/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5022,plain,
% 3.10/1.00      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5023,plain,
% 3.10/1.00      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_5022]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6020,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.00      | m1_subset_1(sK3(X0,X1,sK7),sK4) = iProver_top
% 3.10/1.00      | sK5 = k1_xboole_0 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_4270,c_41,c_3011,c_5023]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6021,plain,
% 3.10/1.00      ( sK5 = k1_xboole_0
% 3.10/1.00      | m1_subset_1(sK3(X0,X1,sK7),sK4) = iProver_top
% 3.10/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_6020]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_27,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.10/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2539,plain,
% 3.10/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.10/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2925,plain,
% 3.10/1.00      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2536,c_2539]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_35,negated_conjecture,
% 3.10/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2537,plain,
% 3.10/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3062,plain,
% 3.10/1.00      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_2925,c_2537]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_21,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.10/1.00      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 3.10/1.00      | ~ v1_relat_1(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2542,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.10/1.00      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
% 3.10/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_24,plain,
% 3.10/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.10/1.00      | ~ v1_funct_1(X2)
% 3.10/1.00      | ~ v1_relat_1(X2)
% 3.10/1.00      | k1_funct_1(X2,X0) = X1 ),
% 3.10/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_38,negated_conjecture,
% 3.10/1.00      ( v1_funct_1(sK7) ),
% 3.10/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_521,plain,
% 3.10/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.10/1.00      | ~ v1_relat_1(X2)
% 3.10/1.00      | k1_funct_1(X2,X0) = X1
% 3.10/1.00      | sK7 != X2 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_38]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_522,plain,
% 3.10/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.10/1.00      | ~ v1_relat_1(sK7)
% 3.10/1.00      | k1_funct_1(sK7,X0) = X1 ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_521]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2533,plain,
% 3.10/1.00      ( k1_funct_1(sK7,X0) = X1
% 3.10/1.00      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4625,plain,
% 3.10/1.00      ( k1_funct_1(sK7,sK3(X0,X1,sK7)) = X0
% 3.10/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2542,c_2533]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4906,plain,
% 3.10/1.00      ( k1_funct_1(sK7,sK3(sK8,sK6,sK7)) = sK8
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3062,c_4625]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4940,plain,
% 3.10/1.00      ( ~ v1_relat_1(sK7) | k1_funct_1(sK7,sK3(sK8,sK6,sK7)) = sK8 ),
% 3.10/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4906]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5029,plain,
% 3.10/1.00      ( k1_funct_1(sK7,sK3(sK8,sK6,sK7)) = sK8 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_4906,c_36,c_3010,c_4940,c_5022]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_34,negated_conjecture,
% 3.10/1.00      ( ~ m1_subset_1(X0,sK4)
% 3.10/1.00      | ~ r2_hidden(X0,sK6)
% 3.10/1.00      | k1_funct_1(sK7,X0) != sK8 ),
% 3.10/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2538,plain,
% 3.10/1.00      ( k1_funct_1(sK7,X0) != sK8
% 3.10/1.00      | m1_subset_1(X0,sK4) != iProver_top
% 3.10/1.00      | r2_hidden(X0,sK6) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5034,plain,
% 3.10/1.00      ( m1_subset_1(sK3(sK8,sK6,sK7),sK4) != iProver_top
% 3.10/1.00      | r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_5029,c_2538]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6030,plain,
% 3.10/1.00      ( sK5 = k1_xboole_0
% 3.10/1.00      | r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top
% 3.10/1.00      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_6021,c_5034]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6050,plain,
% 3.10/1.00      ( r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top
% 3.10/1.00      | sK5 = k1_xboole_0 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_6030,c_3062]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6051,plain,
% 3.10/1.00      ( sK5 = k1_xboole_0
% 3.10/1.00      | r2_hidden(sK3(sK8,sK6,sK7),sK6) != iProver_top ),
% 3.10/1.00      inference(renaming,[status(thm)],[c_6050]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6056,plain,
% 3.10/1.00      ( sK5 = k1_xboole_0
% 3.10/1.00      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2543,c_6051]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6153,plain,
% 3.10/1.00      ( sK5 = k1_xboole_0 ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_6056,c_41,c_3011,c_3062,c_5023]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_15,plain,
% 3.10/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2548,plain,
% 3.10/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.10/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.10/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4698,plain,
% 3.10/1.00      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 3.10/1.00      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2536,c_2548]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_943,plain,
% 3.10/1.00      ( r2_hidden(X0,X1)
% 3.10/1.00      | v1_xboole_0(X1)
% 3.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != X1
% 3.10/1.00      | sK7 != X0 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_36]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_944,plain,
% 3.10/1.00      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.10/1.00      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_943]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_13,plain,
% 3.10/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_950,plain,
% 3.10/1.00      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.10/1.00      inference(forward_subsumption_resolution,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_944,c_13]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_952,plain,
% 3.10/1.00      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4826,plain,
% 3.10/1.00      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_4698,c_952]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_9,plain,
% 3.10/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.10/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2551,plain,
% 3.10/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.10/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4833,plain,
% 3.10/1.00      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_4826,c_2551]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4,plain,
% 3.10/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2556,plain,
% 3.10/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.10/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.10/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5325,plain,
% 3.10/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
% 3.10/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_4833,c_2556]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6156,plain,
% 3.10/1.00      ( r2_hidden(X0,k2_zfmisc_1(sK4,k1_xboole_0)) = iProver_top
% 3.10/1.00      | r2_hidden(X0,sK7) != iProver_top ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_6153,c_5325]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_10,plain,
% 3.10/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.10/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6193,plain,
% 3.10/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.10/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.10/1.00      inference(demodulation,[status(thm)],[c_6156,c_10]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_1,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_5,plain,
% 3.10/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_614,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_615,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_614]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_616,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6466,plain,
% 3.10/1.00      ( r2_hidden(X0,sK7) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_6193,c_616]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_6473,plain,
% 3.10/1.00      ( v1_xboole_0(sK7) = iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2560,c_6466]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_23,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.10/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.10/1.00      | ~ v1_funct_1(X1)
% 3.10/1.00      | ~ v1_relat_1(X1) ),
% 3.10/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_506,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.10/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.10/1.00      | ~ v1_relat_1(X1)
% 3.10/1.00      | sK7 != X1 ),
% 3.10/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_507,plain,
% 3.10/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.10/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
% 3.10/1.00      | ~ v1_relat_1(sK7) ),
% 3.10/1.00      inference(unflattening,[status(thm)],[c_506]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2534,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.10/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2559,plain,
% 3.10/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.10/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3485,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top
% 3.10/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2534,c_2559]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_16,plain,
% 3.10/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.10/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2828,plain,
% 3.10/1.00      ( v1_relat_1(sK7) | ~ v1_xboole_0(sK7) ),
% 3.10/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_2829,plain,
% 3.10/1.00      ( v1_relat_1(sK7) = iProver_top | v1_xboole_0(sK7) != iProver_top ),
% 3.10/1.00      inference(predicate_to_equality,[status(thm)],[c_2828]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3661,plain,
% 3.10/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.10/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_3485,c_2829]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_3860,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.00      | v1_relat_1(sK7) != iProver_top
% 3.10/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_2541,c_3661]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4395,plain,
% 3.10/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.10/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.10/1.00      inference(global_propositional_subsumption,
% 3.10/1.00                [status(thm)],
% 3.10/1.00                [c_3860,c_2829]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(c_4405,plain,
% 3.10/1.00      ( v1_xboole_0(sK7) != iProver_top ),
% 3.10/1.00      inference(superposition,[status(thm)],[c_3062,c_4395]) ).
% 3.10/1.00  
% 3.10/1.00  cnf(contradiction,plain,
% 3.10/1.00      ( $false ),
% 3.10/1.00      inference(minisat,[status(thm)],[c_6473,c_4405]) ).
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/1.00  
% 3.10/1.00  ------                               Statistics
% 3.10/1.00  
% 3.10/1.00  ------ General
% 3.10/1.00  
% 3.10/1.00  abstr_ref_over_cycles:                  0
% 3.10/1.00  abstr_ref_under_cycles:                 0
% 3.10/1.00  gc_basic_clause_elim:                   0
% 3.10/1.00  forced_gc_time:                         0
% 3.10/1.00  parsing_time:                           0.026
% 3.10/1.00  unif_index_cands_time:                  0.
% 3.10/1.00  unif_index_add_time:                    0.
% 3.10/1.00  orderings_time:                         0.
% 3.10/1.00  out_proof_time:                         0.017
% 3.10/1.00  total_time:                             0.223
% 3.10/1.00  num_of_symbols:                         56
% 3.10/1.00  num_of_terms:                           4969
% 3.10/1.00  
% 3.10/1.00  ------ Preprocessing
% 3.10/1.00  
% 3.10/1.00  num_of_splits:                          0
% 3.10/1.00  num_of_split_atoms:                     0
% 3.10/1.00  num_of_reused_defs:                     0
% 3.10/1.00  num_eq_ax_congr_red:                    39
% 3.10/1.00  num_of_sem_filtered_clauses:            1
% 3.10/1.00  num_of_subtypes:                        0
% 3.10/1.00  monotx_restored_types:                  0
% 3.10/1.00  sat_num_of_epr_types:                   0
% 3.10/1.00  sat_num_of_non_cyclic_types:            0
% 3.10/1.00  sat_guarded_non_collapsed_types:        0
% 3.10/1.00  num_pure_diseq_elim:                    0
% 3.10/1.00  simp_replaced_by:                       0
% 3.10/1.00  res_preprocessed:                       170
% 3.10/1.00  prep_upred:                             0
% 3.10/1.00  prep_unflattend:                        98
% 3.10/1.00  smt_new_axioms:                         0
% 3.10/1.00  pred_elim_cands:                        5
% 3.10/1.00  pred_elim:                              2
% 3.10/1.00  pred_elim_cl:                           5
% 3.10/1.00  pred_elim_cycles:                       8
% 3.10/1.00  merged_defs:                            8
% 3.10/1.00  merged_defs_ncl:                        0
% 3.10/1.00  bin_hyper_res:                          8
% 3.10/1.00  prep_cycles:                            4
% 3.10/1.00  pred_elim_time:                         0.018
% 3.10/1.00  splitting_time:                         0.
% 3.10/1.00  sem_filter_time:                        0.
% 3.10/1.00  monotx_time:                            0.
% 3.10/1.00  subtype_inf_time:                       0.
% 3.10/1.00  
% 3.10/1.00  ------ Problem properties
% 3.10/1.00  
% 3.10/1.00  clauses:                                34
% 3.10/1.00  conjectures:                            3
% 3.10/1.00  epr:                                    6
% 3.10/1.00  horn:                                   27
% 3.10/1.00  ground:                                 6
% 3.10/1.00  unary:                                  7
% 3.10/1.00  binary:                                 11
% 3.10/1.00  lits:                                   80
% 3.10/1.00  lits_eq:                                18
% 3.10/1.00  fd_pure:                                0
% 3.10/1.00  fd_pseudo:                              0
% 3.10/1.00  fd_cond:                                1
% 3.10/1.00  fd_pseudo_cond:                         3
% 3.10/1.00  ac_symbols:                             0
% 3.10/1.00  
% 3.10/1.00  ------ Propositional Solver
% 3.10/1.00  
% 3.10/1.00  prop_solver_calls:                      28
% 3.10/1.00  prop_fast_solver_calls:                 1230
% 3.10/1.00  smt_solver_calls:                       0
% 3.10/1.00  smt_fast_solver_calls:                  0
% 3.10/1.00  prop_num_of_clauses:                    1916
% 3.10/1.00  prop_preprocess_simplified:             6906
% 3.10/1.00  prop_fo_subsumed:                       19
% 3.10/1.00  prop_solver_time:                       0.
% 3.10/1.00  smt_solver_time:                        0.
% 3.10/1.00  smt_fast_solver_time:                   0.
% 3.10/1.00  prop_fast_solver_time:                  0.
% 3.10/1.00  prop_unsat_core_time:                   0.
% 3.10/1.00  
% 3.10/1.00  ------ QBF
% 3.10/1.00  
% 3.10/1.00  qbf_q_res:                              0
% 3.10/1.00  qbf_num_tautologies:                    0
% 3.10/1.00  qbf_prep_cycles:                        0
% 3.10/1.00  
% 3.10/1.00  ------ BMC1
% 3.10/1.00  
% 3.10/1.00  bmc1_current_bound:                     -1
% 3.10/1.00  bmc1_last_solved_bound:                 -1
% 3.10/1.00  bmc1_unsat_core_size:                   -1
% 3.10/1.00  bmc1_unsat_core_parents_size:           -1
% 3.10/1.00  bmc1_merge_next_fun:                    0
% 3.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.10/1.00  
% 3.10/1.00  ------ Instantiation
% 3.10/1.00  
% 3.10/1.00  inst_num_of_clauses:                    630
% 3.10/1.00  inst_num_in_passive:                    71
% 3.10/1.00  inst_num_in_active:                     335
% 3.10/1.00  inst_num_in_unprocessed:                225
% 3.10/1.00  inst_num_of_loops:                      370
% 3.10/1.00  inst_num_of_learning_restarts:          0
% 3.10/1.00  inst_num_moves_active_passive:          32
% 3.10/1.00  inst_lit_activity:                      0
% 3.10/1.00  inst_lit_activity_moves:                0
% 3.10/1.00  inst_num_tautologies:                   0
% 3.10/1.00  inst_num_prop_implied:                  0
% 3.10/1.00  inst_num_existing_simplified:           0
% 3.10/1.00  inst_num_eq_res_simplified:             0
% 3.10/1.00  inst_num_child_elim:                    0
% 3.10/1.00  inst_num_of_dismatching_blockings:      104
% 3.10/1.00  inst_num_of_non_proper_insts:           522
% 3.10/1.00  inst_num_of_duplicates:                 0
% 3.10/1.00  inst_inst_num_from_inst_to_res:         0
% 3.10/1.00  inst_dismatching_checking_time:         0.
% 3.10/1.00  
% 3.10/1.00  ------ Resolution
% 3.10/1.00  
% 3.10/1.00  res_num_of_clauses:                     0
% 3.10/1.00  res_num_in_passive:                     0
% 3.10/1.00  res_num_in_active:                      0
% 3.10/1.00  res_num_of_loops:                       174
% 3.10/1.00  res_forward_subset_subsumed:            47
% 3.10/1.00  res_backward_subset_subsumed:           2
% 3.10/1.00  res_forward_subsumed:                   0
% 3.10/1.00  res_backward_subsumed:                  0
% 3.10/1.00  res_forward_subsumption_resolution:     1
% 3.10/1.00  res_backward_subsumption_resolution:    0
% 3.10/1.00  res_clause_to_clause_subsumption:       238
% 3.10/1.00  res_orphan_elimination:                 0
% 3.10/1.00  res_tautology_del:                      97
% 3.10/1.00  res_num_eq_res_simplified:              0
% 3.10/1.00  res_num_sel_changes:                    0
% 3.10/1.00  res_moves_from_active_to_pass:          0
% 3.10/1.00  
% 3.10/1.00  ------ Superposition
% 3.10/1.00  
% 3.10/1.00  sup_time_total:                         0.
% 3.10/1.00  sup_time_generating:                    0.
% 3.10/1.00  sup_time_sim_full:                      0.
% 3.10/1.00  sup_time_sim_immed:                     0.
% 3.10/1.00  
% 3.10/1.00  sup_num_of_clauses:                     107
% 3.10/1.00  sup_num_in_active:                      56
% 3.10/1.00  sup_num_in_passive:                     51
% 3.10/1.00  sup_num_of_loops:                       73
% 3.10/1.00  sup_fw_superposition:                   63
% 3.10/1.00  sup_bw_superposition:                   68
% 3.10/1.00  sup_immediate_simplified:               29
% 3.10/1.00  sup_given_eliminated:                   2
% 3.10/1.00  comparisons_done:                       0
% 3.10/1.00  comparisons_avoided:                    3
% 3.10/1.00  
% 3.10/1.00  ------ Simplifications
% 3.10/1.00  
% 3.10/1.00  
% 3.10/1.00  sim_fw_subset_subsumed:                 17
% 3.10/1.00  sim_bw_subset_subsumed:                 9
% 3.10/1.00  sim_fw_subsumed:                        6
% 3.10/1.00  sim_bw_subsumed:                        2
% 3.10/1.00  sim_fw_subsumption_res:                 2
% 3.10/1.00  sim_bw_subsumption_res:                 0
% 3.10/1.00  sim_tautology_del:                      4
% 3.10/1.00  sim_eq_tautology_del:                   3
% 3.10/1.00  sim_eq_res_simp:                        1
% 3.10/1.00  sim_fw_demodulated:                     6
% 3.10/1.00  sim_bw_demodulated:                     10
% 3.10/1.00  sim_light_normalised:                   0
% 3.10/1.00  sim_joinable_taut:                      0
% 3.10/1.00  sim_joinable_simp:                      0
% 3.10/1.00  sim_ac_normalised:                      0
% 3.10/1.00  sim_smt_subsumption:                    0
% 3.10/1.00  
%------------------------------------------------------------------------------
