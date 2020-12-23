%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:05 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  213 (1253 expanded)
%              Number of clauses        :  132 ( 445 expanded)
%              Number of leaves         :   22 ( 227 expanded)
%              Depth                    :   28
%              Number of atoms          :  621 (5281 expanded)
%              Number of equality atoms :  283 (1453 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f53,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK5,X4) != sK2
          | ~ m1_subset_1(X4,sK3) )
      & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ! [X4] :
        ( k1_funct_1(sK5,X4) != sK2
        | ~ m1_subset_1(X4,sK3) )
    & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f53])).

fof(f87,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) != sK2
      | ~ m1_subset_1(X4,sK3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f76])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2492,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2498,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3988,plain,
    ( m1_subset_1(sK1(X0,X1,X2),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(X2,X1)) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2492,c_2498])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_563,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_565,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_33])).

cnf(c_2482,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2486,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3632,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2482,c_2486])).

cnf(c_3799,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_565,c_3632])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2485,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3248,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2482,c_2485])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2483,plain,
    ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3502,plain,
    ( r2_hidden(sK2,k2_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3248,c_2483])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2487,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3392,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2482,c_2487])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2489,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3485,plain,
    ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3392,c_2489])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2491,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_20,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_421,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_422,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_2478,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_423,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_2718,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2719,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2718])).

cnf(c_2745,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | k1_funct_1(sK5,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2478,c_38,c_423,c_2719])).

cnf(c_2746,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2745])).

cnf(c_4192,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_2746])).

cnf(c_4629,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4192,c_38,c_2719])).

cnf(c_4630,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4629])).

cnf(c_4640,plain,
    ( k1_funct_1(sK5,sK1(X0,k1_relat_1(sK5),sK5)) = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3485,c_4630])).

cnf(c_5208,plain,
    ( k1_funct_1(sK5,sK1(sK2,k1_relat_1(sK5),sK5)) = sK2 ),
    inference(superposition,[status(thm)],[c_3502,c_4640])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | k1_funct_1(sK5,X0) != sK2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2484,plain,
    ( k1_funct_1(sK5,X0) != sK2
    | m1_subset_1(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5250,plain,
    ( m1_subset_1(sK1(sK2,k1_relat_1(sK5),sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5208,c_2484])).

cnf(c_5339,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK2,sK3,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3799,c_5250])).

cnf(c_5731,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2,k9_relat_1(sK5,sK3)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3988,c_5339])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_406,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_407,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_2479,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_408,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_2795,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2479,c_38,c_408,c_2719])).

cnf(c_2796,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_2795])).

cnf(c_5249,plain,
    ( r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5208,c_2796])).

cnf(c_5412,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3799,c_5249])).

cnf(c_5544,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3799,c_5412])).

cnf(c_5542,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top
    | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5))) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2492,c_5412])).

cnf(c_5556,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top
    | r2_hidden(sK2,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5542,c_3485])).

cnf(c_6082,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5544,c_38,c_2719,c_3502,c_5556])).

cnf(c_21,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_391,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_392,plain,
    ( r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_2480,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_393,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_2754,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2480,c_38,c_393,c_2719])).

cnf(c_2755,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_2754])).

cnf(c_6090,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK2,sK3,sK5),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6082,c_2755])).

cnf(c_6193,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3799,c_6090])).

cnf(c_6208,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6193,c_2498])).

cnf(c_6295,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5731,c_5339,c_6208])).

cnf(c_6307,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6295,c_2482])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_6309,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6307,c_5])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2494,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3026,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_2494])).

cnf(c_3201,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3026,c_2489])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2500,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_380,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_381,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_2481,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_4190,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_2481])).

cnf(c_97,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_99,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_110,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_111,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2023,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2721,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
    | X0 != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_2722,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2721])).

cnf(c_2724,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2722])).

cnf(c_2017,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2889,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_2890,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2889])).

cnf(c_5110,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4190,c_99,c_110,c_111,c_2724,c_2890])).

cnf(c_5117,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_5110])).

cnf(c_5822,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3201,c_5117])).

cnf(c_5829,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5822])).

cnf(c_2019,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2876,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X1)
    | k2_relset_1(sK3,sK4,sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_3475,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0)
    | ~ r1_tarski(k2_relat_1(sK5),X0)
    | k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2876])).

cnf(c_3476,plain,
    ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3475])).

cnf(c_3478,plain,
    ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
    | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3476])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3143,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(sK5,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3144,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(sK5,X1) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3143])).

cnf(c_3146,plain,
    ( v5_relat_1(sK5,k1_xboole_0) = iProver_top
    | v5_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3144])).

cnf(c_2999,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_3002,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2999])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2822,plain,
    ( ~ v5_relat_1(sK5,X0)
    | r1_tarski(k2_relat_1(sK5),X0)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2836,plain,
    ( v5_relat_1(sK5,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2822])).

cnf(c_2838,plain,
    ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2836])).

cnf(c_2775,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2731,plain,
    ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),X0)
    | r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2732,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
    | r2_hidden(sK2,X0) = iProver_top
    | r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2731])).

cnf(c_2734,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_xboole_0) != iProver_top
    | r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) != iProver_top
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2732])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_103,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_105,plain,
    ( v5_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_39,plain,
    ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6309,c_5829,c_3478,c_3146,c_3002,c_2890,c_2838,c_2775,c_2734,c_2724,c_2719,c_111,c_110,c_105,c_99,c_39,c_38,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/0.99  
% 3.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/0.99  
% 3.16/0.99  ------  iProver source info
% 3.16/0.99  
% 3.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/0.99  git: non_committed_changes: false
% 3.16/0.99  git: last_make_outside_of_git: false
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/0.99  
% 3.16/0.99  ------ General Options
% 3.16/0.99  
% 3.16/0.99  --fof                                   false
% 3.16/0.99  --time_out_real                         305.
% 3.16/0.99  --time_out_virtual                      -1.
% 3.16/0.99  --symbol_type_check                     false
% 3.16/0.99  --clausify_out                          false
% 3.16/0.99  --sig_cnt_out                           false
% 3.16/0.99  --trig_cnt_out                          false
% 3.16/0.99  --trig_cnt_out_tolerance                1.
% 3.16/0.99  --trig_cnt_out_sk_spl                   false
% 3.16/0.99  --abstr_cl_out                          false
% 3.16/0.99  
% 3.16/0.99  ------ Global Options
% 3.16/0.99  
% 3.16/0.99  --schedule                              default
% 3.16/0.99  --add_important_lit                     false
% 3.16/0.99  --prop_solver_per_cl                    1000
% 3.16/0.99  --min_unsat_core                        false
% 3.16/0.99  --soft_assumptions                      false
% 3.16/0.99  --soft_lemma_size                       3
% 3.16/0.99  --prop_impl_unit_size                   0
% 3.16/0.99  --prop_impl_unit                        []
% 3.16/0.99  --share_sel_clauses                     true
% 3.16/0.99  --reset_solvers                         false
% 3.16/0.99  --bc_imp_inh                            [conj_cone]
% 3.16/0.99  --conj_cone_tolerance                   3.
% 3.16/0.99  --extra_neg_conj                        none
% 3.16/0.99  --large_theory_mode                     true
% 3.16/0.99  --prolific_symb_bound                   200
% 3.16/0.99  --lt_threshold                          2000
% 3.16/0.99  --clause_weak_htbl                      true
% 3.16/0.99  --gc_record_bc_elim                     false
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing Options
% 3.16/0.99  
% 3.16/0.99  --preprocessing_flag                    true
% 3.16/0.99  --time_out_prep_mult                    0.1
% 3.16/0.99  --splitting_mode                        input
% 3.16/0.99  --splitting_grd                         true
% 3.16/0.99  --splitting_cvd                         false
% 3.16/0.99  --splitting_cvd_svl                     false
% 3.16/0.99  --splitting_nvd                         32
% 3.16/0.99  --sub_typing                            true
% 3.16/0.99  --prep_gs_sim                           true
% 3.16/0.99  --prep_unflatten                        true
% 3.16/0.99  --prep_res_sim                          true
% 3.16/0.99  --prep_upred                            true
% 3.16/0.99  --prep_sem_filter                       exhaustive
% 3.16/0.99  --prep_sem_filter_out                   false
% 3.16/0.99  --pred_elim                             true
% 3.16/0.99  --res_sim_input                         true
% 3.16/0.99  --eq_ax_congr_red                       true
% 3.16/0.99  --pure_diseq_elim                       true
% 3.16/0.99  --brand_transform                       false
% 3.16/0.99  --non_eq_to_eq                          false
% 3.16/0.99  --prep_def_merge                        true
% 3.16/0.99  --prep_def_merge_prop_impl              false
% 3.16/0.99  --prep_def_merge_mbd                    true
% 3.16/0.99  --prep_def_merge_tr_red                 false
% 3.16/0.99  --prep_def_merge_tr_cl                  false
% 3.16/0.99  --smt_preprocessing                     true
% 3.16/0.99  --smt_ac_axioms                         fast
% 3.16/0.99  --preprocessed_out                      false
% 3.16/0.99  --preprocessed_stats                    false
% 3.16/0.99  
% 3.16/0.99  ------ Abstraction refinement Options
% 3.16/0.99  
% 3.16/0.99  --abstr_ref                             []
% 3.16/0.99  --abstr_ref_prep                        false
% 3.16/0.99  --abstr_ref_until_sat                   false
% 3.16/0.99  --abstr_ref_sig_restrict                funpre
% 3.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/0.99  --abstr_ref_under                       []
% 3.16/0.99  
% 3.16/0.99  ------ SAT Options
% 3.16/0.99  
% 3.16/0.99  --sat_mode                              false
% 3.16/0.99  --sat_fm_restart_options                ""
% 3.16/0.99  --sat_gr_def                            false
% 3.16/0.99  --sat_epr_types                         true
% 3.16/0.99  --sat_non_cyclic_types                  false
% 3.16/0.99  --sat_finite_models                     false
% 3.16/0.99  --sat_fm_lemmas                         false
% 3.16/0.99  --sat_fm_prep                           false
% 3.16/0.99  --sat_fm_uc_incr                        true
% 3.16/0.99  --sat_out_model                         small
% 3.16/0.99  --sat_out_clauses                       false
% 3.16/0.99  
% 3.16/0.99  ------ QBF Options
% 3.16/0.99  
% 3.16/0.99  --qbf_mode                              false
% 3.16/0.99  --qbf_elim_univ                         false
% 3.16/0.99  --qbf_dom_inst                          none
% 3.16/0.99  --qbf_dom_pre_inst                      false
% 3.16/0.99  --qbf_sk_in                             false
% 3.16/0.99  --qbf_pred_elim                         true
% 3.16/0.99  --qbf_split                             512
% 3.16/0.99  
% 3.16/0.99  ------ BMC1 Options
% 3.16/0.99  
% 3.16/0.99  --bmc1_incremental                      false
% 3.16/0.99  --bmc1_axioms                           reachable_all
% 3.16/0.99  --bmc1_min_bound                        0
% 3.16/0.99  --bmc1_max_bound                        -1
% 3.16/0.99  --bmc1_max_bound_default                -1
% 3.16/0.99  --bmc1_symbol_reachability              true
% 3.16/0.99  --bmc1_property_lemmas                  false
% 3.16/0.99  --bmc1_k_induction                      false
% 3.16/0.99  --bmc1_non_equiv_states                 false
% 3.16/0.99  --bmc1_deadlock                         false
% 3.16/0.99  --bmc1_ucm                              false
% 3.16/0.99  --bmc1_add_unsat_core                   none
% 3.16/0.99  --bmc1_unsat_core_children              false
% 3.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/0.99  --bmc1_out_stat                         full
% 3.16/0.99  --bmc1_ground_init                      false
% 3.16/0.99  --bmc1_pre_inst_next_state              false
% 3.16/0.99  --bmc1_pre_inst_state                   false
% 3.16/0.99  --bmc1_pre_inst_reach_state             false
% 3.16/0.99  --bmc1_out_unsat_core                   false
% 3.16/0.99  --bmc1_aig_witness_out                  false
% 3.16/0.99  --bmc1_verbose                          false
% 3.16/0.99  --bmc1_dump_clauses_tptp                false
% 3.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.16/0.99  --bmc1_dump_file                        -
% 3.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.16/0.99  --bmc1_ucm_extend_mode                  1
% 3.16/0.99  --bmc1_ucm_init_mode                    2
% 3.16/0.99  --bmc1_ucm_cone_mode                    none
% 3.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.16/0.99  --bmc1_ucm_relax_model                  4
% 3.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/0.99  --bmc1_ucm_layered_model                none
% 3.16/0.99  --bmc1_ucm_max_lemma_size               10
% 3.16/0.99  
% 3.16/0.99  ------ AIG Options
% 3.16/0.99  
% 3.16/0.99  --aig_mode                              false
% 3.16/0.99  
% 3.16/0.99  ------ Instantiation Options
% 3.16/0.99  
% 3.16/0.99  --instantiation_flag                    true
% 3.16/0.99  --inst_sos_flag                         false
% 3.16/0.99  --inst_sos_phase                        true
% 3.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/0.99  --inst_lit_sel_side                     num_symb
% 3.16/0.99  --inst_solver_per_active                1400
% 3.16/0.99  --inst_solver_calls_frac                1.
% 3.16/0.99  --inst_passive_queue_type               priority_queues
% 3.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/0.99  --inst_passive_queues_freq              [25;2]
% 3.16/0.99  --inst_dismatching                      true
% 3.16/0.99  --inst_eager_unprocessed_to_passive     true
% 3.16/0.99  --inst_prop_sim_given                   true
% 3.16/0.99  --inst_prop_sim_new                     false
% 3.16/0.99  --inst_subs_new                         false
% 3.16/0.99  --inst_eq_res_simp                      false
% 3.16/0.99  --inst_subs_given                       false
% 3.16/0.99  --inst_orphan_elimination               true
% 3.16/0.99  --inst_learning_loop_flag               true
% 3.16/0.99  --inst_learning_start                   3000
% 3.16/0.99  --inst_learning_factor                  2
% 3.16/0.99  --inst_start_prop_sim_after_learn       3
% 3.16/0.99  --inst_sel_renew                        solver
% 3.16/0.99  --inst_lit_activity_flag                true
% 3.16/0.99  --inst_restr_to_given                   false
% 3.16/0.99  --inst_activity_threshold               500
% 3.16/0.99  --inst_out_proof                        true
% 3.16/0.99  
% 3.16/0.99  ------ Resolution Options
% 3.16/0.99  
% 3.16/0.99  --resolution_flag                       true
% 3.16/0.99  --res_lit_sel                           adaptive
% 3.16/0.99  --res_lit_sel_side                      none
% 3.16/0.99  --res_ordering                          kbo
% 3.16/0.99  --res_to_prop_solver                    active
% 3.16/0.99  --res_prop_simpl_new                    false
% 3.16/0.99  --res_prop_simpl_given                  true
% 3.16/0.99  --res_passive_queue_type                priority_queues
% 3.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/0.99  --res_passive_queues_freq               [15;5]
% 3.16/0.99  --res_forward_subs                      full
% 3.16/0.99  --res_backward_subs                     full
% 3.16/0.99  --res_forward_subs_resolution           true
% 3.16/0.99  --res_backward_subs_resolution          true
% 3.16/0.99  --res_orphan_elimination                true
% 3.16/0.99  --res_time_limit                        2.
% 3.16/0.99  --res_out_proof                         true
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Options
% 3.16/0.99  
% 3.16/0.99  --superposition_flag                    true
% 3.16/0.99  --sup_passive_queue_type                priority_queues
% 3.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.16/0.99  --demod_completeness_check              fast
% 3.16/0.99  --demod_use_ground                      true
% 3.16/0.99  --sup_to_prop_solver                    passive
% 3.16/0.99  --sup_prop_simpl_new                    true
% 3.16/0.99  --sup_prop_simpl_given                  true
% 3.16/0.99  --sup_fun_splitting                     false
% 3.16/0.99  --sup_smt_interval                      50000
% 3.16/0.99  
% 3.16/0.99  ------ Superposition Simplification Setup
% 3.16/0.99  
% 3.16/0.99  --sup_indices_passive                   []
% 3.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_full_bw                           [BwDemod]
% 3.16/0.99  --sup_immed_triv                        [TrivRules]
% 3.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_immed_bw_main                     []
% 3.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/0.99  
% 3.16/0.99  ------ Combination Options
% 3.16/0.99  
% 3.16/0.99  --comb_res_mult                         3
% 3.16/0.99  --comb_sup_mult                         2
% 3.16/0.99  --comb_inst_mult                        10
% 3.16/0.99  
% 3.16/0.99  ------ Debug Options
% 3.16/0.99  
% 3.16/0.99  --dbg_backtrace                         false
% 3.16/0.99  --dbg_dump_prop_clauses                 false
% 3.16/0.99  --dbg_dump_prop_clauses_file            -
% 3.16/0.99  --dbg_out_stat                          false
% 3.16/0.99  ------ Parsing...
% 3.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/0.99  
% 3.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/0.99  ------ Proving...
% 3.16/0.99  ------ Problem Properties 
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  clauses                                 30
% 3.16/0.99  conjectures                             3
% 3.16/0.99  EPR                                     3
% 3.16/0.99  Horn                                    26
% 3.16/0.99  unary                                   6
% 3.16/0.99  binary                                  9
% 3.16/0.99  lits                                    74
% 3.16/0.99  lits eq                                 17
% 3.16/0.99  fd_pure                                 0
% 3.16/0.99  fd_pseudo                               0
% 3.16/0.99  fd_cond                                 1
% 3.16/0.99  fd_pseudo_cond                          1
% 3.16/0.99  AC symbols                              0
% 3.16/0.99  
% 3.16/0.99  ------ Schedule dynamic 5 is on 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/0.99  
% 3.16/0.99  
% 3.16/0.99  ------ 
% 3.16/0.99  Current options:
% 3.16/0.99  ------ 
% 3.16/0.99  
% 3.16/0.99  ------ Input Options
% 3.16/0.99  
% 3.16/0.99  --out_options                           all
% 3.16/0.99  --tptp_safe_out                         true
% 3.16/0.99  --problem_path                          ""
% 3.16/0.99  --include_path                          ""
% 3.16/0.99  --clausifier                            res/vclausify_rel
% 3.16/0.99  --clausifier_options                    --mode clausify
% 3.16/0.99  --stdin                                 false
% 3.16/0.99  --stats_out                             all
% 3.16/1.00  
% 3.16/1.00  ------ General Options
% 3.16/1.00  
% 3.16/1.00  --fof                                   false
% 3.16/1.00  --time_out_real                         305.
% 3.16/1.00  --time_out_virtual                      -1.
% 3.16/1.00  --symbol_type_check                     false
% 3.16/1.00  --clausify_out                          false
% 3.16/1.00  --sig_cnt_out                           false
% 3.16/1.00  --trig_cnt_out                          false
% 3.16/1.00  --trig_cnt_out_tolerance                1.
% 3.16/1.00  --trig_cnt_out_sk_spl                   false
% 3.16/1.00  --abstr_cl_out                          false
% 3.16/1.00  
% 3.16/1.00  ------ Global Options
% 3.16/1.00  
% 3.16/1.00  --schedule                              default
% 3.16/1.00  --add_important_lit                     false
% 3.16/1.00  --prop_solver_per_cl                    1000
% 3.16/1.00  --min_unsat_core                        false
% 3.16/1.00  --soft_assumptions                      false
% 3.16/1.00  --soft_lemma_size                       3
% 3.16/1.00  --prop_impl_unit_size                   0
% 3.16/1.00  --prop_impl_unit                        []
% 3.16/1.00  --share_sel_clauses                     true
% 3.16/1.00  --reset_solvers                         false
% 3.16/1.00  --bc_imp_inh                            [conj_cone]
% 3.16/1.00  --conj_cone_tolerance                   3.
% 3.16/1.00  --extra_neg_conj                        none
% 3.16/1.00  --large_theory_mode                     true
% 3.16/1.00  --prolific_symb_bound                   200
% 3.16/1.00  --lt_threshold                          2000
% 3.16/1.00  --clause_weak_htbl                      true
% 3.16/1.00  --gc_record_bc_elim                     false
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing Options
% 3.16/1.00  
% 3.16/1.00  --preprocessing_flag                    true
% 3.16/1.00  --time_out_prep_mult                    0.1
% 3.16/1.00  --splitting_mode                        input
% 3.16/1.00  --splitting_grd                         true
% 3.16/1.00  --splitting_cvd                         false
% 3.16/1.00  --splitting_cvd_svl                     false
% 3.16/1.00  --splitting_nvd                         32
% 3.16/1.00  --sub_typing                            true
% 3.16/1.00  --prep_gs_sim                           true
% 3.16/1.00  --prep_unflatten                        true
% 3.16/1.00  --prep_res_sim                          true
% 3.16/1.00  --prep_upred                            true
% 3.16/1.00  --prep_sem_filter                       exhaustive
% 3.16/1.00  --prep_sem_filter_out                   false
% 3.16/1.00  --pred_elim                             true
% 3.16/1.00  --res_sim_input                         true
% 3.16/1.00  --eq_ax_congr_red                       true
% 3.16/1.00  --pure_diseq_elim                       true
% 3.16/1.00  --brand_transform                       false
% 3.16/1.00  --non_eq_to_eq                          false
% 3.16/1.00  --prep_def_merge                        true
% 3.16/1.00  --prep_def_merge_prop_impl              false
% 3.16/1.00  --prep_def_merge_mbd                    true
% 3.16/1.00  --prep_def_merge_tr_red                 false
% 3.16/1.00  --prep_def_merge_tr_cl                  false
% 3.16/1.00  --smt_preprocessing                     true
% 3.16/1.00  --smt_ac_axioms                         fast
% 3.16/1.00  --preprocessed_out                      false
% 3.16/1.00  --preprocessed_stats                    false
% 3.16/1.00  
% 3.16/1.00  ------ Abstraction refinement Options
% 3.16/1.00  
% 3.16/1.00  --abstr_ref                             []
% 3.16/1.00  --abstr_ref_prep                        false
% 3.16/1.00  --abstr_ref_until_sat                   false
% 3.16/1.00  --abstr_ref_sig_restrict                funpre
% 3.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.00  --abstr_ref_under                       []
% 3.16/1.00  
% 3.16/1.00  ------ SAT Options
% 3.16/1.00  
% 3.16/1.00  --sat_mode                              false
% 3.16/1.00  --sat_fm_restart_options                ""
% 3.16/1.00  --sat_gr_def                            false
% 3.16/1.00  --sat_epr_types                         true
% 3.16/1.00  --sat_non_cyclic_types                  false
% 3.16/1.00  --sat_finite_models                     false
% 3.16/1.00  --sat_fm_lemmas                         false
% 3.16/1.00  --sat_fm_prep                           false
% 3.16/1.00  --sat_fm_uc_incr                        true
% 3.16/1.00  --sat_out_model                         small
% 3.16/1.00  --sat_out_clauses                       false
% 3.16/1.00  
% 3.16/1.00  ------ QBF Options
% 3.16/1.00  
% 3.16/1.00  --qbf_mode                              false
% 3.16/1.00  --qbf_elim_univ                         false
% 3.16/1.00  --qbf_dom_inst                          none
% 3.16/1.00  --qbf_dom_pre_inst                      false
% 3.16/1.00  --qbf_sk_in                             false
% 3.16/1.00  --qbf_pred_elim                         true
% 3.16/1.00  --qbf_split                             512
% 3.16/1.00  
% 3.16/1.00  ------ BMC1 Options
% 3.16/1.00  
% 3.16/1.00  --bmc1_incremental                      false
% 3.16/1.00  --bmc1_axioms                           reachable_all
% 3.16/1.00  --bmc1_min_bound                        0
% 3.16/1.00  --bmc1_max_bound                        -1
% 3.16/1.00  --bmc1_max_bound_default                -1
% 3.16/1.00  --bmc1_symbol_reachability              true
% 3.16/1.00  --bmc1_property_lemmas                  false
% 3.16/1.00  --bmc1_k_induction                      false
% 3.16/1.00  --bmc1_non_equiv_states                 false
% 3.16/1.00  --bmc1_deadlock                         false
% 3.16/1.00  --bmc1_ucm                              false
% 3.16/1.00  --bmc1_add_unsat_core                   none
% 3.16/1.00  --bmc1_unsat_core_children              false
% 3.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.00  --bmc1_out_stat                         full
% 3.16/1.00  --bmc1_ground_init                      false
% 3.16/1.00  --bmc1_pre_inst_next_state              false
% 3.16/1.00  --bmc1_pre_inst_state                   false
% 3.16/1.00  --bmc1_pre_inst_reach_state             false
% 3.16/1.00  --bmc1_out_unsat_core                   false
% 3.16/1.00  --bmc1_aig_witness_out                  false
% 3.16/1.00  --bmc1_verbose                          false
% 3.16/1.00  --bmc1_dump_clauses_tptp                false
% 3.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.00  --bmc1_dump_file                        -
% 3.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.00  --bmc1_ucm_extend_mode                  1
% 3.16/1.00  --bmc1_ucm_init_mode                    2
% 3.16/1.00  --bmc1_ucm_cone_mode                    none
% 3.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.00  --bmc1_ucm_relax_model                  4
% 3.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.00  --bmc1_ucm_layered_model                none
% 3.16/1.00  --bmc1_ucm_max_lemma_size               10
% 3.16/1.00  
% 3.16/1.00  ------ AIG Options
% 3.16/1.00  
% 3.16/1.00  --aig_mode                              false
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation Options
% 3.16/1.00  
% 3.16/1.00  --instantiation_flag                    true
% 3.16/1.00  --inst_sos_flag                         false
% 3.16/1.00  --inst_sos_phase                        true
% 3.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.00  --inst_lit_sel_side                     none
% 3.16/1.00  --inst_solver_per_active                1400
% 3.16/1.00  --inst_solver_calls_frac                1.
% 3.16/1.00  --inst_passive_queue_type               priority_queues
% 3.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.00  --inst_passive_queues_freq              [25;2]
% 3.16/1.00  --inst_dismatching                      true
% 3.16/1.00  --inst_eager_unprocessed_to_passive     true
% 3.16/1.00  --inst_prop_sim_given                   true
% 3.16/1.00  --inst_prop_sim_new                     false
% 3.16/1.00  --inst_subs_new                         false
% 3.16/1.00  --inst_eq_res_simp                      false
% 3.16/1.00  --inst_subs_given                       false
% 3.16/1.00  --inst_orphan_elimination               true
% 3.16/1.00  --inst_learning_loop_flag               true
% 3.16/1.00  --inst_learning_start                   3000
% 3.16/1.00  --inst_learning_factor                  2
% 3.16/1.00  --inst_start_prop_sim_after_learn       3
% 3.16/1.00  --inst_sel_renew                        solver
% 3.16/1.00  --inst_lit_activity_flag                true
% 3.16/1.00  --inst_restr_to_given                   false
% 3.16/1.00  --inst_activity_threshold               500
% 3.16/1.00  --inst_out_proof                        true
% 3.16/1.00  
% 3.16/1.00  ------ Resolution Options
% 3.16/1.00  
% 3.16/1.00  --resolution_flag                       false
% 3.16/1.00  --res_lit_sel                           adaptive
% 3.16/1.00  --res_lit_sel_side                      none
% 3.16/1.00  --res_ordering                          kbo
% 3.16/1.00  --res_to_prop_solver                    active
% 3.16/1.00  --res_prop_simpl_new                    false
% 3.16/1.00  --res_prop_simpl_given                  true
% 3.16/1.00  --res_passive_queue_type                priority_queues
% 3.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.00  --res_passive_queues_freq               [15;5]
% 3.16/1.00  --res_forward_subs                      full
% 3.16/1.00  --res_backward_subs                     full
% 3.16/1.00  --res_forward_subs_resolution           true
% 3.16/1.00  --res_backward_subs_resolution          true
% 3.16/1.00  --res_orphan_elimination                true
% 3.16/1.00  --res_time_limit                        2.
% 3.16/1.00  --res_out_proof                         true
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Options
% 3.16/1.00  
% 3.16/1.00  --superposition_flag                    true
% 3.16/1.00  --sup_passive_queue_type                priority_queues
% 3.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.00  --demod_completeness_check              fast
% 3.16/1.00  --demod_use_ground                      true
% 3.16/1.00  --sup_to_prop_solver                    passive
% 3.16/1.00  --sup_prop_simpl_new                    true
% 3.16/1.00  --sup_prop_simpl_given                  true
% 3.16/1.00  --sup_fun_splitting                     false
% 3.16/1.00  --sup_smt_interval                      50000
% 3.16/1.00  
% 3.16/1.00  ------ Superposition Simplification Setup
% 3.16/1.00  
% 3.16/1.00  --sup_indices_passive                   []
% 3.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_full_bw                           [BwDemod]
% 3.16/1.00  --sup_immed_triv                        [TrivRules]
% 3.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_immed_bw_main                     []
% 3.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.00  
% 3.16/1.00  ------ Combination Options
% 3.16/1.00  
% 3.16/1.00  --comb_res_mult                         3
% 3.16/1.00  --comb_sup_mult                         2
% 3.16/1.00  --comb_inst_mult                        10
% 3.16/1.00  
% 3.16/1.00  ------ Debug Options
% 3.16/1.00  
% 3.16/1.00  --dbg_backtrace                         false
% 3.16/1.00  --dbg_dump_prop_clauses                 false
% 3.16/1.00  --dbg_dump_prop_clauses_file            -
% 3.16/1.00  --dbg_out_stat                          false
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  ------ Proving...
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS status Theorem for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  fof(f9,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f26,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(ennf_transformation,[],[f9])).
% 3.16/1.00  
% 3.16/1.00  fof(f46,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(nnf_transformation,[],[f26])).
% 3.16/1.00  
% 3.16/1.00  fof(f47,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(rectify,[],[f46])).
% 3.16/1.00  
% 3.16/1.00  fof(f48,plain,(
% 3.16/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f49,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.16/1.00  
% 3.16/1.00  fof(f70,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f49])).
% 3.16/1.00  
% 3.16/1.00  fof(f5,axiom,(
% 3.16/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f22,plain,(
% 3.16/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f5])).
% 3.16/1.00  
% 3.16/1.00  fof(f63,plain,(
% 3.16/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f22])).
% 3.16/1.00  
% 3.16/1.00  fof(f16,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f35,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f16])).
% 3.16/1.00  
% 3.16/1.00  fof(f36,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(flattening,[],[f35])).
% 3.16/1.00  
% 3.16/1.00  fof(f52,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(nnf_transformation,[],[f36])).
% 3.16/1.00  
% 3.16/1.00  fof(f80,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f52])).
% 3.16/1.00  
% 3.16/1.00  fof(f17,conjecture,(
% 3.16/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f18,negated_conjecture,(
% 3.16/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 3.16/1.00    inference(negated_conjecture,[],[f17])).
% 3.16/1.00  
% 3.16/1.00  fof(f37,plain,(
% 3.16/1.00    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 3.16/1.00    inference(ennf_transformation,[],[f18])).
% 3.16/1.00  
% 3.16/1.00  fof(f38,plain,(
% 3.16/1.00    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 3.16/1.00    inference(flattening,[],[f37])).
% 3.16/1.00  
% 3.16/1.00  fof(f53,plain,(
% 3.16/1.00    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK5,X4) != sK2 | ~m1_subset_1(X4,sK3)) & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f54,plain,(
% 3.16/1.00    ! [X4] : (k1_funct_1(sK5,X4) != sK2 | ~m1_subset_1(X4,sK3)) & r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f38,f53])).
% 3.16/1.00  
% 3.16/1.00  fof(f87,plain,(
% 3.16/1.00    v1_funct_2(sK5,sK3,sK4)),
% 3.16/1.00    inference(cnf_transformation,[],[f54])).
% 3.16/1.00  
% 3.16/1.00  fof(f88,plain,(
% 3.16/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.16/1.00    inference(cnf_transformation,[],[f54])).
% 3.16/1.00  
% 3.16/1.00  fof(f14,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f33,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f14])).
% 3.16/1.00  
% 3.16/1.00  fof(f78,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f33])).
% 3.16/1.00  
% 3.16/1.00  fof(f15,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f34,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f15])).
% 3.16/1.00  
% 3.16/1.00  fof(f79,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f34])).
% 3.16/1.00  
% 3.16/1.00  fof(f89,plain,(
% 3.16/1.00    r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5))),
% 3.16/1.00    inference(cnf_transformation,[],[f54])).
% 3.16/1.00  
% 3.16/1.00  fof(f13,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f32,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.00    inference(ennf_transformation,[],[f13])).
% 3.16/1.00  
% 3.16/1.00  fof(f77,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f32])).
% 3.16/1.00  
% 3.16/1.00  fof(f10,axiom,(
% 3.16/1.00    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f27,plain,(
% 3.16/1.00    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.16/1.00    inference(ennf_transformation,[],[f10])).
% 3.16/1.00  
% 3.16/1.00  fof(f72,plain,(
% 3.16/1.00    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f27])).
% 3.16/1.00  
% 3.16/1.00  fof(f69,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f49])).
% 3.16/1.00  
% 3.16/1.00  fof(f12,axiom,(
% 3.16/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f30,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.16/1.00    inference(ennf_transformation,[],[f12])).
% 3.16/1.00  
% 3.16/1.00  fof(f31,plain,(
% 3.16/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(flattening,[],[f30])).
% 3.16/1.00  
% 3.16/1.00  fof(f50,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(nnf_transformation,[],[f31])).
% 3.16/1.00  
% 3.16/1.00  fof(f51,plain,(
% 3.16/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.16/1.00    inference(flattening,[],[f50])).
% 3.16/1.00  
% 3.16/1.00  fof(f75,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f51])).
% 3.16/1.00  
% 3.16/1.00  fof(f86,plain,(
% 3.16/1.00    v1_funct_1(sK5)),
% 3.16/1.00    inference(cnf_transformation,[],[f54])).
% 3.16/1.00  
% 3.16/1.00  fof(f90,plain,(
% 3.16/1.00    ( ! [X4] : (k1_funct_1(sK5,X4) != sK2 | ~m1_subset_1(X4,sK3)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f54])).
% 3.16/1.00  
% 3.16/1.00  fof(f76,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f51])).
% 3.16/1.00  
% 3.16/1.00  fof(f93,plain,(
% 3.16/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(equality_resolution,[],[f76])).
% 3.16/1.00  
% 3.16/1.00  fof(f74,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f51])).
% 3.16/1.00  
% 3.16/1.00  fof(f4,axiom,(
% 3.16/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f43,plain,(
% 3.16/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.16/1.00    inference(nnf_transformation,[],[f4])).
% 3.16/1.00  
% 3.16/1.00  fof(f44,plain,(
% 3.16/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.16/1.00    inference(flattening,[],[f43])).
% 3.16/1.00  
% 3.16/1.00  fof(f62,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.16/1.00    inference(cnf_transformation,[],[f44])).
% 3.16/1.00  
% 3.16/1.00  fof(f91,plain,(
% 3.16/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.16/1.00    inference(equality_resolution,[],[f62])).
% 3.16/1.00  
% 3.16/1.00  fof(f8,axiom,(
% 3.16/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f67,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.16/1.00    inference(cnf_transformation,[],[f8])).
% 3.16/1.00  
% 3.16/1.00  fof(f2,axiom,(
% 3.16/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f21,plain,(
% 3.16/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.16/1.00    inference(ennf_transformation,[],[f2])).
% 3.16/1.00  
% 3.16/1.00  fof(f39,plain,(
% 3.16/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/1.00    inference(nnf_transformation,[],[f21])).
% 3.16/1.00  
% 3.16/1.00  fof(f40,plain,(
% 3.16/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/1.00    inference(rectify,[],[f39])).
% 3.16/1.00  
% 3.16/1.00  fof(f41,plain,(
% 3.16/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.16/1.00    introduced(choice_axiom,[])).
% 3.16/1.00  
% 3.16/1.00  fof(f42,plain,(
% 3.16/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.16/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.16/1.00  
% 3.16/1.00  fof(f57,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f42])).
% 3.16/1.00  
% 3.16/1.00  fof(f1,axiom,(
% 3.16/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f19,plain,(
% 3.16/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.16/1.00    inference(unused_predicate_definition_removal,[],[f1])).
% 3.16/1.00  
% 3.16/1.00  fof(f20,plain,(
% 3.16/1.00    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.16/1.00    inference(ennf_transformation,[],[f19])).
% 3.16/1.00  
% 3.16/1.00  fof(f55,plain,(
% 3.16/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f20])).
% 3.16/1.00  
% 3.16/1.00  fof(f3,axiom,(
% 3.16/1.00    v1_xboole_0(k1_xboole_0)),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f59,plain,(
% 3.16/1.00    v1_xboole_0(k1_xboole_0)),
% 3.16/1.00    inference(cnf_transformation,[],[f3])).
% 3.16/1.00  
% 3.16/1.00  fof(f60,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f44])).
% 3.16/1.00  
% 3.16/1.00  fof(f61,plain,(
% 3.16/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.16/1.00    inference(cnf_transformation,[],[f44])).
% 3.16/1.00  
% 3.16/1.00  fof(f92,plain,(
% 3.16/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.16/1.00    inference(equality_resolution,[],[f61])).
% 3.16/1.00  
% 3.16/1.00  fof(f6,axiom,(
% 3.16/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f23,plain,(
% 3.16/1.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/1.00    inference(ennf_transformation,[],[f6])).
% 3.16/1.00  
% 3.16/1.00  fof(f24,plain,(
% 3.16/1.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(flattening,[],[f23])).
% 3.16/1.00  
% 3.16/1.00  fof(f64,plain,(
% 3.16/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f24])).
% 3.16/1.00  
% 3.16/1.00  fof(f7,axiom,(
% 3.16/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.16/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.16/1.00  
% 3.16/1.00  fof(f25,plain,(
% 3.16/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(ennf_transformation,[],[f7])).
% 3.16/1.00  
% 3.16/1.00  fof(f45,plain,(
% 3.16/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.16/1.00    inference(nnf_transformation,[],[f25])).
% 3.16/1.00  
% 3.16/1.00  fof(f65,plain,(
% 3.16/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f45])).
% 3.16/1.00  
% 3.16/1.00  fof(f56,plain,(
% 3.16/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f42])).
% 3.16/1.00  
% 3.16/1.00  fof(f66,plain,(
% 3.16/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.16/1.00    inference(cnf_transformation,[],[f45])).
% 3.16/1.00  
% 3.16/1.00  cnf(c_14,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.16/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.16/1.00      | ~ v1_relat_1(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2492,plain,
% 3.16/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.16/1.00      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 3.16/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_8,plain,
% 3.16/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2498,plain,
% 3.16/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.16/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3988,plain,
% 3.16/1.00      ( m1_subset_1(sK1(X0,X1,X2),X1) = iProver_top
% 3.16/1.00      | r2_hidden(X0,k9_relat_1(X2,X1)) != iProver_top
% 3.16/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2492,c_2498]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_30,plain,
% 3.16/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.16/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.16/1.00      | k1_xboole_0 = X2 ),
% 3.16/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_34,negated_conjecture,
% 3.16/1.00      ( v1_funct_2(sK5,sK3,sK4) ),
% 3.16/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_562,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.16/1.00      | sK4 != X2
% 3.16/1.00      | sK3 != X1
% 3.16/1.00      | sK5 != X0
% 3.16/1.00      | k1_xboole_0 = X2 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_563,plain,
% 3.16/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.16/1.00      | k1_relset_1(sK3,sK4,sK5) = sK3
% 3.16/1.00      | k1_xboole_0 = sK4 ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_562]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_33,negated_conjecture,
% 3.16/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.16/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_565,plain,
% 3.16/1.00      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_563,c_33]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2482,plain,
% 3.16/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_23,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2486,plain,
% 3.16/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3632,plain,
% 3.16/1.00      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2482,c_2486]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3799,plain,
% 3.16/1.00      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_565,c_3632]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_24,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2485,plain,
% 3.16/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.16/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3248,plain,
% 3.16/1.00      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2482,c_2485]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_32,negated_conjecture,
% 3.16/1.00      ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2483,plain,
% 3.16/1.00      ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3502,plain,
% 3.16/1.00      ( r2_hidden(sK2,k2_relat_1(sK5)) = iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_3248,c_2483]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_22,plain,
% 3.16/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.00      | v1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2487,plain,
% 3.16/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3392,plain,
% 3.16/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2482,c_2487]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_17,plain,
% 3.16/1.00      ( ~ v1_relat_1(X0)
% 3.16/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2489,plain,
% 3.16/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3485,plain,
% 3.16/1.00      ( k9_relat_1(sK5,k1_relat_1(sK5)) = k2_relat_1(sK5) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3392,c_2489]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_15,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.16/1.00      | ~ v1_relat_1(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2491,plain,
% 3.16/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.16/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_20,plain,
% 3.16/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.16/1.00      | ~ v1_funct_1(X2)
% 3.16/1.00      | ~ v1_relat_1(X2)
% 3.16/1.00      | k1_funct_1(X2,X0) = X1 ),
% 3.16/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_35,negated_conjecture,
% 3.16/1.00      ( v1_funct_1(sK5) ),
% 3.16/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_421,plain,
% 3.16/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.16/1.00      | ~ v1_relat_1(X2)
% 3.16/1.00      | k1_funct_1(X2,X0) = X1
% 3.16/1.00      | sK5 != X2 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_422,plain,
% 3.16/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.16/1.00      | ~ v1_relat_1(sK5)
% 3.16/1.00      | k1_funct_1(sK5,X0) = X1 ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2478,plain,
% 3.16/1.00      ( k1_funct_1(sK5,X0) = X1
% 3.16/1.00      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_38,plain,
% 3.16/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_423,plain,
% 3.16/1.00      ( k1_funct_1(sK5,X0) = X1
% 3.16/1.00      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2718,plain,
% 3.16/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.16/1.00      | v1_relat_1(sK5) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2719,plain,
% 3.16/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2718]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2745,plain,
% 3.16/1.00      ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.16/1.00      | k1_funct_1(sK5,X0) = X1 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_2478,c_38,c_423,c_2719]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2746,plain,
% 3.16/1.00      ( k1_funct_1(sK5,X0) = X1
% 3.16/1.00      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
% 3.16/1.00      inference(renaming,[status(thm)],[c_2745]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4192,plain,
% 3.16/1.00      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 3.16/1.00      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2491,c_2746]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4629,plain,
% 3.16/1.00      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.16/1.00      | k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_4192,c_38,c_2719]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4630,plain,
% 3.16/1.00      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 3.16/1.00      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 3.16/1.00      inference(renaming,[status(thm)],[c_4629]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4640,plain,
% 3.16/1.00      ( k1_funct_1(sK5,sK1(X0,k1_relat_1(sK5),sK5)) = X0
% 3.16/1.00      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3485,c_4630]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5208,plain,
% 3.16/1.00      ( k1_funct_1(sK5,sK1(sK2,k1_relat_1(sK5),sK5)) = sK2 ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3502,c_4640]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_31,negated_conjecture,
% 3.16/1.00      ( ~ m1_subset_1(X0,sK3) | k1_funct_1(sK5,X0) != sK2 ),
% 3.16/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2484,plain,
% 3.16/1.00      ( k1_funct_1(sK5,X0) != sK2 | m1_subset_1(X0,sK3) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5250,plain,
% 3.16/1.00      ( m1_subset_1(sK1(sK2,k1_relat_1(sK5),sK5),sK3) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_5208,c_2484]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5339,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | m1_subset_1(sK1(sK2,sK3,sK5),sK3) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3799,c_5250]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5731,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(sK2,k9_relat_1(sK5,sK3)) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3988,c_5339]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_19,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.16/1.00      | ~ v1_funct_1(X1)
% 3.16/1.00      | ~ v1_relat_1(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_406,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | sK5 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_407,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 3.16/1.00      | ~ v1_relat_1(sK5) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_406]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2479,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_408,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2795,plain,
% 3.16/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.16/1.00      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_2479,c_38,c_408,c_2719]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2796,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top ),
% 3.16/1.00      inference(renaming,[status(thm)],[c_2795]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5249,plain,
% 3.16/1.00      ( r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(sK2,k1_relat_1(sK5),sK5),sK2),sK5) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_5208,c_2796]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5412,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(sK1(sK2,k1_relat_1(sK5),sK5),k1_relat_1(sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3799,c_5249]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5544,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(sK1(sK2,sK3,sK5),sK3) != iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3799,c_5412]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5542,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top
% 3.16/1.00      | r2_hidden(sK2,k9_relat_1(sK5,k1_relat_1(sK5))) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2492,c_5412]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5556,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top
% 3.16/1.00      | r2_hidden(sK2,k2_relat_1(sK5)) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(light_normalisation,[status(thm)],[c_5542,c_3485]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6082,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(k4_tarski(sK1(sK2,sK3,sK5),sK2),sK5) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_5544,c_38,c_2719,c_3502,c_5556]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_21,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.16/1.00      | ~ v1_funct_1(X1)
% 3.16/1.00      | ~ v1_relat_1(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_391,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.16/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.16/1.00      | ~ v1_relat_1(X1)
% 3.16/1.00      | sK5 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_392,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5))
% 3.16/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.16/1.00      | ~ v1_relat_1(sK5) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_391]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2480,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_393,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2754,plain,
% 3.16/1.00      ( r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.16/1.00      | r2_hidden(X0,k1_relat_1(sK5)) = iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_2480,c_38,c_393,c_2719]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2755,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) = iProver_top
% 3.16/1.00      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top ),
% 3.16/1.00      inference(renaming,[status(thm)],[c_2754]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6090,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(sK1(sK2,sK3,sK5),k1_relat_1(sK5)) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_6082,c_2755]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6193,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | r2_hidden(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3799,c_6090]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6208,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0
% 3.16/1.00      | m1_subset_1(sK1(sK2,sK3,sK5),sK3) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_6193,c_2498]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6295,plain,
% 3.16/1.00      ( sK4 = k1_xboole_0 ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_5731,c_5339,c_6208]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6307,plain,
% 3.16/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_6295,c_2482]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5,plain,
% 3.16/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6309,plain,
% 3.16/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.16/1.00      inference(demodulation,[status(thm)],[c_6307,c_5]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_12,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.16/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2494,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3026,plain,
% 3.16/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_5,c_2494]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3201,plain,
% 3.16/1.00      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3026,c_2489]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2,plain,
% 3.16/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2500,plain,
% 3.16/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.16/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_0,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4,plain,
% 3.16/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_380,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 3.16/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_381,plain,
% 3.16/1.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.16/1.00      inference(unflattening,[status(thm)],[c_380]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2481,plain,
% 3.16/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_4190,plain,
% 3.16/1.00      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 3.16/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2491,c_2481]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_97,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_99,plain,
% 3.16/1.00      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_97]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_7,plain,
% 3.16/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.16/1.00      | k1_xboole_0 = X1
% 3.16/1.00      | k1_xboole_0 = X0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_110,plain,
% 3.16/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.16/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_6,plain,
% 3.16/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.16/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_111,plain,
% 3.16/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2023,plain,
% 3.16/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 3.16/1.00      theory(equality) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2721,plain,
% 3.16/1.00      ( v1_relat_1(X0)
% 3.16/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2))
% 3.16/1.00      | X0 != k2_zfmisc_1(X1,X2) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2023]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2722,plain,
% 3.16/1.00      ( X0 != k2_zfmisc_1(X1,X2)
% 3.16/1.00      | v1_relat_1(X0) = iProver_top
% 3.16/1.00      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2721]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2724,plain,
% 3.16/1.00      ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.16/1.00      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.16/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2722]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2017,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2889,plain,
% 3.16/1.00      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2017]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2890,plain,
% 3.16/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.16/1.00      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 3.16/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2889]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5110,plain,
% 3.16/1.00      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
% 3.16/1.00      inference(global_propositional_subsumption,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_4190,c_99,c_110,c_111,c_2724,c_2890]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5117,plain,
% 3.16/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),X1) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_2500,c_5110]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5822,plain,
% 3.16/1.00      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.16/1.00      inference(superposition,[status(thm)],[c_3201,c_5117]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_5829,plain,
% 3.16/1.00      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_5822]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2019,plain,
% 3.16/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.16/1.00      theory(equality) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2876,plain,
% 3.16/1.00      ( ~ r1_tarski(X0,X1)
% 3.16/1.00      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X1)
% 3.16/1.00      | k2_relset_1(sK3,sK4,sK5) != X0 ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2019]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3475,plain,
% 3.16/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0)
% 3.16/1.00      | ~ r1_tarski(k2_relat_1(sK5),X0)
% 3.16/1.00      | k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2876]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3476,plain,
% 3.16/1.00      ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
% 3.16/1.00      | r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) = iProver_top
% 3.16/1.00      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_3475]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3478,plain,
% 3.16/1.00      ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
% 3.16/1.00      | r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_xboole_0) = iProver_top
% 3.16/1.00      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3476]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_9,plain,
% 3.16/1.00      ( ~ v5_relat_1(X0,X1)
% 3.16/1.00      | v5_relat_1(X2,X1)
% 3.16/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.16/1.00      | ~ v1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3143,plain,
% 3.16/1.00      ( ~ v5_relat_1(X0,X1)
% 3.16/1.00      | v5_relat_1(sK5,X1)
% 3.16/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.16/1.00      | ~ v1_relat_1(X0) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3144,plain,
% 3.16/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 3.16/1.00      | v5_relat_1(sK5,X1) = iProver_top
% 3.16/1.00      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_3143]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3146,plain,
% 3.16/1.00      ( v5_relat_1(sK5,k1_xboole_0) = iProver_top
% 3.16/1.00      | v5_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.16/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.16/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3144]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2999,plain,
% 3.16/1.00      ( ~ r2_hidden(sK2,k1_xboole_0) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_381]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3002,plain,
% 3.16/1.00      ( r2_hidden(sK2,k1_xboole_0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2999]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_11,plain,
% 3.16/1.00      ( ~ v5_relat_1(X0,X1)
% 3.16/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.16/1.00      | ~ v1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2822,plain,
% 3.16/1.00      ( ~ v5_relat_1(sK5,X0)
% 3.16/1.00      | r1_tarski(k2_relat_1(sK5),X0)
% 3.16/1.00      | ~ v1_relat_1(sK5) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2836,plain,
% 3.16/1.00      ( v5_relat_1(sK5,X0) != iProver_top
% 3.16/1.00      | r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2822]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2838,plain,
% 3.16/1.00      ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
% 3.16/1.00      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) = iProver_top
% 3.16/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2836]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2775,plain,
% 3.16/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.16/1.00      | k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_3,plain,
% 3.16/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.16/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2731,plain,
% 3.16/1.00      ( ~ r1_tarski(k2_relset_1(sK3,sK4,sK5),X0)
% 3.16/1.00      | r2_hidden(sK2,X0)
% 3.16/1.00      | ~ r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2732,plain,
% 3.16/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),X0) != iProver_top
% 3.16/1.00      | r2_hidden(sK2,X0) = iProver_top
% 3.16/1.00      | r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2731]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_2734,plain,
% 3.16/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK5),k1_xboole_0) != iProver_top
% 3.16/1.00      | r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) != iProver_top
% 3.16/1.00      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_2732]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_10,plain,
% 3.16/1.00      ( v5_relat_1(X0,X1)
% 3.16/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.16/1.00      | ~ v1_relat_1(X0) ),
% 3.16/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_103,plain,
% 3.16/1.00      ( v5_relat_1(X0,X1) = iProver_top
% 3.16/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.16/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_105,plain,
% 3.16/1.00      ( v5_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 3.16/1.00      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top
% 3.16/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.16/1.00      inference(instantiation,[status(thm)],[c_103]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(c_39,plain,
% 3.16/1.00      ( r2_hidden(sK2,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 3.16/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.16/1.00  
% 3.16/1.00  cnf(contradiction,plain,
% 3.16/1.00      ( $false ),
% 3.16/1.00      inference(minisat,
% 3.16/1.00                [status(thm)],
% 3.16/1.00                [c_6309,c_5829,c_3478,c_3146,c_3002,c_2890,c_2838,c_2775,
% 3.16/1.00                 c_2734,c_2724,c_2719,c_111,c_110,c_105,c_99,c_39,c_38,
% 3.16/1.00                 c_33]) ).
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.00  
% 3.16/1.00  ------                               Statistics
% 3.16/1.00  
% 3.16/1.00  ------ General
% 3.16/1.00  
% 3.16/1.00  abstr_ref_over_cycles:                  0
% 3.16/1.00  abstr_ref_under_cycles:                 0
% 3.16/1.00  gc_basic_clause_elim:                   0
% 3.16/1.00  forced_gc_time:                         0
% 3.16/1.00  parsing_time:                           0.01
% 3.16/1.00  unif_index_cands_time:                  0.
% 3.16/1.00  unif_index_add_time:                    0.
% 3.16/1.00  orderings_time:                         0.
% 3.16/1.00  out_proof_time:                         0.01
% 3.16/1.00  total_time:                             0.186
% 3.16/1.00  num_of_symbols:                         55
% 3.16/1.00  num_of_terms:                           5145
% 3.16/1.00  
% 3.16/1.00  ------ Preprocessing
% 3.16/1.00  
% 3.16/1.00  num_of_splits:                          0
% 3.16/1.00  num_of_split_atoms:                     0
% 3.16/1.00  num_of_reused_defs:                     0
% 3.16/1.00  num_eq_ax_congr_red:                    36
% 3.16/1.00  num_of_sem_filtered_clauses:            1
% 3.16/1.00  num_of_subtypes:                        0
% 3.16/1.00  monotx_restored_types:                  0
% 3.16/1.00  sat_num_of_epr_types:                   0
% 3.16/1.00  sat_num_of_non_cyclic_types:            0
% 3.16/1.00  sat_guarded_non_collapsed_types:        0
% 3.16/1.00  num_pure_diseq_elim:                    0
% 3.16/1.00  simp_replaced_by:                       0
% 3.16/1.00  res_preprocessed:                       155
% 3.16/1.00  prep_upred:                             0
% 3.16/1.00  prep_unflattend:                        113
% 3.16/1.00  smt_new_axioms:                         0
% 3.16/1.00  pred_elim_cands:                        5
% 3.16/1.00  pred_elim:                              3
% 3.16/1.00  pred_elim_cl:                           6
% 3.16/1.00  pred_elim_cycles:                       9
% 3.16/1.00  merged_defs:                            0
% 3.16/1.00  merged_defs_ncl:                        0
% 3.16/1.00  bin_hyper_res:                          0
% 3.16/1.00  prep_cycles:                            4
% 3.16/1.00  pred_elim_time:                         0.026
% 3.16/1.00  splitting_time:                         0.
% 3.16/1.00  sem_filter_time:                        0.
% 3.16/1.00  monotx_time:                            0.001
% 3.16/1.00  subtype_inf_time:                       0.
% 3.16/1.00  
% 3.16/1.00  ------ Problem properties
% 3.16/1.00  
% 3.16/1.00  clauses:                                30
% 3.16/1.00  conjectures:                            3
% 3.16/1.00  epr:                                    3
% 3.16/1.00  horn:                                   26
% 3.16/1.00  ground:                                 5
% 3.16/1.00  unary:                                  6
% 3.16/1.00  binary:                                 9
% 3.16/1.00  lits:                                   74
% 3.16/1.00  lits_eq:                                17
% 3.16/1.00  fd_pure:                                0
% 3.16/1.00  fd_pseudo:                              0
% 3.16/1.00  fd_cond:                                1
% 3.16/1.00  fd_pseudo_cond:                         1
% 3.16/1.00  ac_symbols:                             0
% 3.16/1.00  
% 3.16/1.00  ------ Propositional Solver
% 3.16/1.00  
% 3.16/1.00  prop_solver_calls:                      28
% 3.16/1.00  prop_fast_solver_calls:                 1250
% 3.16/1.00  smt_solver_calls:                       0
% 3.16/1.00  smt_fast_solver_calls:                  0
% 3.16/1.00  prop_num_of_clauses:                    1872
% 3.16/1.00  prop_preprocess_simplified:             6612
% 3.16/1.00  prop_fo_subsumed:                       14
% 3.16/1.00  prop_solver_time:                       0.
% 3.16/1.00  smt_solver_time:                        0.
% 3.16/1.00  smt_fast_solver_time:                   0.
% 3.16/1.00  prop_fast_solver_time:                  0.
% 3.16/1.00  prop_unsat_core_time:                   0.
% 3.16/1.00  
% 3.16/1.00  ------ QBF
% 3.16/1.00  
% 3.16/1.00  qbf_q_res:                              0
% 3.16/1.00  qbf_num_tautologies:                    0
% 3.16/1.00  qbf_prep_cycles:                        0
% 3.16/1.00  
% 3.16/1.00  ------ BMC1
% 3.16/1.00  
% 3.16/1.00  bmc1_current_bound:                     -1
% 3.16/1.00  bmc1_last_solved_bound:                 -1
% 3.16/1.00  bmc1_unsat_core_size:                   -1
% 3.16/1.00  bmc1_unsat_core_parents_size:           -1
% 3.16/1.00  bmc1_merge_next_fun:                    0
% 3.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.00  
% 3.16/1.00  ------ Instantiation
% 3.16/1.00  
% 3.16/1.00  inst_num_of_clauses:                    746
% 3.16/1.00  inst_num_in_passive:                    13
% 3.16/1.00  inst_num_in_active:                     372
% 3.16/1.00  inst_num_in_unprocessed:                361
% 3.16/1.00  inst_num_of_loops:                      410
% 3.16/1.00  inst_num_of_learning_restarts:          0
% 3.16/1.00  inst_num_moves_active_passive:          35
% 3.16/1.00  inst_lit_activity:                      0
% 3.16/1.00  inst_lit_activity_moves:                0
% 3.16/1.00  inst_num_tautologies:                   0
% 3.16/1.00  inst_num_prop_implied:                  0
% 3.16/1.00  inst_num_existing_simplified:           0
% 3.16/1.00  inst_num_eq_res_simplified:             0
% 3.16/1.00  inst_num_child_elim:                    0
% 3.16/1.00  inst_num_of_dismatching_blockings:      93
% 3.16/1.00  inst_num_of_non_proper_insts:           519
% 3.16/1.00  inst_num_of_duplicates:                 0
% 3.16/1.00  inst_inst_num_from_inst_to_res:         0
% 3.16/1.00  inst_dismatching_checking_time:         0.
% 3.16/1.00  
% 3.16/1.00  ------ Resolution
% 3.16/1.00  
% 3.16/1.00  res_num_of_clauses:                     0
% 3.16/1.00  res_num_in_passive:                     0
% 3.16/1.00  res_num_in_active:                      0
% 3.16/1.00  res_num_of_loops:                       159
% 3.16/1.00  res_forward_subset_subsumed:            30
% 3.16/1.00  res_backward_subset_subsumed:           2
% 3.16/1.00  res_forward_subsumed:                   0
% 3.16/1.00  res_backward_subsumed:                  0
% 3.16/1.00  res_forward_subsumption_resolution:     0
% 3.16/1.00  res_backward_subsumption_resolution:    0
% 3.16/1.00  res_clause_to_clause_subsumption:       274
% 3.16/1.00  res_orphan_elimination:                 0
% 3.16/1.00  res_tautology_del:                      60
% 3.16/1.00  res_num_eq_res_simplified:              0
% 3.16/1.00  res_num_sel_changes:                    0
% 3.16/1.00  res_moves_from_active_to_pass:          0
% 3.16/1.00  
% 3.16/1.00  ------ Superposition
% 3.16/1.00  
% 3.16/1.00  sup_time_total:                         0.
% 3.16/1.00  sup_time_generating:                    0.
% 3.16/1.00  sup_time_sim_full:                      0.
% 3.16/1.00  sup_time_sim_immed:                     0.
% 3.16/1.00  
% 3.16/1.00  sup_num_of_clauses:                     113
% 3.16/1.00  sup_num_in_active:                      61
% 3.16/1.00  sup_num_in_passive:                     52
% 3.16/1.00  sup_num_of_loops:                       80
% 3.16/1.00  sup_fw_superposition:                   74
% 3.16/1.00  sup_bw_superposition:                   69
% 3.16/1.00  sup_immediate_simplified:               25
% 3.16/1.00  sup_given_eliminated:                   0
% 3.16/1.00  comparisons_done:                       0
% 3.16/1.00  comparisons_avoided:                    9
% 3.16/1.00  
% 3.16/1.00  ------ Simplifications
% 3.16/1.00  
% 3.16/1.00  
% 3.16/1.00  sim_fw_subset_subsumed:                 12
% 3.16/1.00  sim_bw_subset_subsumed:                 14
% 3.16/1.00  sim_fw_subsumed:                        3
% 3.16/1.00  sim_bw_subsumed:                        1
% 3.16/1.00  sim_fw_subsumption_res:                 2
% 3.16/1.00  sim_bw_subsumption_res:                 0
% 3.16/1.00  sim_tautology_del:                      5
% 3.16/1.00  sim_eq_tautology_del:                   5
% 3.16/1.00  sim_eq_res_simp:                        1
% 3.16/1.00  sim_fw_demodulated:                     7
% 3.16/1.00  sim_bw_demodulated:                     12
% 3.16/1.00  sim_light_normalised:                   3
% 3.16/1.00  sim_joinable_taut:                      0
% 3.16/1.00  sim_joinable_simp:                      0
% 3.16/1.00  sim_ac_normalised:                      0
% 3.16/1.00  sim_smt_subsumption:                    0
% 3.16/1.00  
%------------------------------------------------------------------------------
