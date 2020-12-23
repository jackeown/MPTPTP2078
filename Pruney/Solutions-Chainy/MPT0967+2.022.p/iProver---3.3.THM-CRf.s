%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:41 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  250 (1286 expanded)
%              Number of clauses        :  159 ( 514 expanded)
%              Number of leaves         :   27 ( 252 expanded)
%              Depth                    :   18
%              Number of atoms          :  680 (5387 expanded)
%              Number of equality atoms :  342 (1602 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f26,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f49,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f50,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f49])).

fof(f70,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
        | ~ v1_funct_2(sK7,sK4,sK6)
        | ~ v1_funct_1(sK7) )
      & ( k1_xboole_0 = sK4
        | k1_xboole_0 != sK5 )
      & r1_tarski(sK5,sK6)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
      | ~ v1_funct_2(sK7,sK4,sK6)
      | ~ v1_funct_1(sK7) )
    & ( k1_xboole_0 = sK4
      | k1_xboole_0 != sK5 )
    & r1_tarski(sK5,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f50,f70])).

fof(f122,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f71])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,(
    r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f71])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f24,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f125,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_2(sK7,sK4,sK6)
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f71])).

fof(f120,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f71])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f121,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).

fof(f72,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f84,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f127,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f82])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f63])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f130,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f91])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f124,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f71])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f25,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f30,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK3(X0,X1),X0,X1)
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK3(X0,X1),X0,X1)
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1))
      & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f68])).

fof(f116,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f135,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f119,plain,(
    ! [X0,X1] : v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2559,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2557,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_51,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2543,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2555,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6820,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2555])).

cnf(c_23,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2556,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7022,plain,
    ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6820,c_2556])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2554,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2552,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7508,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2554,c_2552])).

cnf(c_35043,plain,
    ( m1_subset_1(sK7,X0) = iProver_top
    | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7022,c_7508])).

cnf(c_36344,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_35043])).

cnf(c_37041,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2559,c_36344])).

cnf(c_50,negated_conjecture,
    ( r1_tarski(sK5,sK6) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2544,plain,
    ( r1_tarski(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2547,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_38146,plain,
    ( k1_relset_1(sK4,X0,sK7) = k1_relat_1(sK7)
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_37041,c_2547])).

cnf(c_39463,plain,
    ( k1_relset_1(sK4,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2544,c_38146])).

cnf(c_41,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_48,negated_conjecture,
    ( ~ v1_funct_2(sK7,sK4,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_53,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_265,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_2(sK7,sK4,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_48,c_53])).

cnf(c_266,negated_conjecture,
    ( ~ v1_funct_2(sK7,sK4,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_946,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK6 != X2
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_266])).

cnf(c_947,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | k1_relset_1(sK4,sK6,sK7) != sK4
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_946])).

cnf(c_2536,plain,
    ( k1_relset_1(sK4,sK6,sK7) != sK4
    | k1_xboole_0 = sK6
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_39467,plain,
    ( k1_relat_1(sK7) != sK4
    | sK6 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_39463,c_2536])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_156,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_948,plain,
    ( k1_relset_1(sK4,sK6,sK7) != sK4
    | k1_xboole_0 = sK6
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_1593,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3069,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_1595,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3084,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_3085,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3084])).

cnf(c_3087,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3085])).

cnf(c_4263,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_4264,plain,
    ( sK6 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4263])).

cnf(c_4266,plain,
    ( sK6 != k1_xboole_0
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4264])).

cnf(c_4423,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_52,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_959,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X2
    | sK4 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_52])).

cnf(c_960,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_962,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_960,c_51])).

cnf(c_4871,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2543,c_2547])).

cnf(c_5225,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_962,c_4871])).

cnf(c_1594,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4278,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_6506,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_4278])).

cnf(c_6507,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_6506])).

cnf(c_4227,plain,
    ( k1_relset_1(sK4,sK6,sK7) != X0
    | k1_relset_1(sK4,sK6,sK7) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_6990,plain,
    ( k1_relset_1(sK4,sK6,sK7) != k1_relat_1(sK7)
    | k1_relset_1(sK4,sK6,sK7) = sK4
    | sK4 != k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4227])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2572,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2574,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4564,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_2574])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2565,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6866,plain,
    ( sK5 = sK6
    | r1_tarski(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2544,c_2565])).

cnf(c_6977,plain,
    ( sK5 = sK6
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4564,c_6866])).

cnf(c_980,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | sK5 != sK6
    | sK4 != sK4
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_52])).

cnf(c_981,plain,
    ( sK5 != sK6
    | sK4 != sK4
    | sK7 != sK7
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_2909,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ r1_tarski(sK7,k2_zfmisc_1(sK4,sK6)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2910,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(sK4,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2909])).

cnf(c_3033,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK6))
    | r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3040,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK6)) = iProver_top
    | r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3033])).

cnf(c_3352,plain,
    ( ~ r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3353,plain,
    ( r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3352])).

cnf(c_3395,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_377,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_378,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_458,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_24,c_378])).

cnf(c_2542,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_4464,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2544,c_2542])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2548,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5594,plain,
    ( v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2548])).

cnf(c_7026,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6977,c_981,c_2910,c_3040,c_3069,c_3353,c_3395,c_4464,c_5594])).

cnf(c_3061,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_6057,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3061])).

cnf(c_11541,plain,
    ( k1_relat_1(sK7) != sK4
    | sK4 = k1_relat_1(sK7)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_6057])).

cnf(c_12,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2564,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5592,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2554,c_2548])).

cnf(c_14867,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2564,c_5592])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2553,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4032,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2553])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2571,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7427,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4032,c_2571])).

cnf(c_7680,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7427,c_2574])).

cnf(c_14941,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_14867,c_7680])).

cnf(c_15447,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_14941])).

cnf(c_18,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_21,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2558,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5627,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_2558])).

cnf(c_17,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_5836,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_zfmisc_1(X1,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2559])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2563,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6862,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2563,c_2565])).

cnf(c_9011,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5836,c_6862])).

cnf(c_10248,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)) = k1_xboole_0
    | r1_tarski(X2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5836,c_9011])).

cnf(c_12690,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))) = k1_xboole_0
    | r1_tarski(X3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5836,c_10248])).

cnf(c_15347,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)))) = k1_xboole_0
    | r1_tarski(X3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5627,c_12690])).

cnf(c_33989,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(sK7,X3)))) = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_15447,c_15347])).

cnf(c_49,negated_conjecture,
    ( k1_xboole_0 != sK5
    | k1_xboole_0 = sK4 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2979,plain,
    ( sK4 != X0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1594])).

cnf(c_3068,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2979])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_5787,plain,
    ( ~ v1_xboole_0(sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5788,plain,
    ( k1_xboole_0 = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5787])).

cnf(c_47,plain,
    ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2545,plain,
    ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3456,plain,
    ( m1_subset_1(sK3(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2545])).

cnf(c_4034,plain,
    ( r1_tarski(sK3(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3456,c_2553])).

cnf(c_4467,plain,
    ( v1_xboole_0(sK3(X0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4034,c_2542])).

cnf(c_6272,plain,
    ( v1_xboole_0(sK3(X0,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4467,c_156])).

cnf(c_2569,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6281,plain,
    ( sK3(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6272,c_2569])).

cnf(c_4870,plain,
    ( k1_relset_1(X0,X1,sK3(X0,X1)) = k1_relat_1(sK3(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2545,c_2547])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_44,plain,
    ( v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_894,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | X2 != X1
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3(X3,X2) != X0
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_44])).

cnf(c_895,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | k1_relset_1(k1_xboole_0,X0,sK3(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_894])).

cnf(c_903,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_895,c_47])).

cnf(c_5425,plain,
    ( k1_relat_1(sK3(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4870,c_903])).

cnf(c_6464,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6281,c_5425])).

cnf(c_6991,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | k1_relset_1(sK4,sK6,sK7) = k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_6992,plain,
    ( k1_relset_1(sK4,sK6,sK7) = k1_relat_1(sK7)
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6991])).

cnf(c_6860,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4564,c_2565])).

cnf(c_15538,plain,
    ( sK7 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_15447,c_6860])).

cnf(c_15656,plain,
    ( sK7 = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15538])).

cnf(c_11542,plain,
    ( k1_relat_1(sK7) != X0
    | sK4 != X0
    | sK4 = k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3061])).

cnf(c_26384,plain,
    ( k1_relat_1(sK7) != k1_relat_1(X0)
    | sK4 != k1_relat_1(X0)
    | sK4 = k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11542])).

cnf(c_26386,plain,
    ( k1_relat_1(sK7) != k1_relat_1(k1_xboole_0)
    | sK4 = k1_relat_1(sK7)
    | sK4 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_26384])).

cnf(c_1603,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_26385,plain,
    ( k1_relat_1(sK7) = k1_relat_1(X0)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_1603])).

cnf(c_26387,plain,
    ( k1_relat_1(sK7) = k1_relat_1(k1_xboole_0)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_26385])).

cnf(c_34585,plain,
    ( k1_relat_1(X0) != X1
    | sK4 != X1
    | sK4 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_3061])).

cnf(c_34596,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK4 = k1_relat_1(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34585])).

cnf(c_34673,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33989,c_49,c_156,c_948,c_981,c_2910,c_3040,c_3068,c_3069,c_3353,c_3395,c_4266,c_4423,c_4464,c_5594,c_5788,c_6464,c_6507,c_6977,c_6990,c_6992,c_15656,c_26386,c_26387,c_34596])).

cnf(c_39863,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39467,c_49,c_156,c_948,c_981,c_2910,c_3040,c_3068,c_3069,c_3087,c_3353,c_3395,c_4266,c_4423,c_4464,c_5225,c_5594,c_5788,c_6464,c_6507,c_6977,c_6990,c_6992,c_11541,c_15656,c_26386,c_26387,c_34596,c_39463])).

cnf(c_39869,plain,
    ( r1_tarski(sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_37041,c_39863])).

cnf(c_57,plain,
    ( r1_tarski(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39869,c_57])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:08:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.26/1.44  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/1.44  
% 7.26/1.44  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.44  
% 7.26/1.44  ------  iProver source info
% 7.26/1.44  
% 7.26/1.44  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.44  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.44  git: non_committed_changes: false
% 7.26/1.44  git: last_make_outside_of_git: false
% 7.26/1.44  
% 7.26/1.44  ------ 
% 7.26/1.44  
% 7.26/1.44  ------ Input Options
% 7.26/1.44  
% 7.26/1.44  --out_options                           all
% 7.26/1.44  --tptp_safe_out                         true
% 7.26/1.44  --problem_path                          ""
% 7.26/1.44  --include_path                          ""
% 7.26/1.44  --clausifier                            res/vclausify_rel
% 7.26/1.44  --clausifier_options                    --mode clausify
% 7.26/1.44  --stdin                                 false
% 7.26/1.44  --stats_out                             all
% 7.26/1.44  
% 7.26/1.44  ------ General Options
% 7.26/1.44  
% 7.26/1.44  --fof                                   false
% 7.26/1.44  --time_out_real                         305.
% 7.26/1.44  --time_out_virtual                      -1.
% 7.26/1.44  --symbol_type_check                     false
% 7.26/1.44  --clausify_out                          false
% 7.26/1.44  --sig_cnt_out                           false
% 7.26/1.44  --trig_cnt_out                          false
% 7.26/1.44  --trig_cnt_out_tolerance                1.
% 7.26/1.44  --trig_cnt_out_sk_spl                   false
% 7.26/1.44  --abstr_cl_out                          false
% 7.26/1.44  
% 7.26/1.44  ------ Global Options
% 7.26/1.44  
% 7.26/1.44  --schedule                              default
% 7.26/1.44  --add_important_lit                     false
% 7.26/1.44  --prop_solver_per_cl                    1000
% 7.26/1.44  --min_unsat_core                        false
% 7.26/1.44  --soft_assumptions                      false
% 7.26/1.44  --soft_lemma_size                       3
% 7.26/1.44  --prop_impl_unit_size                   0
% 7.26/1.44  --prop_impl_unit                        []
% 7.26/1.44  --share_sel_clauses                     true
% 7.26/1.44  --reset_solvers                         false
% 7.26/1.44  --bc_imp_inh                            [conj_cone]
% 7.26/1.44  --conj_cone_tolerance                   3.
% 7.26/1.44  --extra_neg_conj                        none
% 7.26/1.44  --large_theory_mode                     true
% 7.26/1.44  --prolific_symb_bound                   200
% 7.26/1.44  --lt_threshold                          2000
% 7.26/1.44  --clause_weak_htbl                      true
% 7.26/1.44  --gc_record_bc_elim                     false
% 7.26/1.44  
% 7.26/1.44  ------ Preprocessing Options
% 7.26/1.44  
% 7.26/1.44  --preprocessing_flag                    true
% 7.26/1.44  --time_out_prep_mult                    0.1
% 7.26/1.44  --splitting_mode                        input
% 7.26/1.44  --splitting_grd                         true
% 7.26/1.44  --splitting_cvd                         false
% 7.26/1.44  --splitting_cvd_svl                     false
% 7.26/1.44  --splitting_nvd                         32
% 7.26/1.44  --sub_typing                            true
% 7.26/1.44  --prep_gs_sim                           true
% 7.26/1.44  --prep_unflatten                        true
% 7.26/1.44  --prep_res_sim                          true
% 7.26/1.44  --prep_upred                            true
% 7.26/1.44  --prep_sem_filter                       exhaustive
% 7.26/1.44  --prep_sem_filter_out                   false
% 7.26/1.44  --pred_elim                             true
% 7.26/1.44  --res_sim_input                         true
% 7.26/1.44  --eq_ax_congr_red                       true
% 7.26/1.44  --pure_diseq_elim                       true
% 7.26/1.44  --brand_transform                       false
% 7.26/1.44  --non_eq_to_eq                          false
% 7.26/1.44  --prep_def_merge                        true
% 7.26/1.44  --prep_def_merge_prop_impl              false
% 7.26/1.44  --prep_def_merge_mbd                    true
% 7.26/1.44  --prep_def_merge_tr_red                 false
% 7.26/1.44  --prep_def_merge_tr_cl                  false
% 7.26/1.44  --smt_preprocessing                     true
% 7.26/1.44  --smt_ac_axioms                         fast
% 7.26/1.44  --preprocessed_out                      false
% 7.26/1.44  --preprocessed_stats                    false
% 7.26/1.44  
% 7.26/1.44  ------ Abstraction refinement Options
% 7.26/1.44  
% 7.26/1.44  --abstr_ref                             []
% 7.26/1.44  --abstr_ref_prep                        false
% 7.26/1.44  --abstr_ref_until_sat                   false
% 7.26/1.44  --abstr_ref_sig_restrict                funpre
% 7.26/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.44  --abstr_ref_under                       []
% 7.26/1.44  
% 7.26/1.44  ------ SAT Options
% 7.26/1.44  
% 7.26/1.44  --sat_mode                              false
% 7.26/1.44  --sat_fm_restart_options                ""
% 7.26/1.44  --sat_gr_def                            false
% 7.26/1.44  --sat_epr_types                         true
% 7.26/1.44  --sat_non_cyclic_types                  false
% 7.26/1.44  --sat_finite_models                     false
% 7.26/1.44  --sat_fm_lemmas                         false
% 7.26/1.44  --sat_fm_prep                           false
% 7.26/1.44  --sat_fm_uc_incr                        true
% 7.26/1.44  --sat_out_model                         small
% 7.26/1.44  --sat_out_clauses                       false
% 7.26/1.44  
% 7.26/1.44  ------ QBF Options
% 7.26/1.44  
% 7.26/1.44  --qbf_mode                              false
% 7.26/1.44  --qbf_elim_univ                         false
% 7.26/1.44  --qbf_dom_inst                          none
% 7.26/1.44  --qbf_dom_pre_inst                      false
% 7.26/1.44  --qbf_sk_in                             false
% 7.26/1.44  --qbf_pred_elim                         true
% 7.26/1.44  --qbf_split                             512
% 7.26/1.44  
% 7.26/1.44  ------ BMC1 Options
% 7.26/1.44  
% 7.26/1.44  --bmc1_incremental                      false
% 7.26/1.44  --bmc1_axioms                           reachable_all
% 7.26/1.44  --bmc1_min_bound                        0
% 7.26/1.44  --bmc1_max_bound                        -1
% 7.26/1.44  --bmc1_max_bound_default                -1
% 7.26/1.44  --bmc1_symbol_reachability              true
% 7.26/1.44  --bmc1_property_lemmas                  false
% 7.26/1.44  --bmc1_k_induction                      false
% 7.26/1.44  --bmc1_non_equiv_states                 false
% 7.26/1.44  --bmc1_deadlock                         false
% 7.26/1.44  --bmc1_ucm                              false
% 7.26/1.44  --bmc1_add_unsat_core                   none
% 7.26/1.44  --bmc1_unsat_core_children              false
% 7.26/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.44  --bmc1_out_stat                         full
% 7.26/1.44  --bmc1_ground_init                      false
% 7.26/1.44  --bmc1_pre_inst_next_state              false
% 7.26/1.44  --bmc1_pre_inst_state                   false
% 7.26/1.44  --bmc1_pre_inst_reach_state             false
% 7.26/1.44  --bmc1_out_unsat_core                   false
% 7.26/1.44  --bmc1_aig_witness_out                  false
% 7.26/1.44  --bmc1_verbose                          false
% 7.26/1.44  --bmc1_dump_clauses_tptp                false
% 7.26/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.44  --bmc1_dump_file                        -
% 7.26/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.44  --bmc1_ucm_extend_mode                  1
% 7.26/1.44  --bmc1_ucm_init_mode                    2
% 7.26/1.44  --bmc1_ucm_cone_mode                    none
% 7.26/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.44  --bmc1_ucm_relax_model                  4
% 7.26/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.44  --bmc1_ucm_layered_model                none
% 7.26/1.44  --bmc1_ucm_max_lemma_size               10
% 7.26/1.44  
% 7.26/1.44  ------ AIG Options
% 7.26/1.44  
% 7.26/1.44  --aig_mode                              false
% 7.26/1.44  
% 7.26/1.44  ------ Instantiation Options
% 7.26/1.44  
% 7.26/1.44  --instantiation_flag                    true
% 7.26/1.44  --inst_sos_flag                         false
% 7.26/1.44  --inst_sos_phase                        true
% 7.26/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.44  --inst_lit_sel_side                     num_symb
% 7.26/1.44  --inst_solver_per_active                1400
% 7.26/1.44  --inst_solver_calls_frac                1.
% 7.26/1.44  --inst_passive_queue_type               priority_queues
% 7.26/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.44  --inst_passive_queues_freq              [25;2]
% 7.26/1.44  --inst_dismatching                      true
% 7.26/1.44  --inst_eager_unprocessed_to_passive     true
% 7.26/1.44  --inst_prop_sim_given                   true
% 7.26/1.44  --inst_prop_sim_new                     false
% 7.26/1.44  --inst_subs_new                         false
% 7.26/1.44  --inst_eq_res_simp                      false
% 7.26/1.44  --inst_subs_given                       false
% 7.26/1.44  --inst_orphan_elimination               true
% 7.26/1.44  --inst_learning_loop_flag               true
% 7.26/1.44  --inst_learning_start                   3000
% 7.26/1.44  --inst_learning_factor                  2
% 7.26/1.44  --inst_start_prop_sim_after_learn       3
% 7.26/1.44  --inst_sel_renew                        solver
% 7.26/1.44  --inst_lit_activity_flag                true
% 7.26/1.44  --inst_restr_to_given                   false
% 7.26/1.44  --inst_activity_threshold               500
% 7.26/1.44  --inst_out_proof                        true
% 7.26/1.44  
% 7.26/1.44  ------ Resolution Options
% 7.26/1.44  
% 7.26/1.44  --resolution_flag                       true
% 7.26/1.44  --res_lit_sel                           adaptive
% 7.26/1.44  --res_lit_sel_side                      none
% 7.26/1.44  --res_ordering                          kbo
% 7.26/1.44  --res_to_prop_solver                    active
% 7.26/1.44  --res_prop_simpl_new                    false
% 7.26/1.44  --res_prop_simpl_given                  true
% 7.26/1.44  --res_passive_queue_type                priority_queues
% 7.26/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.44  --res_passive_queues_freq               [15;5]
% 7.26/1.44  --res_forward_subs                      full
% 7.26/1.44  --res_backward_subs                     full
% 7.26/1.44  --res_forward_subs_resolution           true
% 7.26/1.44  --res_backward_subs_resolution          true
% 7.26/1.44  --res_orphan_elimination                true
% 7.26/1.44  --res_time_limit                        2.
% 7.26/1.44  --res_out_proof                         true
% 7.26/1.44  
% 7.26/1.44  ------ Superposition Options
% 7.26/1.44  
% 7.26/1.44  --superposition_flag                    true
% 7.26/1.44  --sup_passive_queue_type                priority_queues
% 7.26/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.44  --demod_completeness_check              fast
% 7.26/1.44  --demod_use_ground                      true
% 7.26/1.44  --sup_to_prop_solver                    passive
% 7.26/1.44  --sup_prop_simpl_new                    true
% 7.26/1.44  --sup_prop_simpl_given                  true
% 7.26/1.44  --sup_fun_splitting                     false
% 7.26/1.44  --sup_smt_interval                      50000
% 7.26/1.44  
% 7.26/1.44  ------ Superposition Simplification Setup
% 7.26/1.44  
% 7.26/1.44  --sup_indices_passive                   []
% 7.26/1.44  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.44  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.44  --sup_full_bw                           [BwDemod]
% 7.26/1.44  --sup_immed_triv                        [TrivRules]
% 7.26/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.44  --sup_immed_bw_main                     []
% 7.26/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.44  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.44  
% 7.26/1.44  ------ Combination Options
% 7.26/1.44  
% 7.26/1.44  --comb_res_mult                         3
% 7.26/1.44  --comb_sup_mult                         2
% 7.26/1.44  --comb_inst_mult                        10
% 7.26/1.44  
% 7.26/1.44  ------ Debug Options
% 7.26/1.44  
% 7.26/1.44  --dbg_backtrace                         false
% 7.26/1.44  --dbg_dump_prop_clauses                 false
% 7.26/1.44  --dbg_dump_prop_clauses_file            -
% 7.26/1.44  --dbg_out_stat                          false
% 7.26/1.44  ------ Parsing...
% 7.26/1.44  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.44  
% 7.26/1.44  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.26/1.44  
% 7.26/1.44  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.44  
% 7.26/1.44  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.44  ------ Proving...
% 7.26/1.44  ------ Problem Properties 
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  clauses                                 52
% 7.26/1.44  conjectures                             3
% 7.26/1.44  EPR                                     15
% 7.26/1.44  Horn                                    42
% 7.26/1.44  unary                                   15
% 7.26/1.44  binary                                  21
% 7.26/1.44  lits                                    109
% 7.26/1.44  lits eq                                 38
% 7.26/1.44  fd_pure                                 0
% 7.26/1.44  fd_pseudo                               0
% 7.26/1.44  fd_cond                                 4
% 7.26/1.44  fd_pseudo_cond                          2
% 7.26/1.44  AC symbols                              0
% 7.26/1.44  
% 7.26/1.44  ------ Schedule dynamic 5 is on 
% 7.26/1.44  
% 7.26/1.44  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  ------ 
% 7.26/1.44  Current options:
% 7.26/1.44  ------ 
% 7.26/1.44  
% 7.26/1.44  ------ Input Options
% 7.26/1.44  
% 7.26/1.44  --out_options                           all
% 7.26/1.44  --tptp_safe_out                         true
% 7.26/1.44  --problem_path                          ""
% 7.26/1.44  --include_path                          ""
% 7.26/1.44  --clausifier                            res/vclausify_rel
% 7.26/1.44  --clausifier_options                    --mode clausify
% 7.26/1.44  --stdin                                 false
% 7.26/1.44  --stats_out                             all
% 7.26/1.44  
% 7.26/1.44  ------ General Options
% 7.26/1.44  
% 7.26/1.44  --fof                                   false
% 7.26/1.44  --time_out_real                         305.
% 7.26/1.44  --time_out_virtual                      -1.
% 7.26/1.44  --symbol_type_check                     false
% 7.26/1.44  --clausify_out                          false
% 7.26/1.44  --sig_cnt_out                           false
% 7.26/1.44  --trig_cnt_out                          false
% 7.26/1.44  --trig_cnt_out_tolerance                1.
% 7.26/1.44  --trig_cnt_out_sk_spl                   false
% 7.26/1.44  --abstr_cl_out                          false
% 7.26/1.44  
% 7.26/1.44  ------ Global Options
% 7.26/1.44  
% 7.26/1.44  --schedule                              default
% 7.26/1.44  --add_important_lit                     false
% 7.26/1.44  --prop_solver_per_cl                    1000
% 7.26/1.44  --min_unsat_core                        false
% 7.26/1.44  --soft_assumptions                      false
% 7.26/1.44  --soft_lemma_size                       3
% 7.26/1.44  --prop_impl_unit_size                   0
% 7.26/1.44  --prop_impl_unit                        []
% 7.26/1.44  --share_sel_clauses                     true
% 7.26/1.44  --reset_solvers                         false
% 7.26/1.44  --bc_imp_inh                            [conj_cone]
% 7.26/1.44  --conj_cone_tolerance                   3.
% 7.26/1.44  --extra_neg_conj                        none
% 7.26/1.44  --large_theory_mode                     true
% 7.26/1.44  --prolific_symb_bound                   200
% 7.26/1.44  --lt_threshold                          2000
% 7.26/1.44  --clause_weak_htbl                      true
% 7.26/1.44  --gc_record_bc_elim                     false
% 7.26/1.44  
% 7.26/1.44  ------ Preprocessing Options
% 7.26/1.44  
% 7.26/1.44  --preprocessing_flag                    true
% 7.26/1.44  --time_out_prep_mult                    0.1
% 7.26/1.44  --splitting_mode                        input
% 7.26/1.44  --splitting_grd                         true
% 7.26/1.44  --splitting_cvd                         false
% 7.26/1.44  --splitting_cvd_svl                     false
% 7.26/1.44  --splitting_nvd                         32
% 7.26/1.44  --sub_typing                            true
% 7.26/1.44  --prep_gs_sim                           true
% 7.26/1.44  --prep_unflatten                        true
% 7.26/1.44  --prep_res_sim                          true
% 7.26/1.44  --prep_upred                            true
% 7.26/1.44  --prep_sem_filter                       exhaustive
% 7.26/1.44  --prep_sem_filter_out                   false
% 7.26/1.44  --pred_elim                             true
% 7.26/1.44  --res_sim_input                         true
% 7.26/1.44  --eq_ax_congr_red                       true
% 7.26/1.44  --pure_diseq_elim                       true
% 7.26/1.44  --brand_transform                       false
% 7.26/1.44  --non_eq_to_eq                          false
% 7.26/1.44  --prep_def_merge                        true
% 7.26/1.44  --prep_def_merge_prop_impl              false
% 7.26/1.44  --prep_def_merge_mbd                    true
% 7.26/1.44  --prep_def_merge_tr_red                 false
% 7.26/1.44  --prep_def_merge_tr_cl                  false
% 7.26/1.44  --smt_preprocessing                     true
% 7.26/1.44  --smt_ac_axioms                         fast
% 7.26/1.44  --preprocessed_out                      false
% 7.26/1.44  --preprocessed_stats                    false
% 7.26/1.44  
% 7.26/1.44  ------ Abstraction refinement Options
% 7.26/1.44  
% 7.26/1.44  --abstr_ref                             []
% 7.26/1.44  --abstr_ref_prep                        false
% 7.26/1.44  --abstr_ref_until_sat                   false
% 7.26/1.44  --abstr_ref_sig_restrict                funpre
% 7.26/1.44  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.44  --abstr_ref_under                       []
% 7.26/1.44  
% 7.26/1.44  ------ SAT Options
% 7.26/1.44  
% 7.26/1.44  --sat_mode                              false
% 7.26/1.44  --sat_fm_restart_options                ""
% 7.26/1.44  --sat_gr_def                            false
% 7.26/1.44  --sat_epr_types                         true
% 7.26/1.44  --sat_non_cyclic_types                  false
% 7.26/1.44  --sat_finite_models                     false
% 7.26/1.44  --sat_fm_lemmas                         false
% 7.26/1.44  --sat_fm_prep                           false
% 7.26/1.44  --sat_fm_uc_incr                        true
% 7.26/1.44  --sat_out_model                         small
% 7.26/1.44  --sat_out_clauses                       false
% 7.26/1.44  
% 7.26/1.44  ------ QBF Options
% 7.26/1.44  
% 7.26/1.44  --qbf_mode                              false
% 7.26/1.44  --qbf_elim_univ                         false
% 7.26/1.44  --qbf_dom_inst                          none
% 7.26/1.44  --qbf_dom_pre_inst                      false
% 7.26/1.44  --qbf_sk_in                             false
% 7.26/1.44  --qbf_pred_elim                         true
% 7.26/1.44  --qbf_split                             512
% 7.26/1.44  
% 7.26/1.44  ------ BMC1 Options
% 7.26/1.44  
% 7.26/1.44  --bmc1_incremental                      false
% 7.26/1.44  --bmc1_axioms                           reachable_all
% 7.26/1.44  --bmc1_min_bound                        0
% 7.26/1.44  --bmc1_max_bound                        -1
% 7.26/1.44  --bmc1_max_bound_default                -1
% 7.26/1.44  --bmc1_symbol_reachability              true
% 7.26/1.44  --bmc1_property_lemmas                  false
% 7.26/1.44  --bmc1_k_induction                      false
% 7.26/1.44  --bmc1_non_equiv_states                 false
% 7.26/1.44  --bmc1_deadlock                         false
% 7.26/1.44  --bmc1_ucm                              false
% 7.26/1.44  --bmc1_add_unsat_core                   none
% 7.26/1.44  --bmc1_unsat_core_children              false
% 7.26/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.44  --bmc1_out_stat                         full
% 7.26/1.44  --bmc1_ground_init                      false
% 7.26/1.44  --bmc1_pre_inst_next_state              false
% 7.26/1.44  --bmc1_pre_inst_state                   false
% 7.26/1.44  --bmc1_pre_inst_reach_state             false
% 7.26/1.44  --bmc1_out_unsat_core                   false
% 7.26/1.44  --bmc1_aig_witness_out                  false
% 7.26/1.44  --bmc1_verbose                          false
% 7.26/1.44  --bmc1_dump_clauses_tptp                false
% 7.26/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.44  --bmc1_dump_file                        -
% 7.26/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.44  --bmc1_ucm_extend_mode                  1
% 7.26/1.44  --bmc1_ucm_init_mode                    2
% 7.26/1.44  --bmc1_ucm_cone_mode                    none
% 7.26/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.44  --bmc1_ucm_relax_model                  4
% 7.26/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.44  --bmc1_ucm_layered_model                none
% 7.26/1.44  --bmc1_ucm_max_lemma_size               10
% 7.26/1.44  
% 7.26/1.44  ------ AIG Options
% 7.26/1.44  
% 7.26/1.44  --aig_mode                              false
% 7.26/1.44  
% 7.26/1.44  ------ Instantiation Options
% 7.26/1.44  
% 7.26/1.44  --instantiation_flag                    true
% 7.26/1.44  --inst_sos_flag                         false
% 7.26/1.44  --inst_sos_phase                        true
% 7.26/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.44  --inst_lit_sel_side                     none
% 7.26/1.44  --inst_solver_per_active                1400
% 7.26/1.44  --inst_solver_calls_frac                1.
% 7.26/1.44  --inst_passive_queue_type               priority_queues
% 7.26/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.44  --inst_passive_queues_freq              [25;2]
% 7.26/1.44  --inst_dismatching                      true
% 7.26/1.44  --inst_eager_unprocessed_to_passive     true
% 7.26/1.44  --inst_prop_sim_given                   true
% 7.26/1.44  --inst_prop_sim_new                     false
% 7.26/1.44  --inst_subs_new                         false
% 7.26/1.44  --inst_eq_res_simp                      false
% 7.26/1.44  --inst_subs_given                       false
% 7.26/1.44  --inst_orphan_elimination               true
% 7.26/1.44  --inst_learning_loop_flag               true
% 7.26/1.44  --inst_learning_start                   3000
% 7.26/1.44  --inst_learning_factor                  2
% 7.26/1.44  --inst_start_prop_sim_after_learn       3
% 7.26/1.44  --inst_sel_renew                        solver
% 7.26/1.44  --inst_lit_activity_flag                true
% 7.26/1.44  --inst_restr_to_given                   false
% 7.26/1.44  --inst_activity_threshold               500
% 7.26/1.44  --inst_out_proof                        true
% 7.26/1.44  
% 7.26/1.44  ------ Resolution Options
% 7.26/1.44  
% 7.26/1.44  --resolution_flag                       false
% 7.26/1.44  --res_lit_sel                           adaptive
% 7.26/1.44  --res_lit_sel_side                      none
% 7.26/1.44  --res_ordering                          kbo
% 7.26/1.44  --res_to_prop_solver                    active
% 7.26/1.44  --res_prop_simpl_new                    false
% 7.26/1.44  --res_prop_simpl_given                  true
% 7.26/1.44  --res_passive_queue_type                priority_queues
% 7.26/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.44  --res_passive_queues_freq               [15;5]
% 7.26/1.44  --res_forward_subs                      full
% 7.26/1.44  --res_backward_subs                     full
% 7.26/1.44  --res_forward_subs_resolution           true
% 7.26/1.44  --res_backward_subs_resolution          true
% 7.26/1.44  --res_orphan_elimination                true
% 7.26/1.44  --res_time_limit                        2.
% 7.26/1.44  --res_out_proof                         true
% 7.26/1.44  
% 7.26/1.44  ------ Superposition Options
% 7.26/1.44  
% 7.26/1.44  --superposition_flag                    true
% 7.26/1.44  --sup_passive_queue_type                priority_queues
% 7.26/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.44  --demod_completeness_check              fast
% 7.26/1.44  --demod_use_ground                      true
% 7.26/1.44  --sup_to_prop_solver                    passive
% 7.26/1.44  --sup_prop_simpl_new                    true
% 7.26/1.44  --sup_prop_simpl_given                  true
% 7.26/1.44  --sup_fun_splitting                     false
% 7.26/1.44  --sup_smt_interval                      50000
% 7.26/1.44  
% 7.26/1.44  ------ Superposition Simplification Setup
% 7.26/1.44  
% 7.26/1.44  --sup_indices_passive                   []
% 7.26/1.44  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.44  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.44  --sup_full_bw                           [BwDemod]
% 7.26/1.44  --sup_immed_triv                        [TrivRules]
% 7.26/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.44  --sup_immed_bw_main                     []
% 7.26/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.44  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.44  
% 7.26/1.44  ------ Combination Options
% 7.26/1.44  
% 7.26/1.44  --comb_res_mult                         3
% 7.26/1.44  --comb_sup_mult                         2
% 7.26/1.44  --comb_inst_mult                        10
% 7.26/1.44  
% 7.26/1.44  ------ Debug Options
% 7.26/1.44  
% 7.26/1.44  --dbg_backtrace                         false
% 7.26/1.44  --dbg_dump_prop_clauses                 false
% 7.26/1.44  --dbg_dump_prop_clauses_file            -
% 7.26/1.44  --dbg_out_stat                          false
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  ------ Proving...
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  % SZS status Theorem for theBenchmark.p
% 7.26/1.44  
% 7.26/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.44  
% 7.26/1.44  fof(f11,axiom,(
% 7.26/1.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f36,plain,(
% 7.26/1.44    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 7.26/1.44    inference(ennf_transformation,[],[f11])).
% 7.26/1.44  
% 7.26/1.44  fof(f93,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f36])).
% 7.26/1.44  
% 7.26/1.44  fof(f12,axiom,(
% 7.26/1.44    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f37,plain,(
% 7.26/1.44    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.26/1.44    inference(ennf_transformation,[],[f12])).
% 7.26/1.44  
% 7.26/1.44  fof(f94,plain,(
% 7.26/1.44    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f37])).
% 7.26/1.44  
% 7.26/1.44  fof(f26,conjecture,(
% 7.26/1.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f27,negated_conjecture,(
% 7.26/1.44    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 7.26/1.44    inference(negated_conjecture,[],[f26])).
% 7.26/1.44  
% 7.26/1.44  fof(f49,plain,(
% 7.26/1.44    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.26/1.44    inference(ennf_transformation,[],[f27])).
% 7.26/1.44  
% 7.26/1.44  fof(f50,plain,(
% 7.26/1.44    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.26/1.44    inference(flattening,[],[f49])).
% 7.26/1.44  
% 7.26/1.44  fof(f70,plain,(
% 7.26/1.44    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_2(sK7,sK4,sK6) | ~v1_funct_1(sK7)) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(sK5,sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 7.26/1.44    introduced(choice_axiom,[])).
% 7.26/1.44  
% 7.26/1.44  fof(f71,plain,(
% 7.26/1.44    (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_2(sK7,sK4,sK6) | ~v1_funct_1(sK7)) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(sK5,sK6) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 7.26/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f50,f70])).
% 7.26/1.44  
% 7.26/1.44  fof(f122,plain,(
% 7.26/1.44    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 7.26/1.44    inference(cnf_transformation,[],[f71])).
% 7.26/1.44  
% 7.26/1.44  fof(f15,axiom,(
% 7.26/1.44    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f39,plain,(
% 7.26/1.44    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.26/1.44    inference(ennf_transformation,[],[f15])).
% 7.26/1.44  
% 7.26/1.44  fof(f40,plain,(
% 7.26/1.44    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.26/1.44    inference(flattening,[],[f39])).
% 7.26/1.44  
% 7.26/1.44  fof(f97,plain,(
% 7.26/1.44    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f40])).
% 7.26/1.44  
% 7.26/1.44  fof(f13,axiom,(
% 7.26/1.44    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f95,plain,(
% 7.26/1.44    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.26/1.44    inference(cnf_transformation,[],[f13])).
% 7.26/1.44  
% 7.26/1.44  fof(f16,axiom,(
% 7.26/1.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f65,plain,(
% 7.26/1.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.26/1.44    inference(nnf_transformation,[],[f16])).
% 7.26/1.44  
% 7.26/1.44  fof(f99,plain,(
% 7.26/1.44    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f65])).
% 7.26/1.44  
% 7.26/1.44  fof(f17,axiom,(
% 7.26/1.44    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f41,plain,(
% 7.26/1.44    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.26/1.44    inference(ennf_transformation,[],[f17])).
% 7.26/1.44  
% 7.26/1.44  fof(f42,plain,(
% 7.26/1.44    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.26/1.44    inference(flattening,[],[f41])).
% 7.26/1.44  
% 7.26/1.44  fof(f100,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f42])).
% 7.26/1.44  
% 7.26/1.44  fof(f123,plain,(
% 7.26/1.44    r1_tarski(sK5,sK6)),
% 7.26/1.44    inference(cnf_transformation,[],[f71])).
% 7.26/1.44  
% 7.26/1.44  fof(f23,axiom,(
% 7.26/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f46,plain,(
% 7.26/1.44    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    inference(ennf_transformation,[],[f23])).
% 7.26/1.44  
% 7.26/1.44  fof(f109,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.44    inference(cnf_transformation,[],[f46])).
% 7.26/1.44  
% 7.26/1.44  fof(f24,axiom,(
% 7.26/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f47,plain,(
% 7.26/1.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    inference(ennf_transformation,[],[f24])).
% 7.26/1.44  
% 7.26/1.44  fof(f48,plain,(
% 7.26/1.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    inference(flattening,[],[f47])).
% 7.26/1.44  
% 7.26/1.44  fof(f67,plain,(
% 7.26/1.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    inference(nnf_transformation,[],[f48])).
% 7.26/1.44  
% 7.26/1.44  fof(f112,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.44    inference(cnf_transformation,[],[f67])).
% 7.26/1.44  
% 7.26/1.44  fof(f125,plain,(
% 7.26/1.44    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_2(sK7,sK4,sK6) | ~v1_funct_1(sK7)),
% 7.26/1.44    inference(cnf_transformation,[],[f71])).
% 7.26/1.44  
% 7.26/1.44  fof(f120,plain,(
% 7.26/1.44    v1_funct_1(sK7)),
% 7.26/1.44    inference(cnf_transformation,[],[f71])).
% 7.26/1.44  
% 7.26/1.44  fof(f3,axiom,(
% 7.26/1.44    v1_xboole_0(k1_xboole_0)),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f77,plain,(
% 7.26/1.44    v1_xboole_0(k1_xboole_0)),
% 7.26/1.44    inference(cnf_transformation,[],[f3])).
% 7.26/1.44  
% 7.26/1.44  fof(f110,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.44    inference(cnf_transformation,[],[f67])).
% 7.26/1.44  
% 7.26/1.44  fof(f121,plain,(
% 7.26/1.44    v1_funct_2(sK7,sK4,sK5)),
% 7.26/1.44    inference(cnf_transformation,[],[f71])).
% 7.26/1.44  
% 7.26/1.44  fof(f2,axiom,(
% 7.26/1.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f31,plain,(
% 7.26/1.44    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.26/1.44    inference(ennf_transformation,[],[f2])).
% 7.26/1.44  
% 7.26/1.44  fof(f55,plain,(
% 7.26/1.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.44    inference(nnf_transformation,[],[f31])).
% 7.26/1.44  
% 7.26/1.44  fof(f56,plain,(
% 7.26/1.44    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.44    inference(rectify,[],[f55])).
% 7.26/1.44  
% 7.26/1.44  fof(f57,plain,(
% 7.26/1.44    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.26/1.44    introduced(choice_axiom,[])).
% 7.26/1.44  
% 7.26/1.44  fof(f58,plain,(
% 7.26/1.44    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f56,f57])).
% 7.26/1.44  
% 7.26/1.44  fof(f75,plain,(
% 7.26/1.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f58])).
% 7.26/1.44  
% 7.26/1.44  fof(f1,axiom,(
% 7.26/1.44    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f51,plain,(
% 7.26/1.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.44    inference(nnf_transformation,[],[f1])).
% 7.26/1.44  
% 7.26/1.44  fof(f52,plain,(
% 7.26/1.44    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.44    inference(rectify,[],[f51])).
% 7.26/1.44  
% 7.26/1.44  fof(f53,plain,(
% 7.26/1.44    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.26/1.44    introduced(choice_axiom,[])).
% 7.26/1.44  
% 7.26/1.44  fof(f54,plain,(
% 7.26/1.44    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f52,f53])).
% 7.26/1.44  
% 7.26/1.44  fof(f72,plain,(
% 7.26/1.44    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f54])).
% 7.26/1.44  
% 7.26/1.44  fof(f6,axiom,(
% 7.26/1.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f61,plain,(
% 7.26/1.44    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.44    inference(nnf_transformation,[],[f6])).
% 7.26/1.44  
% 7.26/1.44  fof(f62,plain,(
% 7.26/1.44    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.44    inference(flattening,[],[f61])).
% 7.26/1.44  
% 7.26/1.44  fof(f84,plain,(
% 7.26/1.44    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f62])).
% 7.26/1.44  
% 7.26/1.44  fof(f14,axiom,(
% 7.26/1.44    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f38,plain,(
% 7.26/1.44    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.26/1.44    inference(ennf_transformation,[],[f14])).
% 7.26/1.44  
% 7.26/1.44  fof(f96,plain,(
% 7.26/1.44    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f38])).
% 7.26/1.44  
% 7.26/1.44  fof(f22,axiom,(
% 7.26/1.44    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f45,plain,(
% 7.26/1.44    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.26/1.44    inference(ennf_transformation,[],[f22])).
% 7.26/1.44  
% 7.26/1.44  fof(f108,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f45])).
% 7.26/1.44  
% 7.26/1.44  fof(f82,plain,(
% 7.26/1.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.26/1.44    inference(cnf_transformation,[],[f62])).
% 7.26/1.44  
% 7.26/1.44  fof(f127,plain,(
% 7.26/1.44    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.26/1.44    inference(equality_resolution,[],[f82])).
% 7.26/1.44  
% 7.26/1.44  fof(f98,plain,(
% 7.26/1.44    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.26/1.44    inference(cnf_transformation,[],[f65])).
% 7.26/1.44  
% 7.26/1.44  fof(f74,plain,(
% 7.26/1.44    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f58])).
% 7.26/1.44  
% 7.26/1.44  fof(f10,axiom,(
% 7.26/1.44    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f63,plain,(
% 7.26/1.44    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.26/1.44    inference(nnf_transformation,[],[f10])).
% 7.26/1.44  
% 7.26/1.44  fof(f64,plain,(
% 7.26/1.44    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.26/1.44    inference(flattening,[],[f63])).
% 7.26/1.44  
% 7.26/1.44  fof(f90,plain,(
% 7.26/1.44    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.26/1.44    inference(cnf_transformation,[],[f64])).
% 7.26/1.44  
% 7.26/1.44  fof(f130,plain,(
% 7.26/1.44    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.26/1.44    inference(equality_resolution,[],[f90])).
% 7.26/1.44  
% 7.26/1.44  fof(f92,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f36])).
% 7.26/1.44  
% 7.26/1.44  fof(f91,plain,(
% 7.26/1.44    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.26/1.44    inference(cnf_transformation,[],[f64])).
% 7.26/1.44  
% 7.26/1.44  fof(f129,plain,(
% 7.26/1.44    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.26/1.44    inference(equality_resolution,[],[f91])).
% 7.26/1.44  
% 7.26/1.44  fof(f7,axiom,(
% 7.26/1.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f85,plain,(
% 7.26/1.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f7])).
% 7.26/1.44  
% 7.26/1.44  fof(f124,plain,(
% 7.26/1.44    k1_xboole_0 = sK4 | k1_xboole_0 != sK5),
% 7.26/1.44    inference(cnf_transformation,[],[f71])).
% 7.26/1.44  
% 7.26/1.44  fof(f4,axiom,(
% 7.26/1.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f32,plain,(
% 7.26/1.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.26/1.44    inference(ennf_transformation,[],[f4])).
% 7.26/1.44  
% 7.26/1.44  fof(f78,plain,(
% 7.26/1.44    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f32])).
% 7.26/1.44  
% 7.26/1.44  fof(f25,axiom,(
% 7.26/1.44    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.44  
% 7.26/1.44  fof(f29,plain,(
% 7.26/1.44    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    inference(pure_predicate_removal,[],[f25])).
% 7.26/1.44  
% 7.26/1.44  fof(f30,plain,(
% 7.26/1.44    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    inference(pure_predicate_removal,[],[f29])).
% 7.26/1.44  
% 7.26/1.44  fof(f68,plain,(
% 7.26/1.44    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.26/1.44    introduced(choice_axiom,[])).
% 7.26/1.44  
% 7.26/1.44  fof(f69,plain,(
% 7.26/1.44    ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1) & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f68])).
% 7.26/1.44  
% 7.26/1.44  fof(f116,plain,(
% 7.26/1.44    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.44    inference(cnf_transformation,[],[f69])).
% 7.26/1.44  
% 7.26/1.44  fof(f111,plain,(
% 7.26/1.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.44    inference(cnf_transformation,[],[f67])).
% 7.26/1.44  
% 7.26/1.44  fof(f135,plain,(
% 7.26/1.44    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.26/1.44    inference(equality_resolution,[],[f111])).
% 7.26/1.44  
% 7.26/1.44  fof(f119,plain,(
% 7.26/1.44    ( ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1)) )),
% 7.26/1.44    inference(cnf_transformation,[],[f69])).
% 7.26/1.44  
% 7.26/1.44  cnf(c_20,plain,
% 7.26/1.44      ( ~ r1_tarski(X0,X1)
% 7.26/1.44      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 7.26/1.44      inference(cnf_transformation,[],[f93]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2559,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.44      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_22,plain,
% 7.26/1.44      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 7.26/1.44      inference(cnf_transformation,[],[f94]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2557,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.44      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_51,negated_conjecture,
% 7.26/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.26/1.44      inference(cnf_transformation,[],[f122]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2543,plain,
% 7.26/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_25,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.26/1.44      inference(cnf_transformation,[],[f97]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2555,plain,
% 7.26/1.44      ( m1_subset_1(X0,X1) != iProver_top
% 7.26/1.44      | r2_hidden(X0,X1) = iProver_top
% 7.26/1.44      | v1_xboole_0(X1) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6820,plain,
% 7.26/1.44      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 7.26/1.44      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2543,c_2555]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_23,plain,
% 7.26/1.44      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.26/1.44      inference(cnf_transformation,[],[f95]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2556,plain,
% 7.26/1.44      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_7022,plain,
% 7.26/1.44      ( r2_hidden(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 7.26/1.44      inference(forward_subsumption_resolution,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_6820,c_2556]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_26,plain,
% 7.26/1.44      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.26/1.44      inference(cnf_transformation,[],[f99]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2554,plain,
% 7.26/1.44      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.26/1.44      | r1_tarski(X0,X1) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_28,plain,
% 7.26/1.44      ( m1_subset_1(X0,X1)
% 7.26/1.44      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.26/1.44      | ~ r2_hidden(X0,X2) ),
% 7.26/1.44      inference(cnf_transformation,[],[f100]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2552,plain,
% 7.26/1.44      ( m1_subset_1(X0,X1) = iProver_top
% 7.26/1.44      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.44      | r2_hidden(X0,X2) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_7508,plain,
% 7.26/1.44      ( m1_subset_1(X0,X1) = iProver_top
% 7.26/1.44      | r1_tarski(X2,X1) != iProver_top
% 7.26/1.44      | r2_hidden(X0,X2) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2554,c_2552]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_35043,plain,
% 7.26/1.44      ( m1_subset_1(sK7,X0) = iProver_top
% 7.26/1.44      | r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)),X0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_7022,c_7508]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_36344,plain,
% 7.26/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(X0)) = iProver_top
% 7.26/1.44      | r1_tarski(k2_zfmisc_1(sK4,sK5),X0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2557,c_35043]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_37041,plain,
% 7.26/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,X0))) = iProver_top
% 7.26/1.44      | r1_tarski(sK5,X0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2559,c_36344]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_50,negated_conjecture,
% 7.26/1.44      ( r1_tarski(sK5,sK6) ),
% 7.26/1.44      inference(cnf_transformation,[],[f123]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2544,plain,
% 7.26/1.44      ( r1_tarski(sK5,sK6) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_37,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.44      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.26/1.44      inference(cnf_transformation,[],[f109]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2547,plain,
% 7.26/1.44      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.26/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_38146,plain,
% 7.26/1.44      ( k1_relset_1(sK4,X0,sK7) = k1_relat_1(sK7)
% 7.26/1.44      | r1_tarski(sK5,X0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_37041,c_2547]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_39463,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK6,sK7) = k1_relat_1(sK7) ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2544,c_38146]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_41,plain,
% 7.26/1.44      ( v1_funct_2(X0,X1,X2)
% 7.26/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.44      | k1_relset_1(X1,X2,X0) != X1
% 7.26/1.44      | k1_xboole_0 = X2 ),
% 7.26/1.44      inference(cnf_transformation,[],[f112]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_48,negated_conjecture,
% 7.26/1.44      ( ~ v1_funct_2(sK7,sK4,sK6)
% 7.26/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 7.26/1.44      | ~ v1_funct_1(sK7) ),
% 7.26/1.44      inference(cnf_transformation,[],[f125]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_53,negated_conjecture,
% 7.26/1.44      ( v1_funct_1(sK7) ),
% 7.26/1.44      inference(cnf_transformation,[],[f120]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_265,plain,
% 7.26/1.44      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 7.26/1.44      | ~ v1_funct_2(sK7,sK4,sK6) ),
% 7.26/1.44      inference(global_propositional_subsumption,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_48,c_53]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_266,negated_conjecture,
% 7.26/1.44      ( ~ v1_funct_2(sK7,sK4,sK6)
% 7.26/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
% 7.26/1.44      inference(renaming,[status(thm)],[c_265]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_946,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.44      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 7.26/1.44      | k1_relset_1(X1,X2,X0) != X1
% 7.26/1.44      | sK6 != X2
% 7.26/1.44      | sK4 != X1
% 7.26/1.44      | sK7 != X0
% 7.26/1.44      | k1_xboole_0 = X2 ),
% 7.26/1.44      inference(resolution_lifted,[status(thm)],[c_41,c_266]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_947,plain,
% 7.26/1.44      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 7.26/1.44      | k1_relset_1(sK4,sK6,sK7) != sK4
% 7.26/1.44      | k1_xboole_0 = sK6 ),
% 7.26/1.44      inference(unflattening,[status(thm)],[c_946]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2536,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK6,sK7) != sK4
% 7.26/1.44      | k1_xboole_0 = sK6
% 7.26/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_39467,plain,
% 7.26/1.44      ( k1_relat_1(sK7) != sK4
% 7.26/1.44      | sK6 = k1_xboole_0
% 7.26/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
% 7.26/1.44      inference(demodulation,[status(thm)],[c_39463,c_2536]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5,plain,
% 7.26/1.44      ( v1_xboole_0(k1_xboole_0) ),
% 7.26/1.44      inference(cnf_transformation,[],[f77]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_156,plain,
% 7.26/1.44      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_948,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK6,sK7) != sK4
% 7.26/1.44      | k1_xboole_0 = sK6
% 7.26/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_1593,plain,( X0 = X0 ),theory(equality) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3069,plain,
% 7.26/1.44      ( sK4 = sK4 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1593]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_1595,plain,
% 7.26/1.44      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.26/1.44      theory(equality) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3084,plain,
% 7.26/1.44      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1595]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3085,plain,
% 7.26/1.44      ( sK5 != X0
% 7.26/1.44      | v1_xboole_0(X0) != iProver_top
% 7.26/1.44      | v1_xboole_0(sK5) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_3084]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3087,plain,
% 7.26/1.44      ( sK5 != k1_xboole_0
% 7.26/1.44      | v1_xboole_0(sK5) = iProver_top
% 7.26/1.44      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_3085]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4263,plain,
% 7.26/1.44      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1595]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4264,plain,
% 7.26/1.44      ( sK6 != X0
% 7.26/1.44      | v1_xboole_0(X0) != iProver_top
% 7.26/1.44      | v1_xboole_0(sK6) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_4263]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4266,plain,
% 7.26/1.44      ( sK6 != k1_xboole_0
% 7.26/1.44      | v1_xboole_0(sK6) = iProver_top
% 7.26/1.44      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_4264]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4423,plain,
% 7.26/1.44      ( sK6 = sK6 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1593]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_43,plain,
% 7.26/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.26/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.44      | k1_relset_1(X1,X2,X0) = X1
% 7.26/1.44      | k1_xboole_0 = X2 ),
% 7.26/1.44      inference(cnf_transformation,[],[f110]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_52,negated_conjecture,
% 7.26/1.44      ( v1_funct_2(sK7,sK4,sK5) ),
% 7.26/1.44      inference(cnf_transformation,[],[f121]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_959,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.44      | k1_relset_1(X1,X2,X0) = X1
% 7.26/1.44      | sK5 != X2
% 7.26/1.44      | sK4 != X1
% 7.26/1.44      | sK7 != X0
% 7.26/1.44      | k1_xboole_0 = X2 ),
% 7.26/1.44      inference(resolution_lifted,[status(thm)],[c_43,c_52]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_960,plain,
% 7.26/1.44      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 7.26/1.44      | k1_relset_1(sK4,sK5,sK7) = sK4
% 7.26/1.44      | k1_xboole_0 = sK5 ),
% 7.26/1.44      inference(unflattening,[status(thm)],[c_959]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_962,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 7.26/1.44      inference(global_propositional_subsumption,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_960,c_51]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4871,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2543,c_2547]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5225,plain,
% 7.26/1.44      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_962,c_4871]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_1594,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4278,plain,
% 7.26/1.44      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1594]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6506,plain,
% 7.26/1.44      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_4278]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6507,plain,
% 7.26/1.44      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_6506]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4227,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK6,sK7) != X0
% 7.26/1.44      | k1_relset_1(sK4,sK6,sK7) = sK4
% 7.26/1.44      | sK4 != X0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1594]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6990,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK6,sK7) != k1_relat_1(sK7)
% 7.26/1.44      | k1_relset_1(sK4,sK6,sK7) = sK4
% 7.26/1.44      | sK4 != k1_relat_1(sK7) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_4227]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.26/1.44      inference(cnf_transformation,[],[f75]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2572,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) = iProver_top
% 7.26/1.44      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_1,plain,
% 7.26/1.44      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.26/1.44      inference(cnf_transformation,[],[f72]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2574,plain,
% 7.26/1.44      ( r2_hidden(X0,X1) != iProver_top
% 7.26/1.44      | v1_xboole_0(X1) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4564,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2572,c_2574]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_10,plain,
% 7.26/1.44      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.26/1.44      inference(cnf_transformation,[],[f84]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2565,plain,
% 7.26/1.44      ( X0 = X1
% 7.26/1.44      | r1_tarski(X1,X0) != iProver_top
% 7.26/1.44      | r1_tarski(X0,X1) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6866,plain,
% 7.26/1.44      ( sK5 = sK6 | r1_tarski(sK6,sK5) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2544,c_2565]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6977,plain,
% 7.26/1.44      ( sK5 = sK6 | v1_xboole_0(sK6) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_4564,c_6866]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_980,plain,
% 7.26/1.44      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 7.26/1.44      | sK5 != sK6
% 7.26/1.44      | sK4 != sK4
% 7.26/1.44      | sK7 != sK7 ),
% 7.26/1.44      inference(resolution_lifted,[status(thm)],[c_266,c_52]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_981,plain,
% 7.26/1.44      ( sK5 != sK6
% 7.26/1.44      | sK4 != sK4
% 7.26/1.44      | sK7 != sK7
% 7.26/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2909,plain,
% 7.26/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 7.26/1.44      | ~ r1_tarski(sK7,k2_zfmisc_1(sK4,sK6)) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_26]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2910,plain,
% 7.26/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) = iProver_top
% 7.26/1.44      | r1_tarski(sK7,k2_zfmisc_1(sK4,sK6)) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_2909]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3033,plain,
% 7.26/1.44      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK6))
% 7.26/1.44      | r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_3]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3040,plain,
% 7.26/1.44      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK6)) = iProver_top
% 7.26/1.44      | r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_3033]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3352,plain,
% 7.26/1.44      ( ~ r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7)
% 7.26/1.44      | ~ v1_xboole_0(sK7) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3353,plain,
% 7.26/1.44      ( r2_hidden(sK1(sK7,k2_zfmisc_1(sK4,sK6)),sK7) != iProver_top
% 7.26/1.44      | v1_xboole_0(sK7) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_3352]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3395,plain,
% 7.26/1.44      ( sK7 = sK7 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1593]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_24,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.44      | ~ v1_xboole_0(X1)
% 7.26/1.44      | v1_xboole_0(X0) ),
% 7.26/1.44      inference(cnf_transformation,[],[f96]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_377,plain,
% 7.26/1.44      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.26/1.44      inference(prop_impl,[status(thm)],[c_26]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_378,plain,
% 7.26/1.44      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.26/1.44      inference(renaming,[status(thm)],[c_377]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_458,plain,
% 7.26/1.44      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 7.26/1.44      inference(bin_hyper_res,[status(thm)],[c_24,c_378]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2542,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.44      | v1_xboole_0(X1) != iProver_top
% 7.26/1.44      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4464,plain,
% 7.26/1.44      ( v1_xboole_0(sK5) = iProver_top
% 7.26/1.44      | v1_xboole_0(sK6) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2544,c_2542]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_36,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.44      | ~ v1_xboole_0(X2)
% 7.26/1.44      | v1_xboole_0(X0) ),
% 7.26/1.44      inference(cnf_transformation,[],[f108]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2548,plain,
% 7.26/1.44      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.26/1.44      | v1_xboole_0(X2) != iProver_top
% 7.26/1.44      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5594,plain,
% 7.26/1.44      ( v1_xboole_0(sK5) != iProver_top
% 7.26/1.44      | v1_xboole_0(sK7) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2543,c_2548]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_7026,plain,
% 7.26/1.44      ( v1_xboole_0(sK6) != iProver_top ),
% 7.26/1.44      inference(global_propositional_subsumption,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_6977,c_981,c_2910,c_3040,c_3069,c_3353,c_3395,c_4464,
% 7.26/1.44                 c_5594]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3061,plain,
% 7.26/1.44      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1594]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6057,plain,
% 7.26/1.44      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_3061]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_11541,plain,
% 7.26/1.44      ( k1_relat_1(sK7) != sK4 | sK4 = k1_relat_1(sK7) | sK4 != sK4 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_6057]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_12,plain,
% 7.26/1.44      ( r1_tarski(X0,X0) ),
% 7.26/1.44      inference(cnf_transformation,[],[f127]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2564,plain,
% 7.26/1.44      ( r1_tarski(X0,X0) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5592,plain,
% 7.26/1.44      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.26/1.44      | v1_xboole_0(X2) != iProver_top
% 7.26/1.44      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2554,c_2548]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_14867,plain,
% 7.26/1.44      ( v1_xboole_0(X0) != iProver_top
% 7.26/1.44      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2564,c_5592]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_27,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.26/1.44      inference(cnf_transformation,[],[f98]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2553,plain,
% 7.26/1.44      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.44      | r1_tarski(X0,X1) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4032,plain,
% 7.26/1.44      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2543,c_2553]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4,plain,
% 7.26/1.44      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.26/1.44      inference(cnf_transformation,[],[f74]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2571,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.44      | r2_hidden(X2,X0) != iProver_top
% 7.26/1.44      | r2_hidden(X2,X1) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_7427,plain,
% 7.26/1.44      ( r2_hidden(X0,k2_zfmisc_1(sK4,sK5)) = iProver_top
% 7.26/1.44      | r2_hidden(X0,sK7) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_4032,c_2571]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_7680,plain,
% 7.26/1.44      ( r2_hidden(X0,sK7) != iProver_top
% 7.26/1.44      | v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_7427,c_2574]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_14941,plain,
% 7.26/1.44      ( r2_hidden(X0,sK7) != iProver_top
% 7.26/1.44      | v1_xboole_0(sK5) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_14867,c_7680]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_15447,plain,
% 7.26/1.44      ( r1_tarski(sK7,X0) = iProver_top
% 7.26/1.44      | v1_xboole_0(sK5) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2572,c_14941]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_18,plain,
% 7.26/1.44      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.26/1.44      inference(cnf_transformation,[],[f130]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_21,plain,
% 7.26/1.44      ( ~ r1_tarski(X0,X1)
% 7.26/1.44      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 7.26/1.44      inference(cnf_transformation,[],[f92]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2558,plain,
% 7.26/1.44      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.44      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5627,plain,
% 7.26/1.44      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.26/1.44      | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_18,c_2558]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_17,plain,
% 7.26/1.44      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.26/1.44      inference(cnf_transformation,[],[f129]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5836,plain,
% 7.26/1.44      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.26/1.44      | r1_tarski(k2_zfmisc_1(X1,X0),k1_xboole_0) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_17,c_2559]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_13,plain,
% 7.26/1.44      ( r1_tarski(k1_xboole_0,X0) ),
% 7.26/1.44      inference(cnf_transformation,[],[f85]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2563,plain,
% 7.26/1.44      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6862,plain,
% 7.26/1.44      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2563,c_2565]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_9011,plain,
% 7.26/1.44      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 7.26/1.44      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_5836,c_6862]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_10248,plain,
% 7.26/1.44      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)) = k1_xboole_0
% 7.26/1.44      | r1_tarski(X2,k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_5836,c_9011]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_12690,plain,
% 7.26/1.44      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))) = k1_xboole_0
% 7.26/1.44      | r1_tarski(X3,k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_5836,c_10248]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_15347,plain,
% 7.26/1.44      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,X4)))) = k1_xboole_0
% 7.26/1.44      | r1_tarski(X3,k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_5627,c_12690]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_33989,plain,
% 7.26/1.44      ( k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(sK7,X3)))) = k1_xboole_0
% 7.26/1.44      | v1_xboole_0(sK5) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_15447,c_15347]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_49,negated_conjecture,
% 7.26/1.44      ( k1_xboole_0 != sK5 | k1_xboole_0 = sK4 ),
% 7.26/1.44      inference(cnf_transformation,[],[f124]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2979,plain,
% 7.26/1.44      ( sK4 != X0 | sK4 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1594]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3068,plain,
% 7.26/1.44      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_2979]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6,plain,
% 7.26/1.44      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.26/1.44      inference(cnf_transformation,[],[f78]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5787,plain,
% 7.26/1.44      ( ~ v1_xboole_0(sK5) | k1_xboole_0 = sK5 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_6]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5788,plain,
% 7.26/1.44      ( k1_xboole_0 = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_5787]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_47,plain,
% 7.26/1.44      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.26/1.44      inference(cnf_transformation,[],[f116]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2545,plain,
% 7.26/1.44      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_3456,plain,
% 7.26/1.44      ( m1_subset_1(sK3(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_17,c_2545]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4034,plain,
% 7.26/1.44      ( r1_tarski(sK3(X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_3456,c_2553]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4467,plain,
% 7.26/1.44      ( v1_xboole_0(sK3(X0,k1_xboole_0)) = iProver_top
% 7.26/1.44      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_4034,c_2542]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6272,plain,
% 7.26/1.44      ( v1_xboole_0(sK3(X0,k1_xboole_0)) = iProver_top ),
% 7.26/1.44      inference(global_propositional_subsumption,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_4467,c_156]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_2569,plain,
% 7.26/1.44      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6281,plain,
% 7.26/1.44      ( sK3(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_6272,c_2569]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_4870,plain,
% 7.26/1.44      ( k1_relset_1(X0,X1,sK3(X0,X1)) = k1_relat_1(sK3(X0,X1)) ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_2545,c_2547]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_42,plain,
% 7.26/1.44      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.26/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.26/1.44      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.26/1.44      inference(cnf_transformation,[],[f135]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_44,plain,
% 7.26/1.44      ( v1_funct_2(sK3(X0,X1),X0,X1) ),
% 7.26/1.44      inference(cnf_transformation,[],[f119]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_894,plain,
% 7.26/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.26/1.44      | X2 != X1
% 7.26/1.44      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 7.26/1.44      | sK3(X3,X2) != X0
% 7.26/1.44      | k1_xboole_0 != X3 ),
% 7.26/1.44      inference(resolution_lifted,[status(thm)],[c_42,c_44]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_895,plain,
% 7.26/1.44      ( ~ m1_subset_1(sK3(k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 7.26/1.44      | k1_relset_1(k1_xboole_0,X0,sK3(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.26/1.44      inference(unflattening,[status(thm)],[c_894]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_903,plain,
% 7.26/1.44      ( k1_relset_1(k1_xboole_0,X0,sK3(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.26/1.44      inference(forward_subsumption_resolution,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_895,c_47]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_5425,plain,
% 7.26/1.44      ( k1_relat_1(sK3(k1_xboole_0,X0)) = k1_xboole_0 ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_4870,c_903]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6464,plain,
% 7.26/1.44      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_6281,c_5425]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6991,plain,
% 7.26/1.44      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
% 7.26/1.44      | k1_relset_1(sK4,sK6,sK7) = k1_relat_1(sK7) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_37]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6992,plain,
% 7.26/1.44      ( k1_relset_1(sK4,sK6,sK7) = k1_relat_1(sK7)
% 7.26/1.44      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_6991]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_6860,plain,
% 7.26/1.44      ( X0 = X1
% 7.26/1.44      | r1_tarski(X0,X1) != iProver_top
% 7.26/1.44      | v1_xboole_0(X1) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_4564,c_2565]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_15538,plain,
% 7.26/1.44      ( sK7 = X0
% 7.26/1.44      | v1_xboole_0(X0) != iProver_top
% 7.26/1.44      | v1_xboole_0(sK5) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_15447,c_6860]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_15656,plain,
% 7.26/1.44      ( sK7 = k1_xboole_0
% 7.26/1.44      | v1_xboole_0(sK5) != iProver_top
% 7.26/1.44      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_15538]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_11542,plain,
% 7.26/1.44      ( k1_relat_1(sK7) != X0 | sK4 != X0 | sK4 = k1_relat_1(sK7) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_3061]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_26384,plain,
% 7.26/1.44      ( k1_relat_1(sK7) != k1_relat_1(X0)
% 7.26/1.44      | sK4 != k1_relat_1(X0)
% 7.26/1.44      | sK4 = k1_relat_1(sK7) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_11542]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_26386,plain,
% 7.26/1.44      ( k1_relat_1(sK7) != k1_relat_1(k1_xboole_0)
% 7.26/1.44      | sK4 = k1_relat_1(sK7)
% 7.26/1.44      | sK4 != k1_relat_1(k1_xboole_0) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_26384]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_1603,plain,
% 7.26/1.44      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 7.26/1.44      theory(equality) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_26385,plain,
% 7.26/1.44      ( k1_relat_1(sK7) = k1_relat_1(X0) | sK7 != X0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_1603]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_26387,plain,
% 7.26/1.44      ( k1_relat_1(sK7) = k1_relat_1(k1_xboole_0) | sK7 != k1_xboole_0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_26385]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_34585,plain,
% 7.26/1.44      ( k1_relat_1(X0) != X1 | sK4 != X1 | sK4 = k1_relat_1(X0) ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_3061]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_34596,plain,
% 7.26/1.44      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 7.26/1.44      | sK4 = k1_relat_1(k1_xboole_0)
% 7.26/1.44      | sK4 != k1_xboole_0 ),
% 7.26/1.44      inference(instantiation,[status(thm)],[c_34585]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_34673,plain,
% 7.26/1.44      ( v1_xboole_0(sK5) != iProver_top ),
% 7.26/1.44      inference(global_propositional_subsumption,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_33989,c_49,c_156,c_948,c_981,c_2910,c_3040,c_3068,
% 7.26/1.44                 c_3069,c_3353,c_3395,c_4266,c_4423,c_4464,c_5594,c_5788,
% 7.26/1.44                 c_6464,c_6507,c_6977,c_6990,c_6992,c_15656,c_26386,
% 7.26/1.44                 c_26387,c_34596]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_39863,plain,
% 7.26/1.44      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) != iProver_top ),
% 7.26/1.44      inference(global_propositional_subsumption,
% 7.26/1.44                [status(thm)],
% 7.26/1.44                [c_39467,c_49,c_156,c_948,c_981,c_2910,c_3040,c_3068,
% 7.26/1.44                 c_3069,c_3087,c_3353,c_3395,c_4266,c_4423,c_4464,c_5225,
% 7.26/1.44                 c_5594,c_5788,c_6464,c_6507,c_6977,c_6990,c_6992,
% 7.26/1.44                 c_11541,c_15656,c_26386,c_26387,c_34596,c_39463]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_39869,plain,
% 7.26/1.44      ( r1_tarski(sK5,sK6) != iProver_top ),
% 7.26/1.44      inference(superposition,[status(thm)],[c_37041,c_39863]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(c_57,plain,
% 7.26/1.44      ( r1_tarski(sK5,sK6) = iProver_top ),
% 7.26/1.44      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.26/1.44  
% 7.26/1.44  cnf(contradiction,plain,
% 7.26/1.44      ( $false ),
% 7.26/1.44      inference(minisat,[status(thm)],[c_39869,c_57]) ).
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.44  
% 7.26/1.44  ------                               Statistics
% 7.26/1.44  
% 7.26/1.44  ------ General
% 7.26/1.44  
% 7.26/1.44  abstr_ref_over_cycles:                  0
% 7.26/1.44  abstr_ref_under_cycles:                 0
% 7.26/1.44  gc_basic_clause_elim:                   0
% 7.26/1.44  forced_gc_time:                         0
% 7.26/1.44  parsing_time:                           0.013
% 7.26/1.44  unif_index_cands_time:                  0.
% 7.26/1.44  unif_index_add_time:                    0.
% 7.26/1.44  orderings_time:                         0.
% 7.26/1.44  out_proof_time:                         0.016
% 7.26/1.44  total_time:                             0.843
% 7.26/1.44  num_of_symbols:                         55
% 7.26/1.44  num_of_terms:                           27210
% 7.26/1.44  
% 7.26/1.44  ------ Preprocessing
% 7.26/1.44  
% 7.26/1.44  num_of_splits:                          0
% 7.26/1.44  num_of_split_atoms:                     0
% 7.26/1.44  num_of_reused_defs:                     0
% 7.26/1.44  num_eq_ax_congr_red:                    28
% 7.26/1.44  num_of_sem_filtered_clauses:            4
% 7.26/1.44  num_of_subtypes:                        0
% 7.26/1.44  monotx_restored_types:                  0
% 7.26/1.44  sat_num_of_epr_types:                   0
% 7.26/1.44  sat_num_of_non_cyclic_types:            0
% 7.26/1.44  sat_guarded_non_collapsed_types:        0
% 7.26/1.44  num_pure_diseq_elim:                    0
% 7.26/1.44  simp_replaced_by:                       0
% 7.26/1.44  res_preprocessed:                       240
% 7.26/1.44  prep_upred:                             0
% 7.26/1.44  prep_unflattend:                        84
% 7.26/1.44  smt_new_axioms:                         0
% 7.26/1.44  pred_elim_cands:                        6
% 7.26/1.44  pred_elim:                              1
% 7.26/1.44  pred_elim_cl:                           -2
% 7.26/1.44  pred_elim_cycles:                       6
% 7.26/1.44  merged_defs:                            8
% 7.26/1.44  merged_defs_ncl:                        0
% 7.26/1.44  bin_hyper_res:                          10
% 7.26/1.44  prep_cycles:                            4
% 7.26/1.44  pred_elim_time:                         0.012
% 7.26/1.44  splitting_time:                         0.
% 7.26/1.44  sem_filter_time:                        0.
% 7.26/1.44  monotx_time:                            0.001
% 7.26/1.44  subtype_inf_time:                       0.
% 7.26/1.44  
% 7.26/1.44  ------ Problem properties
% 7.26/1.44  
% 7.26/1.44  clauses:                                52
% 7.26/1.44  conjectures:                            3
% 7.26/1.44  epr:                                    15
% 7.26/1.44  horn:                                   42
% 7.26/1.44  ground:                                 13
% 7.26/1.44  unary:                                  15
% 7.26/1.44  binary:                                 21
% 7.26/1.44  lits:                                   109
% 7.26/1.44  lits_eq:                                38
% 7.26/1.44  fd_pure:                                0
% 7.26/1.44  fd_pseudo:                              0
% 7.26/1.44  fd_cond:                                4
% 7.26/1.44  fd_pseudo_cond:                         2
% 7.26/1.44  ac_symbols:                             0
% 7.26/1.44  
% 7.26/1.44  ------ Propositional Solver
% 7.26/1.44  
% 7.26/1.44  prop_solver_calls:                      31
% 7.26/1.44  prop_fast_solver_calls:                 2222
% 7.26/1.44  smt_solver_calls:                       0
% 7.26/1.44  smt_fast_solver_calls:                  0
% 7.26/1.44  prop_num_of_clauses:                    14453
% 7.26/1.44  prop_preprocess_simplified:             25941
% 7.26/1.44  prop_fo_subsumed:                       45
% 7.26/1.44  prop_solver_time:                       0.
% 7.26/1.44  smt_solver_time:                        0.
% 7.26/1.44  smt_fast_solver_time:                   0.
% 7.26/1.44  prop_fast_solver_time:                  0.
% 7.26/1.44  prop_unsat_core_time:                   0.001
% 7.26/1.44  
% 7.26/1.44  ------ QBF
% 7.26/1.44  
% 7.26/1.44  qbf_q_res:                              0
% 7.26/1.44  qbf_num_tautologies:                    0
% 7.26/1.44  qbf_prep_cycles:                        0
% 7.26/1.44  
% 7.26/1.44  ------ BMC1
% 7.26/1.44  
% 7.26/1.44  bmc1_current_bound:                     -1
% 7.26/1.44  bmc1_last_solved_bound:                 -1
% 7.26/1.44  bmc1_unsat_core_size:                   -1
% 7.26/1.44  bmc1_unsat_core_parents_size:           -1
% 7.26/1.44  bmc1_merge_next_fun:                    0
% 7.26/1.44  bmc1_unsat_core_clauses_time:           0.
% 7.26/1.44  
% 7.26/1.44  ------ Instantiation
% 7.26/1.44  
% 7.26/1.44  inst_num_of_clauses:                    4150
% 7.26/1.44  inst_num_in_passive:                    689
% 7.26/1.44  inst_num_in_active:                     1705
% 7.26/1.44  inst_num_in_unprocessed:                1756
% 7.26/1.44  inst_num_of_loops:                      2090
% 7.26/1.44  inst_num_of_learning_restarts:          0
% 7.26/1.44  inst_num_moves_active_passive:          381
% 7.26/1.44  inst_lit_activity:                      0
% 7.26/1.44  inst_lit_activity_moves:                0
% 7.26/1.44  inst_num_tautologies:                   0
% 7.26/1.44  inst_num_prop_implied:                  0
% 7.26/1.44  inst_num_existing_simplified:           0
% 7.26/1.44  inst_num_eq_res_simplified:             0
% 7.26/1.44  inst_num_child_elim:                    0
% 7.26/1.44  inst_num_of_dismatching_blockings:      1827
% 7.26/1.44  inst_num_of_non_proper_insts:           4163
% 7.26/1.44  inst_num_of_duplicates:                 0
% 7.26/1.44  inst_inst_num_from_inst_to_res:         0
% 7.26/1.44  inst_dismatching_checking_time:         0.
% 7.26/1.44  
% 7.26/1.44  ------ Resolution
% 7.26/1.44  
% 7.26/1.44  res_num_of_clauses:                     0
% 7.26/1.44  res_num_in_passive:                     0
% 7.26/1.44  res_num_in_active:                      0
% 7.26/1.44  res_num_of_loops:                       244
% 7.26/1.44  res_forward_subset_subsumed:            322
% 7.26/1.44  res_backward_subset_subsumed:           0
% 7.26/1.44  res_forward_subsumed:                   0
% 7.26/1.44  res_backward_subsumed:                  0
% 7.26/1.44  res_forward_subsumption_resolution:     2
% 7.26/1.44  res_backward_subsumption_resolution:    0
% 7.26/1.44  res_clause_to_clause_subsumption:       8352
% 7.26/1.44  res_orphan_elimination:                 0
% 7.26/1.44  res_tautology_del:                      310
% 7.26/1.44  res_num_eq_res_simplified:              1
% 7.26/1.44  res_num_sel_changes:                    0
% 7.26/1.44  res_moves_from_active_to_pass:          0
% 7.26/1.44  
% 7.26/1.44  ------ Superposition
% 7.26/1.44  
% 7.26/1.44  sup_time_total:                         0.
% 7.26/1.44  sup_time_generating:                    0.
% 7.26/1.44  sup_time_sim_full:                      0.
% 7.26/1.44  sup_time_sim_immed:                     0.
% 7.26/1.44  
% 7.26/1.44  sup_num_of_clauses:                     850
% 7.26/1.44  sup_num_in_active:                      393
% 7.26/1.44  sup_num_in_passive:                     457
% 7.26/1.44  sup_num_of_loops:                       416
% 7.26/1.44  sup_fw_superposition:                   1104
% 7.26/1.44  sup_bw_superposition:                   492
% 7.26/1.44  sup_immediate_simplified:               356
% 7.26/1.44  sup_given_eliminated:                   1
% 7.26/1.44  comparisons_done:                       0
% 7.26/1.44  comparisons_avoided:                    5
% 7.26/1.44  
% 7.26/1.44  ------ Simplifications
% 7.26/1.44  
% 7.26/1.44  
% 7.26/1.44  sim_fw_subset_subsumed:                 66
% 7.26/1.44  sim_bw_subset_subsumed:                 14
% 7.26/1.44  sim_fw_subsumed:                        111
% 7.26/1.44  sim_bw_subsumed:                        8
% 7.26/1.44  sim_fw_subsumption_res:                 17
% 7.26/1.44  sim_bw_subsumption_res:                 0
% 7.26/1.44  sim_tautology_del:                      16
% 7.26/1.44  sim_eq_tautology_del:                   45
% 7.26/1.44  sim_eq_res_simp:                        1
% 7.26/1.44  sim_fw_demodulated:                     128
% 7.26/1.44  sim_bw_demodulated:                     17
% 7.26/1.44  sim_light_normalised:                   93
% 7.26/1.44  sim_joinable_taut:                      0
% 7.26/1.44  sim_joinable_simp:                      0
% 7.26/1.44  sim_ac_normalised:                      0
% 7.26/1.44  sim_smt_subsumption:                    0
% 7.26/1.44  
%------------------------------------------------------------------------------
