%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:33 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 983 expanded)
%              Number of clauses        :  155 ( 394 expanded)
%              Number of leaves         :   32 ( 192 expanded)
%              Depth                    :   17
%              Number of atoms          :  738 (4283 expanded)
%              Number of equality atoms :  339 (1393 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f46,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f47,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f65,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
        | ~ v1_funct_2(sK6,sK3,sK5)
        | ~ v1_funct_1(sK6) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
      | ~ v1_funct_2(sK6,sK3,sK5)
      | ~ v1_funct_1(sK6) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f47,f65])).

fof(f110,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f66])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f111,plain,(
    r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f66])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f56])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f23,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f113,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5)
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f66])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f112,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f60])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f109,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f42])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f121,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f105])).

fof(f92,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1762,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1767,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3638,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1762,c_1767])).

cnf(c_43,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1763,plain,
    ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3649,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3638,c_1763])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1780,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_330,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_329])).

cnf(c_402,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_330])).

cnf(c_1761,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_2912,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1761])).

cnf(c_5371,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_2912])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_140,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_38,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_41,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_46,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_235,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ v1_funct_2(sK6,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41,c_46])).

cnf(c_236,negated_conjecture,
    ( ~ v1_funct_2(sK6,sK3,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
    inference(renaming,[status(thm)],[c_235])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK5 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_236])).

cnf(c_638,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(sK3,sK5,sK6) != sK3
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_637])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1847,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(k1_relat_1(sK6),sK3)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1012,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1867,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_1868,plain,
    ( sK5 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1867])).

cnf(c_1870,plain,
    ( sK5 != k1_xboole_0
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1868])).

cnf(c_29,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_19,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_29,c_19])).

cnf(c_1759,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_2199,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1759])).

cnf(c_2200,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3)
    | ~ v1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2199])).

cnf(c_1011,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2085,plain,
    ( k1_relset_1(sK3,sK5,sK6) != X0
    | k1_relset_1(sK3,sK5,sK6) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_2384,plain,
    ( k1_relset_1(sK3,sK5,sK6) != k1_relat_1(sK6)
    | k1_relset_1(sK3,sK5,sK6) = sK3
    | sK3 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2085])).

cnf(c_21,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1773,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1775,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3019,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1775])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_403,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_17,c_330])).

cnf(c_1760,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_3114,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3019,c_1760])).

cnf(c_3117,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_3114])).

cnf(c_3118,plain,
    ( v1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3117])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2904,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3418,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2904])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2136,plain,
    ( r1_tarski(X0,sK5)
    | ~ r2_hidden(sK1(X0,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3421,plain,
    ( r1_tarski(sK5,sK5)
    | ~ r2_hidden(sK1(sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2137,plain,
    ( r1_tarski(X0,sK5)
    | r2_hidden(sK1(X0,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3419,plain,
    ( r1_tarski(sK5,sK5)
    | r2_hidden(sK1(sK5,sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_2903,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3569,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2903])).

cnf(c_3570,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_3651,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3649])).

cnf(c_1010,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3773,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_1779,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4511,plain,
    ( k1_relat_1(sK6) = sK3
    | r1_tarski(sK3,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2199,c_1779])).

cnf(c_42,negated_conjecture,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_13,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_127,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_128,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1838,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1941,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_2560,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2561,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2560])).

cnf(c_2563,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2561])).

cnf(c_40,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_45,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_650,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_45])).

cnf(c_651,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_650])).

cnf(c_653,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_651,c_44])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1768,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3844,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1762,c_1768])).

cnf(c_3940,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_653,c_3844])).

cnf(c_3971,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3972,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3971])).

cnf(c_25,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1772,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4422,plain,
    ( v1_relat_1(k6_relat_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1772])).

cnf(c_28,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_88,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4520,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4422,c_88])).

cnf(c_1783,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1785,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3053,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_1785])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k6_relat_1(X1),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1764,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k6_relat_1(X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3489,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | r1_tarski(k6_relat_1(sK3),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1764])).

cnf(c_3684,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3053,c_3489])).

cnf(c_3936,plain,
    ( k1_relat_1(sK6) = sK3
    | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3844,c_3684])).

cnf(c_4533,plain,
    ( k1_relat_1(sK6) = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4520,c_3936])).

cnf(c_4650,plain,
    ( k1_relat_1(sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4511,c_42,c_127,c_128,c_140,c_1941,c_2563,c_3773,c_3940,c_3972,c_4533])).

cnf(c_1937,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3930,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_4763,plain,
    ( k1_relat_1(sK6) != sK3
    | sK3 = k1_relat_1(sK6)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3930])).

cnf(c_5126,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_5612,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5371,c_42,c_127,c_128,c_140,c_638,c_1847,c_1870,c_1941,c_2200,c_2384,c_2563,c_3118,c_3418,c_3421,c_3419,c_3570,c_3651,c_3773,c_3940,c_3972,c_4533,c_4763,c_5126])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X1,k2_relset_1(X1,X2,X0))
    | ~ r1_tarski(k6_relat_1(X1),X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1765,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(X1,k2_relset_1(X1,X2,X0)) = iProver_top
    | r1_tarski(k6_relat_1(X1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3780,plain,
    ( r1_tarski(k6_relat_1(sK3),sK6) != iProver_top
    | r1_tarski(sK3,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1765])).

cnf(c_3784,plain,
    ( r1_tarski(k6_relat_1(sK3),sK6) != iProver_top
    | r1_tarski(sK3,k2_relat_1(sK6)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3780,c_3638])).

cnf(c_4081,plain,
    ( r1_tarski(sK3,k2_relat_1(sK6)) = iProver_top
    | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3053,c_3784])).

cnf(c_4512,plain,
    ( k2_relat_1(sK6) = sK3
    | r1_tarski(k2_relat_1(sK6),sK3) != iProver_top
    | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4081,c_1779])).

cnf(c_5072,plain,
    ( k2_relat_1(sK6) = sK3
    | v1_xboole_0(k6_relat_1(sK3)) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3053,c_4512])).

cnf(c_5154,plain,
    ( k2_relat_1(sK6) = sK3
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4520,c_5072])).

cnf(c_3102,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_xboole_0(k2_relat_1(sK6))
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3106,plain,
    ( v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3102])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1774,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4003,plain,
    ( sK4 = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3940,c_1774])).

cnf(c_4154,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4003,c_42,c_127,c_128,c_140,c_1941,c_2563,c_3773,c_3972])).

cnf(c_5157,plain,
    ( v1_xboole_0(k2_relat_1(sK6)) != iProver_top
    | k2_relat_1(sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5154,c_3106,c_3117,c_4154])).

cnf(c_5158,plain,
    ( k2_relat_1(sK6) = sK3
    | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5157])).

cnf(c_5614,plain,
    ( sK3 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5612,c_5158])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1770,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4655,plain,
    ( sK3 != k1_xboole_0
    | sK6 = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4650,c_1770])).

cnf(c_90,plain,
    ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_88])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_130,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_37,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK5 != X1
    | sK3 != k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_236])).

cnf(c_609,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_2020,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | ~ r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2333,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5))
    | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2831,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
    | ~ r1_tarski(k6_relat_1(k1_xboole_0),sK6)
    | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_1014,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2191,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK6)
    | X2 != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_2996,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_relat_1(k1_xboole_0),sK6)
    | k6_relat_1(k1_xboole_0) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_2191])).

cnf(c_2998,plain,
    ( r1_tarski(k6_relat_1(k1_xboole_0),sK6)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k6_relat_1(k1_xboole_0) != k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2996])).

cnf(c_3108,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK6)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_3110,plain,
    ( v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_26,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3501,plain,
    ( k6_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_1770])).

cnf(c_3504,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3501])).

cnf(c_4320,plain,
    ( ~ r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4807,plain,
    ( sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4655,c_90,c_127,c_128,c_130,c_5,c_609,c_1847,c_2020,c_2200,c_2333,c_2831,c_2998,c_3110,c_3117,c_3118,c_3504,c_3651,c_4320])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5614,c_4807,c_140])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n019.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 17:32:22 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.62/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.99  
% 3.62/0.99  ------  iProver source info
% 3.62/0.99  
% 3.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.99  git: non_committed_changes: false
% 3.62/0.99  git: last_make_outside_of_git: false
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  ------ Input Options
% 3.62/0.99  
% 3.62/0.99  --out_options                           all
% 3.62/0.99  --tptp_safe_out                         true
% 3.62/0.99  --problem_path                          ""
% 3.62/0.99  --include_path                          ""
% 3.62/0.99  --clausifier                            res/vclausify_rel
% 3.62/0.99  --clausifier_options                    ""
% 3.62/0.99  --stdin                                 false
% 3.62/0.99  --stats_out                             all
% 3.62/0.99  
% 3.62/0.99  ------ General Options
% 3.62/0.99  
% 3.62/0.99  --fof                                   false
% 3.62/0.99  --time_out_real                         305.
% 3.62/0.99  --time_out_virtual                      -1.
% 3.62/0.99  --symbol_type_check                     false
% 3.62/0.99  --clausify_out                          false
% 3.62/0.99  --sig_cnt_out                           false
% 3.62/0.99  --trig_cnt_out                          false
% 3.62/0.99  --trig_cnt_out_tolerance                1.
% 3.62/0.99  --trig_cnt_out_sk_spl                   false
% 3.62/0.99  --abstr_cl_out                          false
% 3.62/0.99  
% 3.62/0.99  ------ Global Options
% 3.62/0.99  
% 3.62/0.99  --schedule                              default
% 3.62/0.99  --add_important_lit                     false
% 3.62/0.99  --prop_solver_per_cl                    1000
% 3.62/0.99  --min_unsat_core                        false
% 3.62/0.99  --soft_assumptions                      false
% 3.62/0.99  --soft_lemma_size                       3
% 3.62/0.99  --prop_impl_unit_size                   0
% 3.62/0.99  --prop_impl_unit                        []
% 3.62/0.99  --share_sel_clauses                     true
% 3.62/0.99  --reset_solvers                         false
% 3.62/0.99  --bc_imp_inh                            [conj_cone]
% 3.62/0.99  --conj_cone_tolerance                   3.
% 3.62/0.99  --extra_neg_conj                        none
% 3.62/0.99  --large_theory_mode                     true
% 3.62/0.99  --prolific_symb_bound                   200
% 3.62/0.99  --lt_threshold                          2000
% 3.62/0.99  --clause_weak_htbl                      true
% 3.62/0.99  --gc_record_bc_elim                     false
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing Options
% 3.62/0.99  
% 3.62/0.99  --preprocessing_flag                    true
% 3.62/0.99  --time_out_prep_mult                    0.1
% 3.62/0.99  --splitting_mode                        input
% 3.62/0.99  --splitting_grd                         true
% 3.62/0.99  --splitting_cvd                         false
% 3.62/0.99  --splitting_cvd_svl                     false
% 3.62/0.99  --splitting_nvd                         32
% 3.62/0.99  --sub_typing                            true
% 3.62/0.99  --prep_gs_sim                           true
% 3.62/0.99  --prep_unflatten                        true
% 3.62/0.99  --prep_res_sim                          true
% 3.62/0.99  --prep_upred                            true
% 3.62/0.99  --prep_sem_filter                       exhaustive
% 3.62/0.99  --prep_sem_filter_out                   false
% 3.62/0.99  --pred_elim                             true
% 3.62/0.99  --res_sim_input                         true
% 3.62/0.99  --eq_ax_congr_red                       true
% 3.62/0.99  --pure_diseq_elim                       true
% 3.62/0.99  --brand_transform                       false
% 3.62/0.99  --non_eq_to_eq                          false
% 3.62/0.99  --prep_def_merge                        true
% 3.62/0.99  --prep_def_merge_prop_impl              false
% 3.62/0.99  --prep_def_merge_mbd                    true
% 3.62/0.99  --prep_def_merge_tr_red                 false
% 3.62/0.99  --prep_def_merge_tr_cl                  false
% 3.62/0.99  --smt_preprocessing                     true
% 3.62/0.99  --smt_ac_axioms                         fast
% 3.62/0.99  --preprocessed_out                      false
% 3.62/0.99  --preprocessed_stats                    false
% 3.62/0.99  
% 3.62/0.99  ------ Abstraction refinement Options
% 3.62/0.99  
% 3.62/0.99  --abstr_ref                             []
% 3.62/0.99  --abstr_ref_prep                        false
% 3.62/0.99  --abstr_ref_until_sat                   false
% 3.62/0.99  --abstr_ref_sig_restrict                funpre
% 3.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.99  --abstr_ref_under                       []
% 3.62/0.99  
% 3.62/0.99  ------ SAT Options
% 3.62/0.99  
% 3.62/0.99  --sat_mode                              false
% 3.62/0.99  --sat_fm_restart_options                ""
% 3.62/0.99  --sat_gr_def                            false
% 3.62/0.99  --sat_epr_types                         true
% 3.62/0.99  --sat_non_cyclic_types                  false
% 3.62/0.99  --sat_finite_models                     false
% 3.62/0.99  --sat_fm_lemmas                         false
% 3.62/0.99  --sat_fm_prep                           false
% 3.62/0.99  --sat_fm_uc_incr                        true
% 3.62/0.99  --sat_out_model                         small
% 3.62/0.99  --sat_out_clauses                       false
% 3.62/0.99  
% 3.62/0.99  ------ QBF Options
% 3.62/0.99  
% 3.62/0.99  --qbf_mode                              false
% 3.62/0.99  --qbf_elim_univ                         false
% 3.62/0.99  --qbf_dom_inst                          none
% 3.62/0.99  --qbf_dom_pre_inst                      false
% 3.62/0.99  --qbf_sk_in                             false
% 3.62/0.99  --qbf_pred_elim                         true
% 3.62/0.99  --qbf_split                             512
% 3.62/0.99  
% 3.62/0.99  ------ BMC1 Options
% 3.62/0.99  
% 3.62/0.99  --bmc1_incremental                      false
% 3.62/0.99  --bmc1_axioms                           reachable_all
% 3.62/0.99  --bmc1_min_bound                        0
% 3.62/0.99  --bmc1_max_bound                        -1
% 3.62/0.99  --bmc1_max_bound_default                -1
% 3.62/0.99  --bmc1_symbol_reachability              true
% 3.62/0.99  --bmc1_property_lemmas                  false
% 3.62/0.99  --bmc1_k_induction                      false
% 3.62/0.99  --bmc1_non_equiv_states                 false
% 3.62/0.99  --bmc1_deadlock                         false
% 3.62/0.99  --bmc1_ucm                              false
% 3.62/0.99  --bmc1_add_unsat_core                   none
% 3.62/0.99  --bmc1_unsat_core_children              false
% 3.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.99  --bmc1_out_stat                         full
% 3.62/0.99  --bmc1_ground_init                      false
% 3.62/0.99  --bmc1_pre_inst_next_state              false
% 3.62/0.99  --bmc1_pre_inst_state                   false
% 3.62/0.99  --bmc1_pre_inst_reach_state             false
% 3.62/0.99  --bmc1_out_unsat_core                   false
% 3.62/0.99  --bmc1_aig_witness_out                  false
% 3.62/0.99  --bmc1_verbose                          false
% 3.62/0.99  --bmc1_dump_clauses_tptp                false
% 3.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.99  --bmc1_dump_file                        -
% 3.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.99  --bmc1_ucm_extend_mode                  1
% 3.62/0.99  --bmc1_ucm_init_mode                    2
% 3.62/0.99  --bmc1_ucm_cone_mode                    none
% 3.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.99  --bmc1_ucm_relax_model                  4
% 3.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.99  --bmc1_ucm_layered_model                none
% 3.62/0.99  --bmc1_ucm_max_lemma_size               10
% 3.62/0.99  
% 3.62/0.99  ------ AIG Options
% 3.62/0.99  
% 3.62/0.99  --aig_mode                              false
% 3.62/0.99  
% 3.62/0.99  ------ Instantiation Options
% 3.62/0.99  
% 3.62/0.99  --instantiation_flag                    true
% 3.62/0.99  --inst_sos_flag                         true
% 3.62/0.99  --inst_sos_phase                        true
% 3.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel_side                     num_symb
% 3.62/0.99  --inst_solver_per_active                1400
% 3.62/0.99  --inst_solver_calls_frac                1.
% 3.62/0.99  --inst_passive_queue_type               priority_queues
% 3.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.99  --inst_passive_queues_freq              [25;2]
% 3.62/0.99  --inst_dismatching                      true
% 3.62/0.99  --inst_eager_unprocessed_to_passive     true
% 3.62/0.99  --inst_prop_sim_given                   true
% 3.62/0.99  --inst_prop_sim_new                     false
% 3.62/0.99  --inst_subs_new                         false
% 3.62/0.99  --inst_eq_res_simp                      false
% 3.62/0.99  --inst_subs_given                       false
% 3.62/0.99  --inst_orphan_elimination               true
% 3.62/0.99  --inst_learning_loop_flag               true
% 3.62/0.99  --inst_learning_start                   3000
% 3.62/0.99  --inst_learning_factor                  2
% 3.62/0.99  --inst_start_prop_sim_after_learn       3
% 3.62/0.99  --inst_sel_renew                        solver
% 3.62/0.99  --inst_lit_activity_flag                true
% 3.62/0.99  --inst_restr_to_given                   false
% 3.62/0.99  --inst_activity_threshold               500
% 3.62/0.99  --inst_out_proof                        true
% 3.62/0.99  
% 3.62/0.99  ------ Resolution Options
% 3.62/0.99  
% 3.62/0.99  --resolution_flag                       true
% 3.62/0.99  --res_lit_sel                           adaptive
% 3.62/0.99  --res_lit_sel_side                      none
% 3.62/0.99  --res_ordering                          kbo
% 3.62/0.99  --res_to_prop_solver                    active
% 3.62/0.99  --res_prop_simpl_new                    false
% 3.62/0.99  --res_prop_simpl_given                  true
% 3.62/0.99  --res_passive_queue_type                priority_queues
% 3.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.99  --res_passive_queues_freq               [15;5]
% 3.62/0.99  --res_forward_subs                      full
% 3.62/0.99  --res_backward_subs                     full
% 3.62/0.99  --res_forward_subs_resolution           true
% 3.62/0.99  --res_backward_subs_resolution          true
% 3.62/0.99  --res_orphan_elimination                true
% 3.62/0.99  --res_time_limit                        2.
% 3.62/0.99  --res_out_proof                         true
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Options
% 3.62/0.99  
% 3.62/0.99  --superposition_flag                    true
% 3.62/0.99  --sup_passive_queue_type                priority_queues
% 3.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.99  --demod_completeness_check              fast
% 3.62/0.99  --demod_use_ground                      true
% 3.62/0.99  --sup_to_prop_solver                    passive
% 3.62/0.99  --sup_prop_simpl_new                    true
% 3.62/0.99  --sup_prop_simpl_given                  true
% 3.62/0.99  --sup_fun_splitting                     true
% 3.62/0.99  --sup_smt_interval                      50000
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Simplification Setup
% 3.62/0.99  
% 3.62/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.62/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.62/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.62/0.99  --sup_immed_triv                        [TrivRules]
% 3.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_immed_bw_main                     []
% 3.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_input_bw                          []
% 3.62/0.99  
% 3.62/0.99  ------ Combination Options
% 3.62/0.99  
% 3.62/0.99  --comb_res_mult                         3
% 3.62/0.99  --comb_sup_mult                         2
% 3.62/0.99  --comb_inst_mult                        10
% 3.62/0.99  
% 3.62/0.99  ------ Debug Options
% 3.62/0.99  
% 3.62/0.99  --dbg_backtrace                         false
% 3.62/0.99  --dbg_dump_prop_clauses                 false
% 3.62/0.99  --dbg_dump_prop_clauses_file            -
% 3.62/0.99  --dbg_out_stat                          false
% 3.62/0.99  ------ Parsing...
% 3.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  ------ Proving...
% 3.62/0.99  ------ Problem Properties 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  clauses                                 41
% 3.62/0.99  conjectures                             3
% 3.62/0.99  EPR                                     9
% 3.62/0.99  Horn                                    35
% 3.62/0.99  unary                                   11
% 3.62/0.99  binary                                  13
% 3.62/0.99  lits                                    93
% 3.62/0.99  lits eq                                 33
% 3.62/0.99  fd_pure                                 0
% 3.62/0.99  fd_pseudo                               0
% 3.62/0.99  fd_cond                                 4
% 3.62/0.99  fd_pseudo_cond                          1
% 3.62/0.99  AC symbols                              0
% 3.62/0.99  
% 3.62/0.99  ------ Schedule dynamic 5 is on 
% 3.62/0.99  
% 3.62/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  Current options:
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  ------ Input Options
% 3.62/0.99  
% 3.62/0.99  --out_options                           all
% 3.62/0.99  --tptp_safe_out                         true
% 3.62/0.99  --problem_path                          ""
% 3.62/0.99  --include_path                          ""
% 3.62/0.99  --clausifier                            res/vclausify_rel
% 3.62/0.99  --clausifier_options                    ""
% 3.62/0.99  --stdin                                 false
% 3.62/0.99  --stats_out                             all
% 3.62/0.99  
% 3.62/0.99  ------ General Options
% 3.62/0.99  
% 3.62/0.99  --fof                                   false
% 3.62/0.99  --time_out_real                         305.
% 3.62/0.99  --time_out_virtual                      -1.
% 3.62/0.99  --symbol_type_check                     false
% 3.62/0.99  --clausify_out                          false
% 3.62/0.99  --sig_cnt_out                           false
% 3.62/0.99  --trig_cnt_out                          false
% 3.62/0.99  --trig_cnt_out_tolerance                1.
% 3.62/0.99  --trig_cnt_out_sk_spl                   false
% 3.62/0.99  --abstr_cl_out                          false
% 3.62/0.99  
% 3.62/0.99  ------ Global Options
% 3.62/0.99  
% 3.62/0.99  --schedule                              default
% 3.62/0.99  --add_important_lit                     false
% 3.62/0.99  --prop_solver_per_cl                    1000
% 3.62/0.99  --min_unsat_core                        false
% 3.62/0.99  --soft_assumptions                      false
% 3.62/0.99  --soft_lemma_size                       3
% 3.62/0.99  --prop_impl_unit_size                   0
% 3.62/0.99  --prop_impl_unit                        []
% 3.62/0.99  --share_sel_clauses                     true
% 3.62/0.99  --reset_solvers                         false
% 3.62/0.99  --bc_imp_inh                            [conj_cone]
% 3.62/0.99  --conj_cone_tolerance                   3.
% 3.62/0.99  --extra_neg_conj                        none
% 3.62/0.99  --large_theory_mode                     true
% 3.62/0.99  --prolific_symb_bound                   200
% 3.62/0.99  --lt_threshold                          2000
% 3.62/0.99  --clause_weak_htbl                      true
% 3.62/0.99  --gc_record_bc_elim                     false
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing Options
% 3.62/0.99  
% 3.62/0.99  --preprocessing_flag                    true
% 3.62/0.99  --time_out_prep_mult                    0.1
% 3.62/0.99  --splitting_mode                        input
% 3.62/0.99  --splitting_grd                         true
% 3.62/0.99  --splitting_cvd                         false
% 3.62/0.99  --splitting_cvd_svl                     false
% 3.62/0.99  --splitting_nvd                         32
% 3.62/0.99  --sub_typing                            true
% 3.62/0.99  --prep_gs_sim                           true
% 3.62/0.99  --prep_unflatten                        true
% 3.62/0.99  --prep_res_sim                          true
% 3.62/0.99  --prep_upred                            true
% 3.62/0.99  --prep_sem_filter                       exhaustive
% 3.62/0.99  --prep_sem_filter_out                   false
% 3.62/0.99  --pred_elim                             true
% 3.62/0.99  --res_sim_input                         true
% 3.62/0.99  --eq_ax_congr_red                       true
% 3.62/0.99  --pure_diseq_elim                       true
% 3.62/0.99  --brand_transform                       false
% 3.62/0.99  --non_eq_to_eq                          false
% 3.62/0.99  --prep_def_merge                        true
% 3.62/0.99  --prep_def_merge_prop_impl              false
% 3.62/0.99  --prep_def_merge_mbd                    true
% 3.62/0.99  --prep_def_merge_tr_red                 false
% 3.62/0.99  --prep_def_merge_tr_cl                  false
% 3.62/0.99  --smt_preprocessing                     true
% 3.62/0.99  --smt_ac_axioms                         fast
% 3.62/0.99  --preprocessed_out                      false
% 3.62/0.99  --preprocessed_stats                    false
% 3.62/0.99  
% 3.62/0.99  ------ Abstraction refinement Options
% 3.62/0.99  
% 3.62/0.99  --abstr_ref                             []
% 3.62/0.99  --abstr_ref_prep                        false
% 3.62/0.99  --abstr_ref_until_sat                   false
% 3.62/0.99  --abstr_ref_sig_restrict                funpre
% 3.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/0.99  --abstr_ref_under                       []
% 3.62/0.99  
% 3.62/0.99  ------ SAT Options
% 3.62/0.99  
% 3.62/0.99  --sat_mode                              false
% 3.62/0.99  --sat_fm_restart_options                ""
% 3.62/0.99  --sat_gr_def                            false
% 3.62/0.99  --sat_epr_types                         true
% 3.62/0.99  --sat_non_cyclic_types                  false
% 3.62/0.99  --sat_finite_models                     false
% 3.62/0.99  --sat_fm_lemmas                         false
% 3.62/0.99  --sat_fm_prep                           false
% 3.62/0.99  --sat_fm_uc_incr                        true
% 3.62/0.99  --sat_out_model                         small
% 3.62/0.99  --sat_out_clauses                       false
% 3.62/0.99  
% 3.62/0.99  ------ QBF Options
% 3.62/0.99  
% 3.62/0.99  --qbf_mode                              false
% 3.62/0.99  --qbf_elim_univ                         false
% 3.62/0.99  --qbf_dom_inst                          none
% 3.62/0.99  --qbf_dom_pre_inst                      false
% 3.62/0.99  --qbf_sk_in                             false
% 3.62/0.99  --qbf_pred_elim                         true
% 3.62/0.99  --qbf_split                             512
% 3.62/0.99  
% 3.62/0.99  ------ BMC1 Options
% 3.62/0.99  
% 3.62/0.99  --bmc1_incremental                      false
% 3.62/0.99  --bmc1_axioms                           reachable_all
% 3.62/0.99  --bmc1_min_bound                        0
% 3.62/0.99  --bmc1_max_bound                        -1
% 3.62/0.99  --bmc1_max_bound_default                -1
% 3.62/0.99  --bmc1_symbol_reachability              true
% 3.62/0.99  --bmc1_property_lemmas                  false
% 3.62/0.99  --bmc1_k_induction                      false
% 3.62/0.99  --bmc1_non_equiv_states                 false
% 3.62/0.99  --bmc1_deadlock                         false
% 3.62/0.99  --bmc1_ucm                              false
% 3.62/0.99  --bmc1_add_unsat_core                   none
% 3.62/0.99  --bmc1_unsat_core_children              false
% 3.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/0.99  --bmc1_out_stat                         full
% 3.62/0.99  --bmc1_ground_init                      false
% 3.62/0.99  --bmc1_pre_inst_next_state              false
% 3.62/0.99  --bmc1_pre_inst_state                   false
% 3.62/0.99  --bmc1_pre_inst_reach_state             false
% 3.62/0.99  --bmc1_out_unsat_core                   false
% 3.62/0.99  --bmc1_aig_witness_out                  false
% 3.62/0.99  --bmc1_verbose                          false
% 3.62/0.99  --bmc1_dump_clauses_tptp                false
% 3.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.62/0.99  --bmc1_dump_file                        -
% 3.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.62/0.99  --bmc1_ucm_extend_mode                  1
% 3.62/0.99  --bmc1_ucm_init_mode                    2
% 3.62/0.99  --bmc1_ucm_cone_mode                    none
% 3.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.62/0.99  --bmc1_ucm_relax_model                  4
% 3.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/0.99  --bmc1_ucm_layered_model                none
% 3.62/0.99  --bmc1_ucm_max_lemma_size               10
% 3.62/0.99  
% 3.62/0.99  ------ AIG Options
% 3.62/0.99  
% 3.62/0.99  --aig_mode                              false
% 3.62/0.99  
% 3.62/0.99  ------ Instantiation Options
% 3.62/0.99  
% 3.62/0.99  --instantiation_flag                    true
% 3.62/0.99  --inst_sos_flag                         true
% 3.62/0.99  --inst_sos_phase                        true
% 3.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/0.99  --inst_lit_sel_side                     none
% 3.62/0.99  --inst_solver_per_active                1400
% 3.62/0.99  --inst_solver_calls_frac                1.
% 3.62/0.99  --inst_passive_queue_type               priority_queues
% 3.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/0.99  --inst_passive_queues_freq              [25;2]
% 3.62/0.99  --inst_dismatching                      true
% 3.62/0.99  --inst_eager_unprocessed_to_passive     true
% 3.62/0.99  --inst_prop_sim_given                   true
% 3.62/0.99  --inst_prop_sim_new                     false
% 3.62/0.99  --inst_subs_new                         false
% 3.62/0.99  --inst_eq_res_simp                      false
% 3.62/0.99  --inst_subs_given                       false
% 3.62/0.99  --inst_orphan_elimination               true
% 3.62/0.99  --inst_learning_loop_flag               true
% 3.62/0.99  --inst_learning_start                   3000
% 3.62/0.99  --inst_learning_factor                  2
% 3.62/0.99  --inst_start_prop_sim_after_learn       3
% 3.62/0.99  --inst_sel_renew                        solver
% 3.62/0.99  --inst_lit_activity_flag                true
% 3.62/0.99  --inst_restr_to_given                   false
% 3.62/0.99  --inst_activity_threshold               500
% 3.62/0.99  --inst_out_proof                        true
% 3.62/0.99  
% 3.62/0.99  ------ Resolution Options
% 3.62/0.99  
% 3.62/0.99  --resolution_flag                       false
% 3.62/0.99  --res_lit_sel                           adaptive
% 3.62/0.99  --res_lit_sel_side                      none
% 3.62/0.99  --res_ordering                          kbo
% 3.62/0.99  --res_to_prop_solver                    active
% 3.62/0.99  --res_prop_simpl_new                    false
% 3.62/0.99  --res_prop_simpl_given                  true
% 3.62/0.99  --res_passive_queue_type                priority_queues
% 3.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/0.99  --res_passive_queues_freq               [15;5]
% 3.62/0.99  --res_forward_subs                      full
% 3.62/0.99  --res_backward_subs                     full
% 3.62/0.99  --res_forward_subs_resolution           true
% 3.62/0.99  --res_backward_subs_resolution          true
% 3.62/0.99  --res_orphan_elimination                true
% 3.62/0.99  --res_time_limit                        2.
% 3.62/0.99  --res_out_proof                         true
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Options
% 3.62/0.99  
% 3.62/0.99  --superposition_flag                    true
% 3.62/0.99  --sup_passive_queue_type                priority_queues
% 3.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.62/0.99  --demod_completeness_check              fast
% 3.62/0.99  --demod_use_ground                      true
% 3.62/0.99  --sup_to_prop_solver                    passive
% 3.62/0.99  --sup_prop_simpl_new                    true
% 3.62/0.99  --sup_prop_simpl_given                  true
% 3.62/0.99  --sup_fun_splitting                     true
% 3.62/0.99  --sup_smt_interval                      50000
% 3.62/0.99  
% 3.62/0.99  ------ Superposition Simplification Setup
% 3.62/0.99  
% 3.62/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.62/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.62/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.62/0.99  --sup_immed_triv                        [TrivRules]
% 3.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_immed_bw_main                     []
% 3.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/0.99  --sup_input_bw                          []
% 3.62/0.99  
% 3.62/0.99  ------ Combination Options
% 3.62/0.99  
% 3.62/0.99  --comb_res_mult                         3
% 3.62/0.99  --comb_sup_mult                         2
% 3.62/0.99  --comb_inst_mult                        10
% 3.62/0.99  
% 3.62/0.99  ------ Debug Options
% 3.62/0.99  
% 3.62/0.99  --dbg_backtrace                         false
% 3.62/0.99  --dbg_dump_prop_clauses                 false
% 3.62/0.99  --dbg_dump_prop_clauses_file            -
% 3.62/0.99  --dbg_out_stat                          false
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS status Theorem for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  fof(f24,conjecture,(
% 3.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f25,negated_conjecture,(
% 3.62/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.62/0.99    inference(negated_conjecture,[],[f24])).
% 3.62/0.99  
% 3.62/0.99  fof(f46,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.62/0.99    inference(ennf_transformation,[],[f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f47,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.62/0.99    inference(flattening,[],[f46])).
% 3.62/0.99  
% 3.62/0.99  fof(f65,plain,(
% 3.62/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f66,plain,(
% 3.62/0.99    (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f47,f65])).
% 3.62/0.99  
% 3.62/0.99  fof(f110,plain,(
% 3.62/0.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.62/0.99    inference(cnf_transformation,[],[f66])).
% 3.62/0.99  
% 3.62/0.99  fof(f20,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f39,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f20])).
% 3.62/0.99  
% 3.62/0.99  fof(f98,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f39])).
% 3.62/0.99  
% 3.62/0.99  fof(f111,plain,(
% 3.62/0.99    r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5)),
% 3.62/0.99    inference(cnf_transformation,[],[f66])).
% 3.62/0.99  
% 3.62/0.99  fof(f4,axiom,(
% 3.62/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f28,plain,(
% 3.62/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.62/0.99    inference(ennf_transformation,[],[f4])).
% 3.62/0.99  
% 3.62/0.99  fof(f56,plain,(
% 3.62/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f57,plain,(
% 3.62/0.99    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f56])).
% 3.62/0.99  
% 3.62/0.99  fof(f73,plain,(
% 3.62/0.99    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f57])).
% 3.62/0.99  
% 3.62/0.99  fof(f9,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f29,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f9])).
% 3.62/0.99  
% 3.62/0.99  fof(f83,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f29])).
% 3.62/0.99  
% 3.62/0.99  fof(f8,axiom,(
% 3.62/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f62,plain,(
% 3.62/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.62/0.99    inference(nnf_transformation,[],[f8])).
% 3.62/0.99  
% 3.62/0.99  fof(f82,plain,(
% 3.62/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f62])).
% 3.62/0.99  
% 3.62/0.99  fof(f3,axiom,(
% 3.62/0.99    v1_xboole_0(k1_xboole_0)),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f72,plain,(
% 3.62/0.99    v1_xboole_0(k1_xboole_0)),
% 3.62/0.99    inference(cnf_transformation,[],[f3])).
% 3.62/0.99  
% 3.62/0.99  fof(f23,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f44,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f23])).
% 3.62/0.99  
% 3.62/0.99  fof(f45,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(flattening,[],[f44])).
% 3.62/0.99  
% 3.62/0.99  fof(f64,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(nnf_transformation,[],[f45])).
% 3.62/0.99  
% 3.62/0.99  fof(f104,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f64])).
% 3.62/0.99  
% 3.62/0.99  fof(f113,plain,(
% 3.62/0.99    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) | ~v1_funct_2(sK6,sK3,sK5) | ~v1_funct_1(sK6)),
% 3.62/0.99    inference(cnf_transformation,[],[f66])).
% 3.62/0.99  
% 3.62/0.99  fof(f108,plain,(
% 3.62/0.99    v1_funct_1(sK6)),
% 3.62/0.99    inference(cnf_transformation,[],[f66])).
% 3.62/0.99  
% 3.62/0.99  fof(f21,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f40,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.62/0.99    inference(ennf_transformation,[],[f21])).
% 3.62/0.99  
% 3.62/0.99  fof(f41,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.62/0.99    inference(flattening,[],[f40])).
% 3.62/0.99  
% 3.62/0.99  fof(f99,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f41])).
% 3.62/0.99  
% 3.62/0.99  fof(f18,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f26,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.62/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f37,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f26])).
% 3.62/0.99  
% 3.62/0.99  fof(f96,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f37])).
% 3.62/0.99  
% 3.62/0.99  fof(f11,axiom,(
% 3.62/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f31,plain,(
% 3.62/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f11])).
% 3.62/0.99  
% 3.62/0.99  fof(f63,plain,(
% 3.62/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.62/0.99    inference(nnf_transformation,[],[f31])).
% 3.62/0.99  
% 3.62/0.99  fof(f85,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f63])).
% 3.62/0.99  
% 3.62/0.99  fof(f13,axiom,(
% 3.62/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f88,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f13])).
% 3.62/0.99  
% 3.62/0.99  fof(f81,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f62])).
% 3.62/0.99  
% 3.62/0.99  fof(f10,axiom,(
% 3.62/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f30,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.62/0.99    inference(ennf_transformation,[],[f10])).
% 3.62/0.99  
% 3.62/0.99  fof(f84,plain,(
% 3.62/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f30])).
% 3.62/0.99  
% 3.62/0.99  fof(f5,axiom,(
% 3.62/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f58,plain,(
% 3.62/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.99    inference(nnf_transformation,[],[f5])).
% 3.62/0.99  
% 3.62/0.99  fof(f59,plain,(
% 3.62/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.62/0.99    inference(flattening,[],[f58])).
% 3.62/0.99  
% 3.62/0.99  fof(f76,plain,(
% 3.62/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f59])).
% 3.62/0.99  
% 3.62/0.99  fof(f2,axiom,(
% 3.62/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f27,plain,(
% 3.62/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f2])).
% 3.62/0.99  
% 3.62/0.99  fof(f52,plain,(
% 3.62/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.62/0.99    inference(nnf_transformation,[],[f27])).
% 3.62/0.99  
% 3.62/0.99  fof(f53,plain,(
% 3.62/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.62/0.99    inference(rectify,[],[f52])).
% 3.62/0.99  
% 3.62/0.99  fof(f54,plain,(
% 3.62/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f55,plain,(
% 3.62/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 3.62/0.99  
% 3.62/0.99  fof(f71,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f70,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f55])).
% 3.62/0.99  
% 3.62/0.99  fof(f112,plain,(
% 3.62/0.99    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 3.62/0.99    inference(cnf_transformation,[],[f66])).
% 3.62/0.99  
% 3.62/0.99  fof(f7,axiom,(
% 3.62/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f60,plain,(
% 3.62/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.62/0.99    inference(nnf_transformation,[],[f7])).
% 3.62/0.99  
% 3.62/0.99  fof(f61,plain,(
% 3.62/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.62/0.99    inference(flattening,[],[f60])).
% 3.62/0.99  
% 3.62/0.99  fof(f78,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f61])).
% 3.62/0.99  
% 3.62/0.99  fof(f79,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f61])).
% 3.62/0.99  
% 3.62/0.99  fof(f117,plain,(
% 3.62/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.62/0.99    inference(equality_resolution,[],[f79])).
% 3.62/0.99  
% 3.62/0.99  fof(f102,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f64])).
% 3.62/0.99  
% 3.62/0.99  fof(f109,plain,(
% 3.62/0.99    v1_funct_2(sK6,sK3,sK4)),
% 3.62/0.99    inference(cnf_transformation,[],[f66])).
% 3.62/0.99  
% 3.62/0.99  fof(f19,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f38,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.62/0.99    inference(ennf_transformation,[],[f19])).
% 3.62/0.99  
% 3.62/0.99  fof(f97,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f38])).
% 3.62/0.99  
% 3.62/0.99  fof(f16,axiom,(
% 3.62/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f93,plain,(
% 3.62/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f16])).
% 3.62/0.99  
% 3.62/0.99  fof(f14,axiom,(
% 3.62/0.99    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f33,plain,(
% 3.62/0.99    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f14])).
% 3.62/0.99  
% 3.62/0.99  fof(f34,plain,(
% 3.62/0.99    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.62/0.99    inference(flattening,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f89,plain,(
% 3.62/0.99    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f34])).
% 3.62/0.99  
% 3.62/0.99  fof(f17,axiom,(
% 3.62/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f94,plain,(
% 3.62/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f1,axiom,(
% 3.62/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f48,plain,(
% 3.62/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.62/0.99    inference(nnf_transformation,[],[f1])).
% 3.62/0.99  
% 3.62/0.99  fof(f49,plain,(
% 3.62/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.62/0.99    inference(rectify,[],[f48])).
% 3.62/0.99  
% 3.62/0.99  fof(f50,plain,(
% 3.62/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f51,plain,(
% 3.62/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 3.62/0.99  
% 3.62/0.99  fof(f67,plain,(
% 3.62/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f51])).
% 3.62/0.99  
% 3.62/0.99  fof(f22,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f42,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.62/0.99    inference(ennf_transformation,[],[f22])).
% 3.62/0.99  
% 3.62/0.99  fof(f43,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.62/0.99    inference(flattening,[],[f42])).
% 3.62/0.99  
% 3.62/0.99  fof(f100,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f43])).
% 3.62/0.99  
% 3.62/0.99  fof(f101,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k2_relset_1(X1,X0,X2)) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f43])).
% 3.62/0.99  
% 3.62/0.99  fof(f12,axiom,(
% 3.62/0.99    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f32,plain,(
% 3.62/0.99    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.62/0.99    inference(ennf_transformation,[],[f12])).
% 3.62/0.99  
% 3.62/0.99  fof(f87,plain,(
% 3.62/0.99    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f32])).
% 3.62/0.99  
% 3.62/0.99  fof(f15,axiom,(
% 3.62/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f35,plain,(
% 3.62/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.62/1.00    inference(ennf_transformation,[],[f15])).
% 3.62/1.00  
% 3.62/1.00  fof(f36,plain,(
% 3.62/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.62/1.00    inference(flattening,[],[f35])).
% 3.62/1.00  
% 3.62/1.00  fof(f90,plain,(
% 3.62/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f36])).
% 3.62/1.00  
% 3.62/1.00  fof(f6,axiom,(
% 3.62/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.62/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.00  
% 3.62/1.00  fof(f77,plain,(
% 3.62/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.62/1.00    inference(cnf_transformation,[],[f6])).
% 3.62/1.00  
% 3.62/1.00  fof(f105,plain,(
% 3.62/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.62/1.00    inference(cnf_transformation,[],[f64])).
% 3.62/1.00  
% 3.62/1.00  fof(f121,plain,(
% 3.62/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.62/1.00    inference(equality_resolution,[],[f105])).
% 3.62/1.00  
% 3.62/1.00  fof(f92,plain,(
% 3.62/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.62/1.00    inference(cnf_transformation,[],[f16])).
% 3.62/1.00  
% 3.62/1.00  cnf(c_44,negated_conjecture,
% 3.62/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.62/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1762,plain,
% 3.62/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_31,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1767,plain,
% 3.62/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.62/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3638,plain,
% 3.62/1.00      ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1762,c_1767]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_43,negated_conjecture,
% 3.62/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) ),
% 3.62/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1763,plain,
% 3.62/1.00      ( r1_tarski(k2_relset_1(sK3,sK4,sK6),sK5) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3649,plain,
% 3.62/1.00      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 3.62/1.00      inference(demodulation,[status(thm)],[c_3638,c_1763]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_6,plain,
% 3.62/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1780,plain,
% 3.62/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_16,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.00      | ~ r2_hidden(X2,X0)
% 3.62/1.00      | ~ v1_xboole_0(X1) ),
% 3.62/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_14,plain,
% 3.62/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_329,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.62/1.00      inference(prop_impl,[status(thm)],[c_14]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_330,plain,
% 3.62/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/1.00      inference(renaming,[status(thm)],[c_329]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_402,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 3.62/1.00      inference(bin_hyper_res,[status(thm)],[c_16,c_330]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1761,plain,
% 3.62/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.62/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.62/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2912,plain,
% 3.62/1.00      ( k1_xboole_0 = X0
% 3.62/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.62/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1780,c_1761]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5371,plain,
% 3.62/1.00      ( k2_relat_1(sK6) = k1_xboole_0 | v1_xboole_0(sK5) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_3649,c_2912]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5,plain,
% 3.62/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_140,plain,
% 3.62/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_38,plain,
% 3.62/1.00      ( v1_funct_2(X0,X1,X2)
% 3.62/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.62/1.00      | k1_xboole_0 = X2 ),
% 3.62/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_41,negated_conjecture,
% 3.62/1.00      ( ~ v1_funct_2(sK6,sK3,sK5)
% 3.62/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | ~ v1_funct_1(sK6) ),
% 3.62/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_46,negated_conjecture,
% 3.62/1.00      ( v1_funct_1(sK6) ),
% 3.62/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_235,plain,
% 3.62/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | ~ v1_funct_2(sK6,sK3,sK5) ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_41,c_46]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_236,negated_conjecture,
% 3.62/1.00      ( ~ v1_funct_2(sK6,sK3,sK5)
% 3.62/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5))) ),
% 3.62/1.00      inference(renaming,[status(thm)],[c_235]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_637,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.62/1.00      | sK5 != X2
% 3.62/1.00      | sK3 != X1
% 3.62/1.00      | sK6 != X0
% 3.62/1.00      | k1_xboole_0 = X2 ),
% 3.62/1.00      inference(resolution_lifted,[status(thm)],[c_38,c_236]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_638,plain,
% 3.62/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | k1_relset_1(sK3,sK5,sK6) != sK3
% 3.62/1.00      | k1_xboole_0 = sK5 ),
% 3.62/1.00      inference(unflattening,[status(thm)],[c_637]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_32,plain,
% 3.62/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.62/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.62/1.00      | ~ v1_relat_1(X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1847,plain,
% 3.62/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | ~ r1_tarski(k2_relat_1(sK6),sK5)
% 3.62/1.00      | ~ r1_tarski(k1_relat_1(sK6),sK3)
% 3.62/1.00      | ~ v1_relat_1(sK6) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_32]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1012,plain,
% 3.62/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.62/1.00      theory(equality) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1867,plain,
% 3.62/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK5) | sK5 != X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1868,plain,
% 3.62/1.00      ( sK5 != X0
% 3.62/1.00      | v1_xboole_0(X0) != iProver_top
% 3.62/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_1867]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1870,plain,
% 3.62/1.00      ( sK5 != k1_xboole_0
% 3.62/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.62/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1868]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_29,plain,
% 3.62/1.00      ( v4_relat_1(X0,X1)
% 3.62/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.62/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_19,plain,
% 3.62/1.00      ( ~ v4_relat_1(X0,X1)
% 3.62/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.62/1.00      | ~ v1_relat_1(X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_538,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.62/1.00      | ~ v1_relat_1(X0) ),
% 3.62/1.00      inference(resolution,[status(thm)],[c_29,c_19]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1759,plain,
% 3.62/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.62/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2199,plain,
% 3.62/1.00      ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top
% 3.62/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1762,c_1759]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2200,plain,
% 3.62/1.00      ( r1_tarski(k1_relat_1(sK6),sK3) | ~ v1_relat_1(sK6) ),
% 3.62/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2199]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1011,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2085,plain,
% 3.62/1.00      ( k1_relset_1(sK3,sK5,sK6) != X0
% 3.62/1.00      | k1_relset_1(sK3,sK5,sK6) = sK3
% 3.62/1.00      | sK3 != X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2384,plain,
% 3.62/1.00      ( k1_relset_1(sK3,sK5,sK6) != k1_relat_1(sK6)
% 3.62/1.00      | k1_relset_1(sK3,sK5,sK6) = sK3
% 3.62/1.00      | sK3 != k1_relat_1(sK6) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2085]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_21,plain,
% 3.62/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1773,plain,
% 3.62/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_15,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.62/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1775,plain,
% 3.62/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.62/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3019,plain,
% 3.62/1.00      ( r1_tarski(sK6,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1762,c_1775]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_17,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/1.00      | ~ v1_relat_1(X1)
% 3.62/1.00      | v1_relat_1(X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_403,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.62/1.00      inference(bin_hyper_res,[status(thm)],[c_17,c_330]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1760,plain,
% 3.62/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.62/1.00      | v1_relat_1(X1) != iProver_top
% 3.62/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3114,plain,
% 3.62/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.62/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_3019,c_1760]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3117,plain,
% 3.62/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1773,c_3114]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3118,plain,
% 3.62/1.00      ( v1_relat_1(sK6) ),
% 3.62/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3117]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_7,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2904,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | sK5 = X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3418,plain,
% 3.62/1.00      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2904]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2,plain,
% 3.62/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.62/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2136,plain,
% 3.62/1.00      ( r1_tarski(X0,sK5) | ~ r2_hidden(sK1(X0,sK5),sK5) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3421,plain,
% 3.62/1.00      ( r1_tarski(sK5,sK5) | ~ r2_hidden(sK1(sK5,sK5),sK5) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2136]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3,plain,
% 3.62/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2137,plain,
% 3.62/1.00      ( r1_tarski(X0,sK5) | r2_hidden(sK1(X0,sK5),X0) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3419,plain,
% 3.62/1.00      ( r1_tarski(sK5,sK5) | r2_hidden(sK1(sK5,sK5),sK5) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2137]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2903,plain,
% 3.62/1.00      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3569,plain,
% 3.62/1.00      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2903]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3570,plain,
% 3.62/1.00      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_3569]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3651,plain,
% 3.62/1.00      ( r1_tarski(k2_relat_1(sK6),sK5) ),
% 3.62/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3649]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1010,plain,( X0 = X0 ),theory(equality) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3773,plain,
% 3.62/1.00      ( sK3 = sK3 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1010]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1779,plain,
% 3.62/1.00      ( X0 = X1
% 3.62/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.62/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4511,plain,
% 3.62/1.00      ( k1_relat_1(sK6) = sK3
% 3.62/1.00      | r1_tarski(sK3,k1_relat_1(sK6)) != iProver_top
% 3.62/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_2199,c_1779]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_42,negated_conjecture,
% 3.62/1.00      ( k1_xboole_0 != sK4 | k1_xboole_0 = sK3 ),
% 3.62/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_13,plain,
% 3.62/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.62/1.00      | k1_xboole_0 = X0
% 3.62/1.00      | k1_xboole_0 = X1 ),
% 3.62/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_127,plain,
% 3.62/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.62/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_12,plain,
% 3.62/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_128,plain,
% 3.62/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1838,plain,
% 3.62/1.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1941,plain,
% 3.62/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1838]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2560,plain,
% 3.62/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2561,plain,
% 3.62/1.00      ( sK3 != X0
% 3.62/1.00      | v1_xboole_0(X0) != iProver_top
% 3.62/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_2560]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2563,plain,
% 3.62/1.00      ( sK3 != k1_xboole_0
% 3.62/1.00      | v1_xboole_0(sK3) = iProver_top
% 3.62/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2561]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_40,plain,
% 3.62/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.62/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.62/1.00      | k1_xboole_0 = X2 ),
% 3.62/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_45,negated_conjecture,
% 3.62/1.00      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.62/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_650,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.62/1.00      | sK4 != X2
% 3.62/1.00      | sK3 != X1
% 3.62/1.00      | sK6 != X0
% 3.62/1.00      | k1_xboole_0 = X2 ),
% 3.62/1.00      inference(resolution_lifted,[status(thm)],[c_40,c_45]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_651,plain,
% 3.62/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.62/1.00      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.62/1.00      | k1_xboole_0 = sK4 ),
% 3.62/1.00      inference(unflattening,[status(thm)],[c_650]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_653,plain,
% 3.62/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_651,c_44]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_30,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1768,plain,
% 3.62/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.62/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3844,plain,
% 3.62/1.00      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1762,c_1768]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3940,plain,
% 3.62/1.00      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_653,c_3844]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3971,plain,
% 3.62/1.00      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3972,plain,
% 3.62/1.00      ( sK4 != k1_xboole_0
% 3.62/1.00      | k1_xboole_0 = sK4
% 3.62/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_3971]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_25,plain,
% 3.62/1.00      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_22,plain,
% 3.62/1.00      ( ~ v1_relat_1(X0)
% 3.62/1.00      | v1_xboole_0(X0)
% 3.62/1.00      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1772,plain,
% 3.62/1.00      ( v1_relat_1(X0) != iProver_top
% 3.62/1.00      | v1_xboole_0(X0) = iProver_top
% 3.62/1.00      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4422,plain,
% 3.62/1.00      ( v1_relat_1(k6_relat_1(X0)) != iProver_top
% 3.62/1.00      | v1_xboole_0(X0) != iProver_top
% 3.62/1.00      | v1_xboole_0(k6_relat_1(X0)) = iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_25,c_1772]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_28,plain,
% 3.62/1.00      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_88,plain,
% 3.62/1.00      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4520,plain,
% 3.62/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.62/1.00      | v1_xboole_0(k6_relat_1(X0)) = iProver_top ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_4422,c_88]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1783,plain,
% 3.62/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.62/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1,plain,
% 3.62/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.62/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1785,plain,
% 3.62/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.62/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3053,plain,
% 3.62/1.00      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1783,c_1785]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_34,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | ~ r1_tarski(k6_relat_1(X1),X0)
% 3.62/1.00      | k1_relset_1(X1,X2,X0) = X1 ),
% 3.62/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1764,plain,
% 3.62/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.62/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.62/1.00      | r1_tarski(k6_relat_1(X0),X2) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3489,plain,
% 3.62/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 3.62/1.00      | r1_tarski(k6_relat_1(sK3),sK6) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1762,c_1764]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3684,plain,
% 3.62/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 3.62/1.00      | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_3053,c_3489]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3936,plain,
% 3.62/1.00      ( k1_relat_1(sK6) = sK3
% 3.62/1.00      | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
% 3.62/1.00      inference(demodulation,[status(thm)],[c_3844,c_3684]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4533,plain,
% 3.62/1.00      ( k1_relat_1(sK6) = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_4520,c_3936]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4650,plain,
% 3.62/1.00      ( k1_relat_1(sK6) = sK3 ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_4511,c_42,c_127,c_128,c_140,c_1941,c_2563,c_3773,
% 3.62/1.00                 c_3940,c_3972,c_4533]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1937,plain,
% 3.62/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3930,plain,
% 3.62/1.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1937]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4763,plain,
% 3.62/1.00      ( k1_relat_1(sK6) != sK3 | sK3 = k1_relat_1(sK6) | sK3 != sK3 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_3930]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5126,plain,
% 3.62/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | k1_relset_1(sK3,sK5,sK6) = k1_relat_1(sK6) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_30]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5612,plain,
% 3.62/1.00      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_5371,c_42,c_127,c_128,c_140,c_638,c_1847,c_1870,
% 3.62/1.00                 c_1941,c_2200,c_2384,c_2563,c_3118,c_3418,c_3421,c_3419,
% 3.62/1.00                 c_3570,c_3651,c_3773,c_3940,c_3972,c_4533,c_4763,c_5126]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_33,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.62/1.00      | r1_tarski(X1,k2_relset_1(X1,X2,X0))
% 3.62/1.00      | ~ r1_tarski(k6_relat_1(X1),X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1765,plain,
% 3.62/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.62/1.00      | r1_tarski(X1,k2_relset_1(X1,X2,X0)) = iProver_top
% 3.62/1.00      | r1_tarski(k6_relat_1(X1),X0) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3780,plain,
% 3.62/1.00      ( r1_tarski(k6_relat_1(sK3),sK6) != iProver_top
% 3.62/1.00      | r1_tarski(sK3,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_1762,c_1765]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3784,plain,
% 3.62/1.00      ( r1_tarski(k6_relat_1(sK3),sK6) != iProver_top
% 3.62/1.00      | r1_tarski(sK3,k2_relat_1(sK6)) = iProver_top ),
% 3.62/1.00      inference(light_normalisation,[status(thm)],[c_3780,c_3638]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4081,plain,
% 3.62/1.00      ( r1_tarski(sK3,k2_relat_1(sK6)) = iProver_top
% 3.62/1.00      | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_3053,c_3784]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4512,plain,
% 3.62/1.00      ( k2_relat_1(sK6) = sK3
% 3.62/1.00      | r1_tarski(k2_relat_1(sK6),sK3) != iProver_top
% 3.62/1.00      | v1_xboole_0(k6_relat_1(sK3)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_4081,c_1779]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5072,plain,
% 3.62/1.00      ( k2_relat_1(sK6) = sK3
% 3.62/1.00      | v1_xboole_0(k6_relat_1(sK3)) != iProver_top
% 3.62/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_3053,c_4512]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5154,plain,
% 3.62/1.00      ( k2_relat_1(sK6) = sK3
% 3.62/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top
% 3.62/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_4520,c_5072]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3102,plain,
% 3.62/1.00      ( ~ v1_relat_1(sK6)
% 3.62/1.00      | ~ v1_xboole_0(k2_relat_1(sK6))
% 3.62/1.00      | v1_xboole_0(sK6) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3106,plain,
% 3.62/1.00      ( v1_relat_1(sK6) != iProver_top
% 3.62/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top
% 3.62/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_3102]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_20,plain,
% 3.62/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 3.62/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1774,plain,
% 3.62/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.62/1.00      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4003,plain,
% 3.62/1.00      ( sK4 = k1_xboole_0
% 3.62/1.00      | v1_xboole_0(sK3) = iProver_top
% 3.62/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_3940,c_1774]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4154,plain,
% 3.62/1.00      ( v1_xboole_0(sK3) = iProver_top
% 3.62/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_4003,c_42,c_127,c_128,c_140,c_1941,c_2563,c_3773,
% 3.62/1.00                 c_3972]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5157,plain,
% 3.62/1.00      ( v1_xboole_0(k2_relat_1(sK6)) != iProver_top
% 3.62/1.00      | k2_relat_1(sK6) = sK3 ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_5154,c_3106,c_3117,c_4154]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5158,plain,
% 3.62/1.00      ( k2_relat_1(sK6) = sK3
% 3.62/1.00      | v1_xboole_0(k2_relat_1(sK6)) != iProver_top ),
% 3.62/1.00      inference(renaming,[status(thm)],[c_5157]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_5614,plain,
% 3.62/1.00      ( sK3 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.62/1.00      inference(demodulation,[status(thm)],[c_5612,c_5158]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_24,plain,
% 3.62/1.00      ( ~ v1_relat_1(X0)
% 3.62/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.62/1.00      | k1_xboole_0 = X0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1770,plain,
% 3.62/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.62/1.00      | k1_xboole_0 = X0
% 3.62/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.62/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4655,plain,
% 3.62/1.00      ( sK3 != k1_xboole_0
% 3.62/1.00      | sK6 = k1_xboole_0
% 3.62/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_4650,c_1770]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_90,plain,
% 3.62/1.00      ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_88]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_10,plain,
% 3.62/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.62/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_130,plain,
% 3.62/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_37,plain,
% 3.62/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.62/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.62/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_608,plain,
% 3.62/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.62/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.62/1.00      | sK5 != X1
% 3.62/1.00      | sK3 != k1_xboole_0
% 3.62/1.00      | sK6 != X0 ),
% 3.62/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_236]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_609,plain,
% 3.62/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK5)))
% 3.62/1.00      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.62/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) != k1_xboole_0
% 3.62/1.00      | sK3 != k1_xboole_0 ),
% 3.62/1.00      inference(unflattening,[status(thm)],[c_608]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2020,plain,
% 3.62/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.62/1.00      | ~ r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5)) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2333,plain,
% 3.62/1.00      ( r1_tarski(sK6,k2_zfmisc_1(k1_xboole_0,sK5))
% 3.62/1.00      | r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2831,plain,
% 3.62/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK5)))
% 3.62/1.00      | ~ r1_tarski(k6_relat_1(k1_xboole_0),sK6)
% 3.62/1.00      | k1_relset_1(k1_xboole_0,sK5,sK6) = k1_xboole_0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_1014,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.62/1.00      theory(equality) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2191,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK6) | X2 != X0 | sK6 != X1 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1014]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2996,plain,
% 3.62/1.00      ( ~ r1_tarski(X0,X1)
% 3.62/1.00      | r1_tarski(k6_relat_1(k1_xboole_0),sK6)
% 3.62/1.00      | k6_relat_1(k1_xboole_0) != X0
% 3.62/1.00      | sK6 != X1 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2191]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_2998,plain,
% 3.62/1.00      ( r1_tarski(k6_relat_1(k1_xboole_0),sK6)
% 3.62/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.62/1.00      | k6_relat_1(k1_xboole_0) != k1_xboole_0
% 3.62/1.00      | sK6 != k1_xboole_0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_2996]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3108,plain,
% 3.62/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK6) | sK6 != X0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3110,plain,
% 3.62/1.00      ( v1_xboole_0(sK6)
% 3.62/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.62/1.00      | sK6 != k1_xboole_0 ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_3108]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_26,plain,
% 3.62/1.00      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.62/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3501,plain,
% 3.62/1.00      ( k6_relat_1(X0) = k1_xboole_0
% 3.62/1.00      | k1_xboole_0 != X0
% 3.62/1.00      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.62/1.00      inference(superposition,[status(thm)],[c_26,c_1770]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_3504,plain,
% 3.62/1.00      ( k6_relat_1(k1_xboole_0) = k1_xboole_0
% 3.62/1.00      | k1_xboole_0 != k1_xboole_0
% 3.62/1.00      | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_3501]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4320,plain,
% 3.62/1.00      ( ~ r2_hidden(sK1(sK6,k2_zfmisc_1(k1_xboole_0,sK5)),sK6)
% 3.62/1.00      | ~ v1_xboole_0(sK6) ),
% 3.62/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(c_4807,plain,
% 3.62/1.00      ( sK3 != k1_xboole_0 ),
% 3.62/1.00      inference(global_propositional_subsumption,
% 3.62/1.00                [status(thm)],
% 3.62/1.00                [c_4655,c_90,c_127,c_128,c_130,c_5,c_609,c_1847,c_2020,
% 3.62/1.00                 c_2200,c_2333,c_2831,c_2998,c_3110,c_3117,c_3118,c_3504,
% 3.62/1.00                 c_3651,c_4320]) ).
% 3.62/1.00  
% 3.62/1.00  cnf(contradiction,plain,
% 3.62/1.00      ( $false ),
% 3.62/1.00      inference(minisat,[status(thm)],[c_5614,c_4807,c_140]) ).
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.00  
% 3.62/1.00  ------                               Statistics
% 3.62/1.00  
% 3.62/1.00  ------ General
% 3.62/1.00  
% 3.62/1.00  abstr_ref_over_cycles:                  0
% 3.62/1.00  abstr_ref_under_cycles:                 0
% 3.62/1.00  gc_basic_clause_elim:                   0
% 3.62/1.00  forced_gc_time:                         0
% 3.62/1.00  parsing_time:                           0.015
% 3.62/1.00  unif_index_cands_time:                  0.
% 3.62/1.00  unif_index_add_time:                    0.
% 3.62/1.00  orderings_time:                         0.
% 3.62/1.00  out_proof_time:                         0.014
% 3.62/1.00  total_time:                             0.209
% 3.62/1.00  num_of_symbols:                         54
% 3.62/1.00  num_of_terms:                           4289
% 3.62/1.00  
% 3.62/1.00  ------ Preprocessing
% 3.62/1.00  
% 3.62/1.00  num_of_splits:                          0
% 3.62/1.00  num_of_split_atoms:                     0
% 3.62/1.00  num_of_reused_defs:                     0
% 3.62/1.00  num_eq_ax_congr_red:                    22
% 3.62/1.00  num_of_sem_filtered_clauses:            3
% 3.62/1.00  num_of_subtypes:                        0
% 3.62/1.00  monotx_restored_types:                  0
% 3.62/1.00  sat_num_of_epr_types:                   0
% 3.62/1.00  sat_num_of_non_cyclic_types:            0
% 3.62/1.00  sat_guarded_non_collapsed_types:        0
% 3.62/1.00  num_pure_diseq_elim:                    0
% 3.62/1.00  simp_replaced_by:                       0
% 3.62/1.00  res_preprocessed:                       196
% 3.62/1.00  prep_upred:                             0
% 3.62/1.00  prep_unflattend:                        33
% 3.62/1.00  smt_new_axioms:                         0
% 3.62/1.00  pred_elim_cands:                        5
% 3.62/1.00  pred_elim:                              2
% 3.62/1.00  pred_elim_cl:                           3
% 3.62/1.00  pred_elim_cycles:                       4
% 3.62/1.00  merged_defs:                            8
% 3.62/1.00  merged_defs_ncl:                        0
% 3.62/1.00  bin_hyper_res:                          10
% 3.62/1.00  prep_cycles:                            4
% 3.62/1.00  pred_elim_time:                         0.007
% 3.62/1.00  splitting_time:                         0.
% 3.62/1.00  sem_filter_time:                        0.
% 3.62/1.00  monotx_time:                            0.
% 3.62/1.00  subtype_inf_time:                       0.
% 3.62/1.00  
% 3.62/1.00  ------ Problem properties
% 3.62/1.00  
% 3.62/1.00  clauses:                                41
% 3.62/1.00  conjectures:                            3
% 3.62/1.00  epr:                                    9
% 3.62/1.00  horn:                                   35
% 3.62/1.00  ground:                                 11
% 3.62/1.00  unary:                                  11
% 3.62/1.00  binary:                                 13
% 3.62/1.00  lits:                                   93
% 3.62/1.00  lits_eq:                                33
% 3.62/1.00  fd_pure:                                0
% 3.62/1.00  fd_pseudo:                              0
% 3.62/1.00  fd_cond:                                4
% 3.62/1.00  fd_pseudo_cond:                         1
% 3.62/1.00  ac_symbols:                             0
% 3.62/1.00  
% 3.62/1.00  ------ Propositional Solver
% 3.62/1.00  
% 3.62/1.00  prop_solver_calls:                      30
% 3.62/1.00  prop_fast_solver_calls:                 1204
% 3.62/1.00  smt_solver_calls:                       0
% 3.62/1.00  smt_fast_solver_calls:                  0
% 3.62/1.00  prop_num_of_clauses:                    2304
% 3.62/1.00  prop_preprocess_simplified:             7394
% 3.62/1.00  prop_fo_subsumed:                       15
% 3.62/1.00  prop_solver_time:                       0.
% 3.62/1.00  smt_solver_time:                        0.
% 3.62/1.00  smt_fast_solver_time:                   0.
% 3.62/1.00  prop_fast_solver_time:                  0.
% 3.62/1.00  prop_unsat_core_time:                   0.
% 3.62/1.00  
% 3.62/1.00  ------ QBF
% 3.62/1.00  
% 3.62/1.00  qbf_q_res:                              0
% 3.62/1.00  qbf_num_tautologies:                    0
% 3.62/1.00  qbf_prep_cycles:                        0
% 3.62/1.00  
% 3.62/1.00  ------ BMC1
% 3.62/1.00  
% 3.62/1.00  bmc1_current_bound:                     -1
% 3.62/1.00  bmc1_last_solved_bound:                 -1
% 3.62/1.00  bmc1_unsat_core_size:                   -1
% 3.62/1.00  bmc1_unsat_core_parents_size:           -1
% 3.62/1.00  bmc1_merge_next_fun:                    0
% 3.62/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.62/1.00  
% 3.62/1.00  ------ Instantiation
% 3.62/1.00  
% 3.62/1.00  inst_num_of_clauses:                    689
% 3.62/1.00  inst_num_in_passive:                    121
% 3.62/1.00  inst_num_in_active:                     328
% 3.62/1.00  inst_num_in_unprocessed:                240
% 3.62/1.00  inst_num_of_loops:                      510
% 3.62/1.00  inst_num_of_learning_restarts:          0
% 3.62/1.00  inst_num_moves_active_passive:          179
% 3.62/1.00  inst_lit_activity:                      0
% 3.62/1.00  inst_lit_activity_moves:                0
% 3.62/1.00  inst_num_tautologies:                   0
% 3.62/1.00  inst_num_prop_implied:                  0
% 3.62/1.00  inst_num_existing_simplified:           0
% 3.62/1.00  inst_num_eq_res_simplified:             0
% 3.62/1.00  inst_num_child_elim:                    0
% 3.62/1.00  inst_num_of_dismatching_blockings:      148
% 3.62/1.00  inst_num_of_non_proper_insts:           779
% 3.62/1.00  inst_num_of_duplicates:                 0
% 3.62/1.00  inst_inst_num_from_inst_to_res:         0
% 3.62/1.00  inst_dismatching_checking_time:         0.
% 3.62/1.00  
% 3.62/1.00  ------ Resolution
% 3.62/1.00  
% 3.62/1.00  res_num_of_clauses:                     0
% 3.62/1.00  res_num_in_passive:                     0
% 3.62/1.00  res_num_in_active:                      0
% 3.62/1.00  res_num_of_loops:                       200
% 3.62/1.00  res_forward_subset_subsumed:            36
% 3.62/1.00  res_backward_subset_subsumed:           4
% 3.62/1.00  res_forward_subsumed:                   0
% 3.62/1.00  res_backward_subsumed:                  0
% 3.62/1.00  res_forward_subsumption_resolution:     0
% 3.62/1.00  res_backward_subsumption_resolution:    0
% 3.62/1.00  res_clause_to_clause_subsumption:       429
% 3.62/1.00  res_orphan_elimination:                 0
% 3.62/1.00  res_tautology_del:                      46
% 3.62/1.00  res_num_eq_res_simplified:              1
% 3.62/1.00  res_num_sel_changes:                    0
% 3.62/1.00  res_moves_from_active_to_pass:          0
% 3.62/1.00  
% 3.62/1.00  ------ Superposition
% 3.62/1.00  
% 3.62/1.00  sup_time_total:                         0.
% 3.62/1.00  sup_time_generating:                    0.
% 3.62/1.00  sup_time_sim_full:                      0.
% 3.62/1.00  sup_time_sim_immed:                     0.
% 3.62/1.00  
% 3.62/1.00  sup_num_of_clauses:                     119
% 3.62/1.00  sup_num_in_active:                      73
% 3.62/1.00  sup_num_in_passive:                     46
% 3.62/1.00  sup_num_of_loops:                       100
% 3.62/1.00  sup_fw_superposition:                   107
% 3.62/1.00  sup_bw_superposition:                   41
% 3.62/1.00  sup_immediate_simplified:               24
% 3.62/1.00  sup_given_eliminated:                   2
% 3.62/1.00  comparisons_done:                       0
% 3.62/1.00  comparisons_avoided:                    3
% 3.62/1.00  
% 3.62/1.00  ------ Simplifications
% 3.62/1.00  
% 3.62/1.00  
% 3.62/1.00  sim_fw_subset_subsumed:                 6
% 3.62/1.00  sim_bw_subset_subsumed:                 5
% 3.62/1.00  sim_fw_subsumed:                        11
% 3.62/1.00  sim_bw_subsumed:                        13
% 3.62/1.00  sim_fw_subsumption_res:                 0
% 3.62/1.00  sim_bw_subsumption_res:                 0
% 3.62/1.00  sim_tautology_del:                      8
% 3.62/1.00  sim_eq_tautology_del:                   11
% 3.62/1.00  sim_eq_res_simp:                        0
% 3.62/1.00  sim_fw_demodulated:                     5
% 3.62/1.00  sim_bw_demodulated:                     16
% 3.62/1.00  sim_light_normalised:                   20
% 3.62/1.00  sim_joinable_taut:                      0
% 3.62/1.00  sim_joinable_simp:                      0
% 3.62/1.00  sim_ac_normalised:                      0
% 3.62/1.00  sim_smt_subsumption:                    0
% 3.62/1.00  
%------------------------------------------------------------------------------
