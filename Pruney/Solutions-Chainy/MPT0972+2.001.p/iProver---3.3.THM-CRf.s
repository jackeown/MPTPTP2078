%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:07 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 964 expanded)
%              Number of clauses        :  113 ( 297 expanded)
%              Number of leaves         :   20 ( 234 expanded)
%              Depth                    :   25
%              Number of atoms          :  592 (5747 expanded)
%              Number of equality atoms :  276 (1297 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK7)
        & ! [X4] :
            ( k1_funct_1(sK7,X4) = k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK7,X0,X1)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK4,sK5,sK6,X3)
          & ! [X4] :
              ( k1_funct_1(sK6,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,sK4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
          & v1_funct_2(X3,sK4,sK5)
          & v1_funct_1(X3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7)
    & ! [X4] :
        ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
        | ~ r2_hidden(X4,sK4) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f31,f51,f50])).

fof(f82,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f47])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f44])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4)
      | ~ r2_hidden(X4,sK4) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1))
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_486,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_488,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_486,c_33])).

cnf(c_1749,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1753,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2626,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1749,c_1753])).

cnf(c_2819,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_488,c_2626])).

cnf(c_17,plain,
    ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | X1 = X0
    | k1_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1755,plain,
    ( X0 = X1
    | k1_relat_1(X1) != k1_relat_1(X0)
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3669,plain,
    ( k1_relat_1(X0) != sK4
    | sK6 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_1755])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_474,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK7 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_475,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_477,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_30])).

cnf(c_1751,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2625,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1751,c_1753])).

cnf(c_2753,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_477,c_2625])).

cnf(c_3668,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_1755])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1984,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1985,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_4142,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3668,c_39,c_41,c_1985])).

cnf(c_4143,plain,
    ( k1_relat_1(X0) != sK4
    | sK7 = X0
    | sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4142])).

cnf(c_4155,plain,
    ( sK7 = sK6
    | sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6),k1_relat_1(sK7)) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_4143])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_12,plain,
    ( m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_28,negated_conjecture,
    ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | sK7 != X0
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | sK6 != sK7 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | sK6 != sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_30])).

cnf(c_554,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != X0
    | sK2(X0) != X1
    | sK7 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_363])).

cnf(c_555,plain,
    ( sK7 != sK6 ),
    inference(unflattening,[status(thm)],[c_554])).

cnf(c_1987,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1988,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1987])).

cnf(c_4168,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6),k1_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4155,c_36,c_38,c_555,c_1988])).

cnf(c_4174,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK3(sK7,sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2753,c_4168])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1752,plain,
    ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4214,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6)) = k1_funct_1(sK6,sK3(sK7,sK6))
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4174,c_1752])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X1
    | k1_funct_1(X0,sK3(X1,X0)) != k1_funct_1(X1,sK3(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1756,plain,
    ( X0 = X1
    | k1_funct_1(X0,sK3(X1,X0)) != k1_funct_1(X1,sK3(X1,X0))
    | k1_relat_1(X1) != k1_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4621,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | sK5 = k1_xboole_0
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4214,c_1756])).

cnf(c_4622,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK7)
    | ~ v1_relat_1(sK6)
    | k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK7 = sK6
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4621])).

cnf(c_4867,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK7)
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4621,c_35,c_33,c_32,c_30,c_555,c_1984,c_1987,c_4622])).

cnf(c_4871,plain,
    ( k1_relat_1(sK6) != sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2753,c_4867])).

cnf(c_4873,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3669,c_2819,c_4871])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1757,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4352,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1757])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_101,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1291,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2162,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(sK7,sK6)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_2164,plain,
    ( r1_tarski(sK7,sK6)
    | ~ r1_tarski(k1_xboole_0,sK6)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2249,plain,
    ( ~ r1_tarski(X0,sK7)
    | ~ r1_tarski(sK7,X0)
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2250,plain,
    ( sK7 = X0
    | r1_tarski(X0,sK7) != iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2249])).

cnf(c_2252,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(sK7,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2358,plain,
    ( r1_tarski(X0,sK7)
    | r2_hidden(sK1(X0,sK7),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2365,plain,
    ( r1_tarski(k1_xboole_0,sK7)
    | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_2364,plain,
    ( r1_tarski(X0,sK7) = iProver_top
    | r2_hidden(sK1(X0,sK7),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2358])).

cnf(c_2366,plain,
    ( r1_tarski(k1_xboole_0,sK7) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2364])).

cnf(c_2372,plain,
    ( r1_tarski(X0,sK6)
    | r2_hidden(sK1(X0,sK6),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2379,plain,
    ( r1_tarski(k1_xboole_0,sK6)
    | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_2378,plain,
    ( r1_tarski(X0,sK6) = iProver_top
    | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2372])).

cnf(c_2380,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_2394,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2395,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2394])).

cnf(c_2397,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_2097,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | X0 = sK6 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2458,plain,
    ( ~ r1_tarski(sK7,sK6)
    | ~ r1_tarski(sK6,sK7)
    | sK7 = sK6 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_2882,plain,
    ( r1_tarski(sK7,X0)
    | r2_hidden(sK1(sK7,X0),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2888,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | r2_hidden(sK1(sK7,X0),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2882])).

cnf(c_2890,plain,
    ( r1_tarski(sK7,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK7,k1_xboole_0),sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2888])).

cnf(c_2907,plain,
    ( r1_tarski(sK6,X0)
    | r2_hidden(sK1(sK6,X0),sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2913,plain,
    ( r1_tarski(sK6,X0) = iProver_top
    | r2_hidden(sK1(sK6,X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2907])).

cnf(c_2915,plain,
    ( r1_tarski(sK6,k1_xboole_0) = iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2913])).

cnf(c_2369,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(X1,sK7)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1291])).

cnf(c_3200,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(sK6,sK7)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_2369])).

cnf(c_3202,plain,
    ( r1_tarski(sK6,sK7)
    | ~ r1_tarski(k1_xboole_0,sK7)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3200])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3366,plain,
    ( ~ r2_hidden(sK1(sK7,X0),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3367,plain,
    ( r2_hidden(sK1(sK7,X0),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3366])).

cnf(c_3369,plain,
    ( r2_hidden(sK1(sK7,k1_xboole_0),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3367])).

cnf(c_3381,plain,
    ( ~ r2_hidden(sK1(sK6,X0),sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3382,plain,
    ( r2_hidden(sK1(sK6,X0),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3381])).

cnf(c_3384,plain,
    ( r2_hidden(sK1(sK6,k1_xboole_0),sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3382])).

cnf(c_4071,plain,
    ( ~ r2_hidden(sK1(X0,sK6),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4073,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4071])).

cnf(c_4072,plain,
    ( r2_hidden(sK1(X0,sK6),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4071])).

cnf(c_4074,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4072])).

cnf(c_4290,plain,
    ( ~ r2_hidden(sK1(X0,sK7),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4292,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4290])).

cnf(c_4291,plain,
    ( r2_hidden(sK1(X0,sK7),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4290])).

cnf(c_4293,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4291])).

cnf(c_4353,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1757])).

cnf(c_4614,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4352,c_5,c_101,c_555,c_2164,c_2252,c_2365,c_2366,c_2379,c_2380,c_2397,c_2458,c_2890,c_2915,c_3202,c_3369,c_3384,c_4073,c_4074,c_4292,c_4293,c_4353])).

cnf(c_4877,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK4,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4873,c_4614])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_4932,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4877,c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4932,c_101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:34:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.02/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/0.98  
% 3.02/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.98  
% 3.02/0.98  ------  iProver source info
% 3.02/0.98  
% 3.02/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.98  git: non_committed_changes: false
% 3.02/0.98  git: last_make_outside_of_git: false
% 3.02/0.98  
% 3.02/0.98  ------ 
% 3.02/0.98  
% 3.02/0.98  ------ Input Options
% 3.02/0.98  
% 3.02/0.98  --out_options                           all
% 3.02/0.98  --tptp_safe_out                         true
% 3.02/0.98  --problem_path                          ""
% 3.02/0.98  --include_path                          ""
% 3.02/0.98  --clausifier                            res/vclausify_rel
% 3.02/0.98  --clausifier_options                    --mode clausify
% 3.02/0.98  --stdin                                 false
% 3.02/0.98  --stats_out                             all
% 3.02/0.98  
% 3.02/0.98  ------ General Options
% 3.02/0.98  
% 3.02/0.98  --fof                                   false
% 3.02/0.98  --time_out_real                         305.
% 3.02/0.98  --time_out_virtual                      -1.
% 3.02/0.98  --symbol_type_check                     false
% 3.02/0.98  --clausify_out                          false
% 3.02/0.98  --sig_cnt_out                           false
% 3.02/0.98  --trig_cnt_out                          false
% 3.02/0.98  --trig_cnt_out_tolerance                1.
% 3.02/0.98  --trig_cnt_out_sk_spl                   false
% 3.02/0.98  --abstr_cl_out                          false
% 3.02/0.98  
% 3.02/0.98  ------ Global Options
% 3.02/0.98  
% 3.02/0.98  --schedule                              default
% 3.02/0.98  --add_important_lit                     false
% 3.02/0.98  --prop_solver_per_cl                    1000
% 3.02/0.98  --min_unsat_core                        false
% 3.02/0.98  --soft_assumptions                      false
% 3.02/0.98  --soft_lemma_size                       3
% 3.02/0.98  --prop_impl_unit_size                   0
% 3.02/0.98  --prop_impl_unit                        []
% 3.02/0.98  --share_sel_clauses                     true
% 3.02/0.98  --reset_solvers                         false
% 3.02/0.98  --bc_imp_inh                            [conj_cone]
% 3.02/0.98  --conj_cone_tolerance                   3.
% 3.02/0.98  --extra_neg_conj                        none
% 3.02/0.98  --large_theory_mode                     true
% 3.02/0.98  --prolific_symb_bound                   200
% 3.02/0.98  --lt_threshold                          2000
% 3.02/0.98  --clause_weak_htbl                      true
% 3.02/0.98  --gc_record_bc_elim                     false
% 3.02/0.98  
% 3.02/0.98  ------ Preprocessing Options
% 3.02/0.98  
% 3.02/0.98  --preprocessing_flag                    true
% 3.02/0.98  --time_out_prep_mult                    0.1
% 3.02/0.98  --splitting_mode                        input
% 3.02/0.98  --splitting_grd                         true
% 3.02/0.98  --splitting_cvd                         false
% 3.02/0.98  --splitting_cvd_svl                     false
% 3.02/0.98  --splitting_nvd                         32
% 3.02/0.98  --sub_typing                            true
% 3.02/0.98  --prep_gs_sim                           true
% 3.02/0.98  --prep_unflatten                        true
% 3.02/0.98  --prep_res_sim                          true
% 3.02/0.98  --prep_upred                            true
% 3.02/0.98  --prep_sem_filter                       exhaustive
% 3.02/0.98  --prep_sem_filter_out                   false
% 3.02/0.98  --pred_elim                             true
% 3.02/0.98  --res_sim_input                         true
% 3.02/0.98  --eq_ax_congr_red                       true
% 3.02/0.98  --pure_diseq_elim                       true
% 3.02/0.98  --brand_transform                       false
% 3.02/0.98  --non_eq_to_eq                          false
% 3.02/0.98  --prep_def_merge                        true
% 3.02/0.98  --prep_def_merge_prop_impl              false
% 3.02/0.98  --prep_def_merge_mbd                    true
% 3.02/0.98  --prep_def_merge_tr_red                 false
% 3.02/0.98  --prep_def_merge_tr_cl                  false
% 3.02/0.98  --smt_preprocessing                     true
% 3.02/0.98  --smt_ac_axioms                         fast
% 3.02/0.98  --preprocessed_out                      false
% 3.02/0.98  --preprocessed_stats                    false
% 3.02/0.98  
% 3.02/0.98  ------ Abstraction refinement Options
% 3.02/0.98  
% 3.02/0.98  --abstr_ref                             []
% 3.02/0.98  --abstr_ref_prep                        false
% 3.02/0.98  --abstr_ref_until_sat                   false
% 3.02/0.98  --abstr_ref_sig_restrict                funpre
% 3.02/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.98  --abstr_ref_under                       []
% 3.02/0.98  
% 3.02/0.98  ------ SAT Options
% 3.02/0.98  
% 3.02/0.98  --sat_mode                              false
% 3.02/0.98  --sat_fm_restart_options                ""
% 3.02/0.98  --sat_gr_def                            false
% 3.02/0.98  --sat_epr_types                         true
% 3.02/0.98  --sat_non_cyclic_types                  false
% 3.02/0.98  --sat_finite_models                     false
% 3.02/0.98  --sat_fm_lemmas                         false
% 3.02/0.98  --sat_fm_prep                           false
% 3.02/0.98  --sat_fm_uc_incr                        true
% 3.02/0.98  --sat_out_model                         small
% 3.02/0.98  --sat_out_clauses                       false
% 3.02/0.98  
% 3.02/0.98  ------ QBF Options
% 3.02/0.98  
% 3.02/0.98  --qbf_mode                              false
% 3.02/0.98  --qbf_elim_univ                         false
% 3.02/0.98  --qbf_dom_inst                          none
% 3.02/0.98  --qbf_dom_pre_inst                      false
% 3.02/0.98  --qbf_sk_in                             false
% 3.02/0.98  --qbf_pred_elim                         true
% 3.02/0.98  --qbf_split                             512
% 3.02/0.98  
% 3.02/0.98  ------ BMC1 Options
% 3.02/0.98  
% 3.02/0.98  --bmc1_incremental                      false
% 3.02/0.98  --bmc1_axioms                           reachable_all
% 3.02/0.98  --bmc1_min_bound                        0
% 3.02/0.98  --bmc1_max_bound                        -1
% 3.02/0.98  --bmc1_max_bound_default                -1
% 3.02/0.98  --bmc1_symbol_reachability              true
% 3.02/0.98  --bmc1_property_lemmas                  false
% 3.02/0.98  --bmc1_k_induction                      false
% 3.02/0.98  --bmc1_non_equiv_states                 false
% 3.02/0.98  --bmc1_deadlock                         false
% 3.02/0.98  --bmc1_ucm                              false
% 3.02/0.98  --bmc1_add_unsat_core                   none
% 3.02/0.98  --bmc1_unsat_core_children              false
% 3.02/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.98  --bmc1_out_stat                         full
% 3.02/0.98  --bmc1_ground_init                      false
% 3.02/0.98  --bmc1_pre_inst_next_state              false
% 3.02/0.98  --bmc1_pre_inst_state                   false
% 3.02/0.98  --bmc1_pre_inst_reach_state             false
% 3.02/0.98  --bmc1_out_unsat_core                   false
% 3.02/0.98  --bmc1_aig_witness_out                  false
% 3.02/0.98  --bmc1_verbose                          false
% 3.02/0.98  --bmc1_dump_clauses_tptp                false
% 3.02/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.98  --bmc1_dump_file                        -
% 3.02/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.98  --bmc1_ucm_extend_mode                  1
% 3.02/0.98  --bmc1_ucm_init_mode                    2
% 3.02/0.98  --bmc1_ucm_cone_mode                    none
% 3.02/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.98  --bmc1_ucm_relax_model                  4
% 3.02/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.98  --bmc1_ucm_layered_model                none
% 3.02/0.98  --bmc1_ucm_max_lemma_size               10
% 3.02/0.98  
% 3.02/0.98  ------ AIG Options
% 3.02/0.98  
% 3.02/0.98  --aig_mode                              false
% 3.02/0.98  
% 3.02/0.98  ------ Instantiation Options
% 3.02/0.98  
% 3.02/0.98  --instantiation_flag                    true
% 3.02/0.98  --inst_sos_flag                         false
% 3.02/0.98  --inst_sos_phase                        true
% 3.02/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.98  --inst_lit_sel_side                     num_symb
% 3.02/0.98  --inst_solver_per_active                1400
% 3.02/0.98  --inst_solver_calls_frac                1.
% 3.02/0.98  --inst_passive_queue_type               priority_queues
% 3.02/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.98  --inst_passive_queues_freq              [25;2]
% 3.02/0.98  --inst_dismatching                      true
% 3.02/0.98  --inst_eager_unprocessed_to_passive     true
% 3.02/0.98  --inst_prop_sim_given                   true
% 3.02/0.98  --inst_prop_sim_new                     false
% 3.02/0.98  --inst_subs_new                         false
% 3.02/0.98  --inst_eq_res_simp                      false
% 3.02/0.98  --inst_subs_given                       false
% 3.02/0.98  --inst_orphan_elimination               true
% 3.02/0.98  --inst_learning_loop_flag               true
% 3.02/0.98  --inst_learning_start                   3000
% 3.02/0.98  --inst_learning_factor                  2
% 3.02/0.98  --inst_start_prop_sim_after_learn       3
% 3.02/0.98  --inst_sel_renew                        solver
% 3.02/0.98  --inst_lit_activity_flag                true
% 3.02/0.98  --inst_restr_to_given                   false
% 3.02/0.98  --inst_activity_threshold               500
% 3.02/0.98  --inst_out_proof                        true
% 3.02/0.98  
% 3.02/0.98  ------ Resolution Options
% 3.02/0.98  
% 3.02/0.98  --resolution_flag                       true
% 3.02/0.98  --res_lit_sel                           adaptive
% 3.02/0.98  --res_lit_sel_side                      none
% 3.02/0.98  --res_ordering                          kbo
% 3.02/0.98  --res_to_prop_solver                    active
% 3.02/0.98  --res_prop_simpl_new                    false
% 3.02/0.98  --res_prop_simpl_given                  true
% 3.02/0.98  --res_passive_queue_type                priority_queues
% 3.02/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.98  --res_passive_queues_freq               [15;5]
% 3.02/0.98  --res_forward_subs                      full
% 3.02/0.98  --res_backward_subs                     full
% 3.02/0.98  --res_forward_subs_resolution           true
% 3.02/0.98  --res_backward_subs_resolution          true
% 3.02/0.98  --res_orphan_elimination                true
% 3.02/0.98  --res_time_limit                        2.
% 3.02/0.98  --res_out_proof                         true
% 3.02/0.98  
% 3.02/0.98  ------ Superposition Options
% 3.02/0.98  
% 3.02/0.98  --superposition_flag                    true
% 3.02/0.98  --sup_passive_queue_type                priority_queues
% 3.02/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.98  --demod_completeness_check              fast
% 3.02/0.98  --demod_use_ground                      true
% 3.02/0.98  --sup_to_prop_solver                    passive
% 3.02/0.98  --sup_prop_simpl_new                    true
% 3.02/0.98  --sup_prop_simpl_given                  true
% 3.02/0.98  --sup_fun_splitting                     false
% 3.02/0.98  --sup_smt_interval                      50000
% 3.02/0.98  
% 3.02/0.98  ------ Superposition Simplification Setup
% 3.02/0.98  
% 3.02/0.98  --sup_indices_passive                   []
% 3.02/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.98  --sup_full_bw                           [BwDemod]
% 3.02/0.98  --sup_immed_triv                        [TrivRules]
% 3.02/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.98  --sup_immed_bw_main                     []
% 3.02/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.98  
% 3.02/0.98  ------ Combination Options
% 3.02/0.98  
% 3.02/0.98  --comb_res_mult                         3
% 3.02/0.98  --comb_sup_mult                         2
% 3.02/0.98  --comb_inst_mult                        10
% 3.02/0.98  
% 3.02/0.98  ------ Debug Options
% 3.02/0.98  
% 3.02/0.98  --dbg_backtrace                         false
% 3.02/0.98  --dbg_dump_prop_clauses                 false
% 3.02/0.98  --dbg_dump_prop_clauses_file            -
% 3.02/0.98  --dbg_out_stat                          false
% 3.02/0.98  ------ Parsing...
% 3.02/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.98  
% 3.02/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.02/0.98  
% 3.02/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.98  
% 3.02/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.98  ------ Proving...
% 3.02/0.98  ------ Problem Properties 
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  clauses                                 30
% 3.02/0.98  conjectures                             5
% 3.02/0.98  EPR                                     7
% 3.02/0.98  Horn                                    22
% 3.02/0.98  unary                                   9
% 3.02/0.98  binary                                  11
% 3.02/0.98  lits                                    71
% 3.02/0.98  lits eq                                 28
% 3.02/0.98  fd_pure                                 0
% 3.02/0.98  fd_pseudo                               0
% 3.02/0.98  fd_cond                                 1
% 3.02/0.98  fd_pseudo_cond                          3
% 3.02/0.98  AC symbols                              0
% 3.02/0.98  
% 3.02/0.98  ------ Schedule dynamic 5 is on 
% 3.02/0.98  
% 3.02/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  ------ 
% 3.02/0.98  Current options:
% 3.02/0.98  ------ 
% 3.02/0.98  
% 3.02/0.98  ------ Input Options
% 3.02/0.98  
% 3.02/0.98  --out_options                           all
% 3.02/0.98  --tptp_safe_out                         true
% 3.02/0.98  --problem_path                          ""
% 3.02/0.98  --include_path                          ""
% 3.02/0.98  --clausifier                            res/vclausify_rel
% 3.02/0.98  --clausifier_options                    --mode clausify
% 3.02/0.98  --stdin                                 false
% 3.02/0.98  --stats_out                             all
% 3.02/0.98  
% 3.02/0.98  ------ General Options
% 3.02/0.98  
% 3.02/0.98  --fof                                   false
% 3.02/0.98  --time_out_real                         305.
% 3.02/0.98  --time_out_virtual                      -1.
% 3.02/0.98  --symbol_type_check                     false
% 3.02/0.98  --clausify_out                          false
% 3.02/0.98  --sig_cnt_out                           false
% 3.02/0.98  --trig_cnt_out                          false
% 3.02/0.98  --trig_cnt_out_tolerance                1.
% 3.02/0.98  --trig_cnt_out_sk_spl                   false
% 3.02/0.98  --abstr_cl_out                          false
% 3.02/0.98  
% 3.02/0.98  ------ Global Options
% 3.02/0.98  
% 3.02/0.98  --schedule                              default
% 3.02/0.98  --add_important_lit                     false
% 3.02/0.98  --prop_solver_per_cl                    1000
% 3.02/0.98  --min_unsat_core                        false
% 3.02/0.98  --soft_assumptions                      false
% 3.02/0.98  --soft_lemma_size                       3
% 3.02/0.98  --prop_impl_unit_size                   0
% 3.02/0.98  --prop_impl_unit                        []
% 3.02/0.98  --share_sel_clauses                     true
% 3.02/0.98  --reset_solvers                         false
% 3.02/0.98  --bc_imp_inh                            [conj_cone]
% 3.02/0.98  --conj_cone_tolerance                   3.
% 3.02/0.98  --extra_neg_conj                        none
% 3.02/0.98  --large_theory_mode                     true
% 3.02/0.98  --prolific_symb_bound                   200
% 3.02/0.98  --lt_threshold                          2000
% 3.02/0.98  --clause_weak_htbl                      true
% 3.02/0.98  --gc_record_bc_elim                     false
% 3.02/0.98  
% 3.02/0.98  ------ Preprocessing Options
% 3.02/0.98  
% 3.02/0.98  --preprocessing_flag                    true
% 3.02/0.98  --time_out_prep_mult                    0.1
% 3.02/0.98  --splitting_mode                        input
% 3.02/0.98  --splitting_grd                         true
% 3.02/0.98  --splitting_cvd                         false
% 3.02/0.98  --splitting_cvd_svl                     false
% 3.02/0.98  --splitting_nvd                         32
% 3.02/0.98  --sub_typing                            true
% 3.02/0.98  --prep_gs_sim                           true
% 3.02/0.98  --prep_unflatten                        true
% 3.02/0.98  --prep_res_sim                          true
% 3.02/0.98  --prep_upred                            true
% 3.02/0.98  --prep_sem_filter                       exhaustive
% 3.02/0.98  --prep_sem_filter_out                   false
% 3.02/0.98  --pred_elim                             true
% 3.02/0.98  --res_sim_input                         true
% 3.02/0.98  --eq_ax_congr_red                       true
% 3.02/0.98  --pure_diseq_elim                       true
% 3.02/0.98  --brand_transform                       false
% 3.02/0.98  --non_eq_to_eq                          false
% 3.02/0.98  --prep_def_merge                        true
% 3.02/0.98  --prep_def_merge_prop_impl              false
% 3.02/0.98  --prep_def_merge_mbd                    true
% 3.02/0.98  --prep_def_merge_tr_red                 false
% 3.02/0.98  --prep_def_merge_tr_cl                  false
% 3.02/0.98  --smt_preprocessing                     true
% 3.02/0.98  --smt_ac_axioms                         fast
% 3.02/0.98  --preprocessed_out                      false
% 3.02/0.98  --preprocessed_stats                    false
% 3.02/0.98  
% 3.02/0.98  ------ Abstraction refinement Options
% 3.02/0.98  
% 3.02/0.98  --abstr_ref                             []
% 3.02/0.98  --abstr_ref_prep                        false
% 3.02/0.98  --abstr_ref_until_sat                   false
% 3.02/0.98  --abstr_ref_sig_restrict                funpre
% 3.02/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.98  --abstr_ref_under                       []
% 3.02/0.98  
% 3.02/0.98  ------ SAT Options
% 3.02/0.98  
% 3.02/0.98  --sat_mode                              false
% 3.02/0.98  --sat_fm_restart_options                ""
% 3.02/0.98  --sat_gr_def                            false
% 3.02/0.98  --sat_epr_types                         true
% 3.02/0.98  --sat_non_cyclic_types                  false
% 3.02/0.98  --sat_finite_models                     false
% 3.02/0.98  --sat_fm_lemmas                         false
% 3.02/0.98  --sat_fm_prep                           false
% 3.02/0.98  --sat_fm_uc_incr                        true
% 3.02/0.98  --sat_out_model                         small
% 3.02/0.98  --sat_out_clauses                       false
% 3.02/0.98  
% 3.02/0.98  ------ QBF Options
% 3.02/0.98  
% 3.02/0.98  --qbf_mode                              false
% 3.02/0.98  --qbf_elim_univ                         false
% 3.02/0.98  --qbf_dom_inst                          none
% 3.02/0.98  --qbf_dom_pre_inst                      false
% 3.02/0.98  --qbf_sk_in                             false
% 3.02/0.98  --qbf_pred_elim                         true
% 3.02/0.98  --qbf_split                             512
% 3.02/0.98  
% 3.02/0.98  ------ BMC1 Options
% 3.02/0.98  
% 3.02/0.98  --bmc1_incremental                      false
% 3.02/0.98  --bmc1_axioms                           reachable_all
% 3.02/0.98  --bmc1_min_bound                        0
% 3.02/0.98  --bmc1_max_bound                        -1
% 3.02/0.98  --bmc1_max_bound_default                -1
% 3.02/0.98  --bmc1_symbol_reachability              true
% 3.02/0.98  --bmc1_property_lemmas                  false
% 3.02/0.98  --bmc1_k_induction                      false
% 3.02/0.98  --bmc1_non_equiv_states                 false
% 3.02/0.98  --bmc1_deadlock                         false
% 3.02/0.98  --bmc1_ucm                              false
% 3.02/0.98  --bmc1_add_unsat_core                   none
% 3.02/0.98  --bmc1_unsat_core_children              false
% 3.02/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.98  --bmc1_out_stat                         full
% 3.02/0.98  --bmc1_ground_init                      false
% 3.02/0.98  --bmc1_pre_inst_next_state              false
% 3.02/0.98  --bmc1_pre_inst_state                   false
% 3.02/0.98  --bmc1_pre_inst_reach_state             false
% 3.02/0.98  --bmc1_out_unsat_core                   false
% 3.02/0.98  --bmc1_aig_witness_out                  false
% 3.02/0.98  --bmc1_verbose                          false
% 3.02/0.98  --bmc1_dump_clauses_tptp                false
% 3.02/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.98  --bmc1_dump_file                        -
% 3.02/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.98  --bmc1_ucm_extend_mode                  1
% 3.02/0.98  --bmc1_ucm_init_mode                    2
% 3.02/0.98  --bmc1_ucm_cone_mode                    none
% 3.02/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.98  --bmc1_ucm_relax_model                  4
% 3.02/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.98  --bmc1_ucm_layered_model                none
% 3.02/0.98  --bmc1_ucm_max_lemma_size               10
% 3.02/0.98  
% 3.02/0.98  ------ AIG Options
% 3.02/0.98  
% 3.02/0.98  --aig_mode                              false
% 3.02/0.98  
% 3.02/0.98  ------ Instantiation Options
% 3.02/0.98  
% 3.02/0.98  --instantiation_flag                    true
% 3.02/0.98  --inst_sos_flag                         false
% 3.02/0.98  --inst_sos_phase                        true
% 3.02/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.98  --inst_lit_sel_side                     none
% 3.02/0.98  --inst_solver_per_active                1400
% 3.02/0.98  --inst_solver_calls_frac                1.
% 3.02/0.98  --inst_passive_queue_type               priority_queues
% 3.02/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.98  --inst_passive_queues_freq              [25;2]
% 3.02/0.98  --inst_dismatching                      true
% 3.02/0.98  --inst_eager_unprocessed_to_passive     true
% 3.02/0.98  --inst_prop_sim_given                   true
% 3.02/0.98  --inst_prop_sim_new                     false
% 3.02/0.98  --inst_subs_new                         false
% 3.02/0.98  --inst_eq_res_simp                      false
% 3.02/0.98  --inst_subs_given                       false
% 3.02/0.98  --inst_orphan_elimination               true
% 3.02/0.98  --inst_learning_loop_flag               true
% 3.02/0.98  --inst_learning_start                   3000
% 3.02/0.98  --inst_learning_factor                  2
% 3.02/0.98  --inst_start_prop_sim_after_learn       3
% 3.02/0.98  --inst_sel_renew                        solver
% 3.02/0.98  --inst_lit_activity_flag                true
% 3.02/0.98  --inst_restr_to_given                   false
% 3.02/0.98  --inst_activity_threshold               500
% 3.02/0.98  --inst_out_proof                        true
% 3.02/0.98  
% 3.02/0.98  ------ Resolution Options
% 3.02/0.98  
% 3.02/0.98  --resolution_flag                       false
% 3.02/0.98  --res_lit_sel                           adaptive
% 3.02/0.98  --res_lit_sel_side                      none
% 3.02/0.98  --res_ordering                          kbo
% 3.02/0.98  --res_to_prop_solver                    active
% 3.02/0.98  --res_prop_simpl_new                    false
% 3.02/0.98  --res_prop_simpl_given                  true
% 3.02/0.98  --res_passive_queue_type                priority_queues
% 3.02/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.98  --res_passive_queues_freq               [15;5]
% 3.02/0.98  --res_forward_subs                      full
% 3.02/0.98  --res_backward_subs                     full
% 3.02/0.98  --res_forward_subs_resolution           true
% 3.02/0.98  --res_backward_subs_resolution          true
% 3.02/0.98  --res_orphan_elimination                true
% 3.02/0.98  --res_time_limit                        2.
% 3.02/0.98  --res_out_proof                         true
% 3.02/0.98  
% 3.02/0.98  ------ Superposition Options
% 3.02/0.98  
% 3.02/0.98  --superposition_flag                    true
% 3.02/0.98  --sup_passive_queue_type                priority_queues
% 3.02/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.98  --demod_completeness_check              fast
% 3.02/0.98  --demod_use_ground                      true
% 3.02/0.98  --sup_to_prop_solver                    passive
% 3.02/0.98  --sup_prop_simpl_new                    true
% 3.02/0.98  --sup_prop_simpl_given                  true
% 3.02/0.98  --sup_fun_splitting                     false
% 3.02/0.98  --sup_smt_interval                      50000
% 3.02/0.98  
% 3.02/0.98  ------ Superposition Simplification Setup
% 3.02/0.98  
% 3.02/0.98  --sup_indices_passive                   []
% 3.02/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.98  --sup_full_bw                           [BwDemod]
% 3.02/0.98  --sup_immed_triv                        [TrivRules]
% 3.02/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.98  --sup_immed_bw_main                     []
% 3.02/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.98  
% 3.02/0.98  ------ Combination Options
% 3.02/0.98  
% 3.02/0.98  --comb_res_mult                         3
% 3.02/0.98  --comb_sup_mult                         2
% 3.02/0.98  --comb_inst_mult                        10
% 3.02/0.98  
% 3.02/0.98  ------ Debug Options
% 3.02/0.98  
% 3.02/0.98  --dbg_backtrace                         false
% 3.02/0.98  --dbg_dump_prop_clauses                 false
% 3.02/0.98  --dbg_dump_prop_clauses_file            -
% 3.02/0.98  --dbg_out_stat                          false
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  ------ Proving...
% 3.02/0.98  
% 3.02/0.98  
% 3.02/0.98  % SZS status Theorem for theBenchmark.p
% 3.02/0.98  
% 3.02/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.98  
% 3.02/0.98  fof(f14,axiom,(
% 3.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f28,plain,(
% 3.02/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.98    inference(ennf_transformation,[],[f14])).
% 3.02/0.98  
% 3.02/0.98  fof(f29,plain,(
% 3.02/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.98    inference(flattening,[],[f28])).
% 3.02/0.98  
% 3.02/0.98  fof(f49,plain,(
% 3.02/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.98    inference(nnf_transformation,[],[f29])).
% 3.02/0.98  
% 3.02/0.98  fof(f75,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.98    inference(cnf_transformation,[],[f49])).
% 3.02/0.98  
% 3.02/0.98  fof(f15,conjecture,(
% 3.02/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f16,negated_conjecture,(
% 3.02/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 3.02/0.98    inference(negated_conjecture,[],[f15])).
% 3.02/0.98  
% 3.02/0.98  fof(f30,plain,(
% 3.02/0.98    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.02/0.98    inference(ennf_transformation,[],[f16])).
% 3.02/0.98  
% 3.02/0.98  fof(f31,plain,(
% 3.02/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.02/0.98    inference(flattening,[],[f30])).
% 3.02/0.98  
% 3.02/0.98  fof(f51,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_relset_1(X0,X1,X2,sK7) & ! [X4] : (k1_funct_1(sK7,X4) = k1_funct_1(X2,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK7,X0,X1) & v1_funct_1(sK7))) )),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f50,plain,(
% 3.02/0.98    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK4,sK5,sK6,X3) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,sK4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(X3,sK4,sK5) & v1_funct_1(X3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f52,plain,(
% 3.02/0.98    (~r2_relset_1(sK4,sK5,sK6,sK7) & ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~r2_hidden(X4,sK4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 3.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f31,f51,f50])).
% 3.02/0.98  
% 3.02/0.98  fof(f82,plain,(
% 3.02/0.98    v1_funct_2(sK6,sK4,sK5)),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f83,plain,(
% 3.02/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f12,axiom,(
% 3.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f25,plain,(
% 3.02/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.98    inference(ennf_transformation,[],[f12])).
% 3.02/0.98  
% 3.02/0.98  fof(f73,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.98    inference(cnf_transformation,[],[f25])).
% 3.02/0.98  
% 3.02/0.98  fof(f9,axiom,(
% 3.02/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f21,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f9])).
% 3.02/0.98  
% 3.02/0.98  fof(f22,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.98    inference(flattening,[],[f21])).
% 3.02/0.98  
% 3.02/0.98  fof(f47,plain,(
% 3.02/0.98    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f48,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f47])).
% 3.02/0.98  
% 3.02/0.98  fof(f69,plain,(
% 3.02/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f48])).
% 3.02/0.98  
% 3.02/0.98  fof(f85,plain,(
% 3.02/0.98    v1_funct_2(sK7,sK4,sK5)),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f86,plain,(
% 3.02/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f84,plain,(
% 3.02/0.98    v1_funct_1(sK7)),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f10,axiom,(
% 3.02/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f23,plain,(
% 3.02/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.98    inference(ennf_transformation,[],[f10])).
% 3.02/0.98  
% 3.02/0.98  fof(f71,plain,(
% 3.02/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.98    inference(cnf_transformation,[],[f23])).
% 3.02/0.98  
% 3.02/0.98  fof(f81,plain,(
% 3.02/0.98    v1_funct_1(sK6)),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f6,axiom,(
% 3.02/0.98    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f44,plain,(
% 3.02/0.98    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f45,plain,(
% 3.02/0.98    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 3.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f6,f44])).
% 3.02/0.98  
% 3.02/0.98  fof(f65,plain,(
% 3.02/0.98    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f45])).
% 3.02/0.98  
% 3.02/0.98  fof(f13,axiom,(
% 3.02/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f26,plain,(
% 3.02/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.02/0.98    inference(ennf_transformation,[],[f13])).
% 3.02/0.98  
% 3.02/0.98  fof(f27,plain,(
% 3.02/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.98    inference(flattening,[],[f26])).
% 3.02/0.98  
% 3.02/0.98  fof(f74,plain,(
% 3.02/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.98    inference(cnf_transformation,[],[f27])).
% 3.02/0.98  
% 3.02/0.98  fof(f88,plain,(
% 3.02/0.98    ~r2_relset_1(sK4,sK5,sK6,sK7)),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f87,plain,(
% 3.02/0.98    ( ! [X4] : (k1_funct_1(sK6,X4) = k1_funct_1(sK7,X4) | ~r2_hidden(X4,sK4)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f52])).
% 3.02/0.98  
% 3.02/0.98  fof(f70,plain,(
% 3.02/0.98    ( ! [X0,X1] : (X0 = X1 | k1_funct_1(X0,sK3(X0,X1)) != k1_funct_1(X1,sK3(X0,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f48])).
% 3.02/0.98  
% 3.02/0.98  fof(f7,axiom,(
% 3.02/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f19,plain,(
% 3.02/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.02/0.98    inference(ennf_transformation,[],[f7])).
% 3.02/0.98  
% 3.02/0.98  fof(f66,plain,(
% 3.02/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f19])).
% 3.02/0.98  
% 3.02/0.98  fof(f3,axiom,(
% 3.02/0.98    v1_xboole_0(k1_xboole_0)),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f58,plain,(
% 3.02/0.98    v1_xboole_0(k1_xboole_0)),
% 3.02/0.98    inference(cnf_transformation,[],[f3])).
% 3.02/0.98  
% 3.02/0.98  fof(f4,axiom,(
% 3.02/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f40,plain,(
% 3.02/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.02/0.98    inference(nnf_transformation,[],[f4])).
% 3.02/0.98  
% 3.02/0.98  fof(f41,plain,(
% 3.02/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.02/0.98    inference(flattening,[],[f40])).
% 3.02/0.98  
% 3.02/0.98  fof(f61,plain,(
% 3.02/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f41])).
% 3.02/0.98  
% 3.02/0.98  fof(f2,axiom,(
% 3.02/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f18,plain,(
% 3.02/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.02/0.98    inference(ennf_transformation,[],[f2])).
% 3.02/0.98  
% 3.02/0.98  fof(f36,plain,(
% 3.02/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.02/0.98    inference(nnf_transformation,[],[f18])).
% 3.02/0.98  
% 3.02/0.98  fof(f37,plain,(
% 3.02/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.02/0.98    inference(rectify,[],[f36])).
% 3.02/0.98  
% 3.02/0.98  fof(f38,plain,(
% 3.02/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f39,plain,(
% 3.02/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.02/0.98  
% 3.02/0.98  fof(f56,plain,(
% 3.02/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f39])).
% 3.02/0.98  
% 3.02/0.98  fof(f1,axiom,(
% 3.02/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f32,plain,(
% 3.02/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.02/0.98    inference(nnf_transformation,[],[f1])).
% 3.02/0.98  
% 3.02/0.98  fof(f33,plain,(
% 3.02/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.02/0.98    inference(rectify,[],[f32])).
% 3.02/0.98  
% 3.02/0.98  fof(f34,plain,(
% 3.02/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.02/0.98    introduced(choice_axiom,[])).
% 3.02/0.98  
% 3.02/0.98  fof(f35,plain,(
% 3.02/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.02/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.02/0.98  
% 3.02/0.98  fof(f53,plain,(
% 3.02/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.02/0.98    inference(cnf_transformation,[],[f35])).
% 3.02/0.98  
% 3.02/0.98  fof(f5,axiom,(
% 3.02/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.02/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.98  
% 3.02/0.98  fof(f42,plain,(
% 3.02/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/0.98    inference(nnf_transformation,[],[f5])).
% 3.02/0.98  
% 3.02/0.98  fof(f43,plain,(
% 3.02/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/0.98    inference(flattening,[],[f42])).
% 3.02/0.98  
% 3.02/0.98  fof(f64,plain,(
% 3.02/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.02/0.98    inference(cnf_transformation,[],[f43])).
% 3.02/0.98  
% 3.02/0.98  fof(f91,plain,(
% 3.02/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.02/0.98    inference(equality_resolution,[],[f64])).
% 3.02/0.98  
% 3.02/0.98  cnf(c_27,plain,
% 3.02/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.02/0.98      | k1_xboole_0 = X2 ),
% 3.02/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_34,negated_conjecture,
% 3.02/0.98      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.02/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_485,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.02/0.98      | sK6 != X0
% 3.02/0.98      | sK5 != X2
% 3.02/0.98      | sK4 != X1
% 3.02/0.98      | k1_xboole_0 = X2 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_486,plain,
% 3.02/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/0.98      | k1_relset_1(sK4,sK5,sK6) = sK4
% 3.02/0.98      | k1_xboole_0 = sK5 ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_485]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_33,negated_conjecture,
% 3.02/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.02/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_488,plain,
% 3.02/0.98      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_486,c_33]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1749,plain,
% 3.02/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_20,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1753,plain,
% 3.02/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2626,plain,
% 3.02/0.98      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_1749,c_1753]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2819,plain,
% 3.02/0.98      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_488,c_2626]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_17,plain,
% 3.02/0.98      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
% 3.02/0.98      | ~ v1_funct_1(X1)
% 3.02/0.98      | ~ v1_funct_1(X0)
% 3.02/0.98      | ~ v1_relat_1(X1)
% 3.02/0.98      | ~ v1_relat_1(X0)
% 3.02/0.98      | X1 = X0
% 3.02/0.98      | k1_relat_1(X0) != k1_relat_1(X1) ),
% 3.02/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1755,plain,
% 3.02/0.98      ( X0 = X1
% 3.02/0.98      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.02/0.98      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.02/0.98      | v1_funct_1(X0) != iProver_top
% 3.02/0.98      | v1_funct_1(X1) != iProver_top
% 3.02/0.98      | v1_relat_1(X1) != iProver_top
% 3.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3669,plain,
% 3.02/0.98      ( k1_relat_1(X0) != sK4
% 3.02/0.98      | sK6 = X0
% 3.02/0.98      | sK5 = k1_xboole_0
% 3.02/0.98      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 3.02/0.98      | v1_funct_1(X0) != iProver_top
% 3.02/0.98      | v1_funct_1(sK6) != iProver_top
% 3.02/0.98      | v1_relat_1(X0) != iProver_top
% 3.02/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_2819,c_1755]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_31,negated_conjecture,
% 3.02/0.98      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.02/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_474,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.02/0.98      | sK7 != X0
% 3.02/0.98      | sK5 != X2
% 3.02/0.98      | sK4 != X1
% 3.02/0.98      | k1_xboole_0 = X2 ),
% 3.02/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_475,plain,
% 3.02/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/0.98      | k1_relset_1(sK4,sK5,sK7) = sK4
% 3.02/0.98      | k1_xboole_0 = sK5 ),
% 3.02/0.98      inference(unflattening,[status(thm)],[c_474]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_30,negated_conjecture,
% 3.02/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.02/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_477,plain,
% 3.02/0.98      ( k1_relset_1(sK4,sK5,sK7) = sK4 | k1_xboole_0 = sK5 ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_475,c_30]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1751,plain,
% 3.02/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2625,plain,
% 3.02/0.98      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_1751,c_1753]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_2753,plain,
% 3.02/0.98      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_477,c_2625]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_3668,plain,
% 3.02/0.98      ( k1_relat_1(X0) != sK4
% 3.02/0.98      | sK7 = X0
% 3.02/0.98      | sK5 = k1_xboole_0
% 3.02/0.98      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.02/0.98      | v1_funct_1(X0) != iProver_top
% 3.02/0.98      | v1_funct_1(sK7) != iProver_top
% 3.02/0.98      | v1_relat_1(X0) != iProver_top
% 3.02/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_2753,c_1755]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_32,negated_conjecture,
% 3.02/0.98      ( v1_funct_1(sK7) ),
% 3.02/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_39,plain,
% 3.02/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_41,plain,
% 3.02/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_18,plain,
% 3.02/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.98      | v1_relat_1(X0) ),
% 3.02/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1984,plain,
% 3.02/0.98      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/0.98      | v1_relat_1(sK7) ),
% 3.02/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_1985,plain,
% 3.02/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.02/0.98      | v1_relat_1(sK7) = iProver_top ),
% 3.02/0.98      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_4142,plain,
% 3.02/0.98      ( v1_relat_1(X0) != iProver_top
% 3.02/0.98      | k1_relat_1(X0) != sK4
% 3.02/0.98      | sK7 = X0
% 3.02/0.98      | sK5 = k1_xboole_0
% 3.02/0.98      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.02/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.02/0.98      inference(global_propositional_subsumption,
% 3.02/0.98                [status(thm)],
% 3.02/0.98                [c_3668,c_39,c_41,c_1985]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_4143,plain,
% 3.02/0.98      ( k1_relat_1(X0) != sK4
% 3.02/0.98      | sK7 = X0
% 3.02/0.98      | sK5 = k1_xboole_0
% 3.02/0.98      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 3.02/0.98      | v1_funct_1(X0) != iProver_top
% 3.02/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.02/0.98      inference(renaming,[status(thm)],[c_4142]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_4155,plain,
% 3.02/0.98      ( sK7 = sK6
% 3.02/0.98      | sK5 = k1_xboole_0
% 3.02/0.98      | r2_hidden(sK3(sK7,sK6),k1_relat_1(sK7)) = iProver_top
% 3.02/0.98      | v1_funct_1(sK6) != iProver_top
% 3.02/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.02/0.98      inference(superposition,[status(thm)],[c_2819,c_4143]) ).
% 3.02/0.98  
% 3.02/0.98  cnf(c_35,negated_conjecture,
% 3.02/0.98      ( v1_funct_1(sK6) ),
% 3.02/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_36,plain,
% 3.02/0.99      ( v1_funct_1(sK6) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_38,plain,
% 3.02/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_12,plain,
% 3.02/0.99      ( m1_subset_1(sK2(X0),X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_21,plain,
% 3.02/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.02/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_28,negated_conjecture,
% 3.02/0.99      ( ~ r2_relset_1(sK4,sK5,sK6,sK7) ),
% 3.02/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_358,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | sK7 != X0
% 3.02/0.99      | sK6 != X0
% 3.02/0.99      | sK5 != X2
% 3.02/0.99      | sK4 != X1 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_359,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/0.99      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/0.99      | sK6 != sK7 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_363,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/0.99      | sK6 != sK7 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_359,c_30]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_554,plain,
% 3.02/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != X0
% 3.02/0.99      | sK2(X0) != X1
% 3.02/0.99      | sK7 != sK6 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_363]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_555,plain,
% 3.02/0.99      ( sK7 != sK6 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_554]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1987,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.02/0.99      | v1_relat_1(sK6) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1988,plain,
% 3.02/0.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.02/0.99      | v1_relat_1(sK6) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1987]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4168,plain,
% 3.02/0.99      ( sK5 = k1_xboole_0
% 3.02/0.99      | r2_hidden(sK3(sK7,sK6),k1_relat_1(sK7)) = iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4155,c_36,c_38,c_555,c_1988]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4174,plain,
% 3.02/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK3(sK7,sK6),sK4) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2753,c_4168]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_29,negated_conjecture,
% 3.02/0.99      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1752,plain,
% 3.02/0.99      ( k1_funct_1(sK6,X0) = k1_funct_1(sK7,X0)
% 3.02/0.99      | r2_hidden(X0,sK4) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4214,plain,
% 3.02/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6)) = k1_funct_1(sK6,sK3(sK7,sK6))
% 3.02/0.99      | sK5 = k1_xboole_0 ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4174,c_1752]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_16,plain,
% 3.02/0.99      ( ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v1_funct_1(X1)
% 3.02/0.99      | ~ v1_relat_1(X0)
% 3.02/0.99      | ~ v1_relat_1(X1)
% 3.02/0.99      | X0 = X1
% 3.02/0.99      | k1_funct_1(X0,sK3(X1,X0)) != k1_funct_1(X1,sK3(X1,X0))
% 3.02/0.99      | k1_relat_1(X1) != k1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1756,plain,
% 3.02/0.99      ( X0 = X1
% 3.02/0.99      | k1_funct_1(X0,sK3(X1,X0)) != k1_funct_1(X1,sK3(X1,X0))
% 3.02/0.99      | k1_relat_1(X1) != k1_relat_1(X0)
% 3.02/0.99      | v1_funct_1(X1) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v1_relat_1(X0) != iProver_top
% 3.02/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4621,plain,
% 3.02/0.99      ( k1_relat_1(sK6) != k1_relat_1(sK7)
% 3.02/0.99      | sK7 = sK6
% 3.02/0.99      | sK5 = k1_xboole_0
% 3.02/0.99      | v1_funct_1(sK7) != iProver_top
% 3.02/0.99      | v1_funct_1(sK6) != iProver_top
% 3.02/0.99      | v1_relat_1(sK7) != iProver_top
% 3.02/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4214,c_1756]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4622,plain,
% 3.02/0.99      ( ~ v1_funct_1(sK7)
% 3.02/0.99      | ~ v1_funct_1(sK6)
% 3.02/0.99      | ~ v1_relat_1(sK7)
% 3.02/0.99      | ~ v1_relat_1(sK6)
% 3.02/0.99      | k1_relat_1(sK6) != k1_relat_1(sK7)
% 3.02/0.99      | sK7 = sK6
% 3.02/0.99      | sK5 = k1_xboole_0 ),
% 3.02/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4621]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4867,plain,
% 3.02/0.99      ( k1_relat_1(sK6) != k1_relat_1(sK7) | sK5 = k1_xboole_0 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4621,c_35,c_33,c_32,c_30,c_555,c_1984,c_1987,c_4622]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4871,plain,
% 3.02/0.99      ( k1_relat_1(sK6) != sK4 | sK5 = k1_xboole_0 ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2753,c_4867]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4873,plain,
% 3.02/0.99      ( sK5 = k1_xboole_0 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_3669,c_2819,c_4871]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_13,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.02/0.99      | ~ v1_xboole_0(X1)
% 3.02/0.99      | v1_xboole_0(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1757,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.02/0.99      | v1_xboole_0(X1) != iProver_top
% 3.02/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4352,plain,
% 3.02/0.99      ( v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.02/0.99      | v1_xboole_0(sK7) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1751,c_1757]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5,plain,
% 3.02/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_101,plain,
% 3.02/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1291,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.02/0.99      theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2162,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,sK6) | r1_tarski(sK7,sK6) | sK7 != X0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1291]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2164,plain,
% 3.02/0.99      ( r1_tarski(sK7,sK6)
% 3.02/0.99      | ~ r1_tarski(k1_xboole_0,sK6)
% 3.02/0.99      | sK7 != k1_xboole_0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2162]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2249,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,sK7) | ~ r1_tarski(sK7,X0) | sK7 = X0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2250,plain,
% 3.02/0.99      ( sK7 = X0
% 3.02/0.99      | r1_tarski(X0,sK7) != iProver_top
% 3.02/0.99      | r1_tarski(sK7,X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2249]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2252,plain,
% 3.02/0.99      ( sK7 = k1_xboole_0
% 3.02/0.99      | r1_tarski(sK7,k1_xboole_0) != iProver_top
% 3.02/0.99      | r1_tarski(k1_xboole_0,sK7) != iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2250]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3,plain,
% 3.02/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2358,plain,
% 3.02/0.99      ( r1_tarski(X0,sK7) | r2_hidden(sK1(X0,sK7),X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2365,plain,
% 3.02/0.99      ( r1_tarski(k1_xboole_0,sK7)
% 3.02/0.99      | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2358]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2364,plain,
% 3.02/0.99      ( r1_tarski(X0,sK7) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(X0,sK7),X0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2358]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2366,plain,
% 3.02/0.99      ( r1_tarski(k1_xboole_0,sK7) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) = iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2364]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2372,plain,
% 3.02/0.99      ( r1_tarski(X0,sK6) | r2_hidden(sK1(X0,sK6),X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2379,plain,
% 3.02/0.99      ( r1_tarski(k1_xboole_0,sK6)
% 3.02/0.99      | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2372]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2378,plain,
% 3.02/0.99      ( r1_tarski(X0,sK6) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2372]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2380,plain,
% 3.02/0.99      ( r1_tarski(k1_xboole_0,sK6) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) = iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2378]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2394,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2395,plain,
% 3.02/0.99      ( sK6 = X0
% 3.02/0.99      | r1_tarski(X0,sK6) != iProver_top
% 3.02/0.99      | r1_tarski(sK6,X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2394]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2397,plain,
% 3.02/0.99      ( sK6 = k1_xboole_0
% 3.02/0.99      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 3.02/0.99      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2395]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2097,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | X0 = sK6 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2458,plain,
% 3.02/0.99      ( ~ r1_tarski(sK7,sK6) | ~ r1_tarski(sK6,sK7) | sK7 = sK6 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2097]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2882,plain,
% 3.02/0.99      ( r1_tarski(sK7,X0) | r2_hidden(sK1(sK7,X0),sK7) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2888,plain,
% 3.02/0.99      ( r1_tarski(sK7,X0) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(sK7,X0),sK7) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2882]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2890,plain,
% 3.02/0.99      ( r1_tarski(sK7,k1_xboole_0) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(sK7,k1_xboole_0),sK7) = iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2888]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2907,plain,
% 3.02/0.99      ( r1_tarski(sK6,X0) | r2_hidden(sK1(sK6,X0),sK6) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2913,plain,
% 3.02/0.99      ( r1_tarski(sK6,X0) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(sK6,X0),sK6) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_2907]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2915,plain,
% 3.02/0.99      ( r1_tarski(sK6,k1_xboole_0) = iProver_top
% 3.02/0.99      | r2_hidden(sK1(sK6,k1_xboole_0),sK6) = iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2913]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2369,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,sK7) | r1_tarski(X1,sK7) | X1 != X0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1291]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3200,plain,
% 3.02/0.99      ( ~ r1_tarski(X0,sK7) | r1_tarski(sK6,sK7) | sK6 != X0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2369]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3202,plain,
% 3.02/0.99      ( r1_tarski(sK6,sK7)
% 3.02/0.99      | ~ r1_tarski(k1_xboole_0,sK7)
% 3.02/0.99      | sK6 != k1_xboole_0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3200]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1,plain,
% 3.02/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3366,plain,
% 3.02/0.99      ( ~ r2_hidden(sK1(sK7,X0),sK7) | ~ v1_xboole_0(sK7) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3367,plain,
% 3.02/0.99      ( r2_hidden(sK1(sK7,X0),sK7) != iProver_top
% 3.02/0.99      | v1_xboole_0(sK7) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3366]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3369,plain,
% 3.02/0.99      ( r2_hidden(sK1(sK7,k1_xboole_0),sK7) != iProver_top
% 3.02/0.99      | v1_xboole_0(sK7) != iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3367]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3381,plain,
% 3.02/0.99      ( ~ r2_hidden(sK1(sK6,X0),sK6) | ~ v1_xboole_0(sK6) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3382,plain,
% 3.02/0.99      ( r2_hidden(sK1(sK6,X0),sK6) != iProver_top
% 3.02/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3381]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3384,plain,
% 3.02/0.99      ( r2_hidden(sK1(sK6,k1_xboole_0),sK6) != iProver_top
% 3.02/0.99      | v1_xboole_0(sK6) != iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3382]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4071,plain,
% 3.02/0.99      ( ~ r2_hidden(sK1(X0,sK6),X0) | ~ v1_xboole_0(X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4073,plain,
% 3.02/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
% 3.02/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_4071]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4072,plain,
% 3.02/0.99      ( r2_hidden(sK1(X0,sK6),X0) != iProver_top
% 3.02/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_4071]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4074,plain,
% 3.02/0.99      ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) != iProver_top
% 3.02/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_4072]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4290,plain,
% 3.02/0.99      ( ~ r2_hidden(sK1(X0,sK7),X0) | ~ v1_xboole_0(X0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4292,plain,
% 3.02/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0)
% 3.02/0.99      | ~ v1_xboole_0(k1_xboole_0) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_4290]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4291,plain,
% 3.02/0.99      ( r2_hidden(sK1(X0,sK7),X0) != iProver_top
% 3.02/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_4290]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4293,plain,
% 3.02/0.99      ( r2_hidden(sK1(k1_xboole_0,sK7),k1_xboole_0) != iProver_top
% 3.02/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_4291]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4353,plain,
% 3.02/0.99      ( v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.02/0.99      | v1_xboole_0(sK6) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1749,c_1757]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4614,plain,
% 3.02/0.99      ( v1_xboole_0(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4352,c_5,c_101,c_555,c_2164,c_2252,c_2365,c_2366,
% 3.02/0.99                 c_2379,c_2380,c_2397,c_2458,c_2890,c_2915,c_3202,c_3369,
% 3.02/0.99                 c_3384,c_4073,c_4074,c_4292,c_4293,c_4353]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4877,plain,
% 3.02/0.99      ( v1_xboole_0(k2_zfmisc_1(sK4,k1_xboole_0)) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4873,c_4614]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_9,plain,
% 3.02/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4932,plain,
% 3.02/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4877,c_9]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(contradiction,plain,
% 3.02/0.99      ( $false ),
% 3.02/0.99      inference(minisat,[status(thm)],[c_4932,c_101]) ).
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  ------                               Statistics
% 3.02/0.99  
% 3.02/0.99  ------ General
% 3.02/0.99  
% 3.02/0.99  abstr_ref_over_cycles:                  0
% 3.02/0.99  abstr_ref_under_cycles:                 0
% 3.02/0.99  gc_basic_clause_elim:                   0
% 3.02/0.99  forced_gc_time:                         0
% 3.02/0.99  parsing_time:                           0.01
% 3.02/0.99  unif_index_cands_time:                  0.
% 3.02/0.99  unif_index_add_time:                    0.
% 3.02/0.99  orderings_time:                         0.
% 3.02/0.99  out_proof_time:                         0.012
% 3.02/0.99  total_time:                             0.167
% 3.02/0.99  num_of_symbols:                         54
% 3.02/0.99  num_of_terms:                           4216
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing
% 3.02/0.99  
% 3.02/0.99  num_of_splits:                          0
% 3.02/0.99  num_of_split_atoms:                     0
% 3.02/0.99  num_of_reused_defs:                     0
% 3.02/0.99  num_eq_ax_congr_red:                    31
% 3.02/0.99  num_of_sem_filtered_clauses:            1
% 3.02/0.99  num_of_subtypes:                        0
% 3.02/0.99  monotx_restored_types:                  0
% 3.02/0.99  sat_num_of_epr_types:                   0
% 3.02/0.99  sat_num_of_non_cyclic_types:            0
% 3.02/0.99  sat_guarded_non_collapsed_types:        0
% 3.02/0.99  num_pure_diseq_elim:                    0
% 3.02/0.99  simp_replaced_by:                       0
% 3.02/0.99  res_preprocessed:                       148
% 3.02/0.99  prep_upred:                             0
% 3.02/0.99  prep_unflattend:                        85
% 3.02/0.99  smt_new_axioms:                         0
% 3.02/0.99  pred_elim_cands:                        6
% 3.02/0.99  pred_elim:                              3
% 3.02/0.99  pred_elim_cl:                           5
% 3.02/0.99  pred_elim_cycles:                       5
% 3.02/0.99  merged_defs:                            0
% 3.02/0.99  merged_defs_ncl:                        0
% 3.02/0.99  bin_hyper_res:                          0
% 3.02/0.99  prep_cycles:                            4
% 3.02/0.99  pred_elim_time:                         0.014
% 3.02/0.99  splitting_time:                         0.
% 3.02/0.99  sem_filter_time:                        0.
% 3.02/0.99  monotx_time:                            0.
% 3.02/0.99  subtype_inf_time:                       0.
% 3.02/0.99  
% 3.02/0.99  ------ Problem properties
% 3.02/0.99  
% 3.02/0.99  clauses:                                30
% 3.02/0.99  conjectures:                            5
% 3.02/0.99  epr:                                    7
% 3.02/0.99  horn:                                   22
% 3.02/0.99  ground:                                 11
% 3.02/0.99  unary:                                  9
% 3.02/0.99  binary:                                 11
% 3.02/0.99  lits:                                   71
% 3.02/0.99  lits_eq:                                28
% 3.02/0.99  fd_pure:                                0
% 3.02/0.99  fd_pseudo:                              0
% 3.02/0.99  fd_cond:                                1
% 3.02/0.99  fd_pseudo_cond:                         3
% 3.02/0.99  ac_symbols:                             0
% 3.02/0.99  
% 3.02/0.99  ------ Propositional Solver
% 3.02/0.99  
% 3.02/0.99  prop_solver_calls:                      28
% 3.02/0.99  prop_fast_solver_calls:                 1049
% 3.02/0.99  smt_solver_calls:                       0
% 3.02/0.99  smt_fast_solver_calls:                  0
% 3.02/0.99  prop_num_of_clauses:                    1522
% 3.02/0.99  prop_preprocess_simplified:             5427
% 3.02/0.99  prop_fo_subsumed:                       22
% 3.02/0.99  prop_solver_time:                       0.
% 3.02/0.99  smt_solver_time:                        0.
% 3.02/0.99  smt_fast_solver_time:                   0.
% 3.02/0.99  prop_fast_solver_time:                  0.
% 3.02/0.99  prop_unsat_core_time:                   0.
% 3.02/0.99  
% 3.02/0.99  ------ QBF
% 3.02/0.99  
% 3.02/0.99  qbf_q_res:                              0
% 3.02/0.99  qbf_num_tautologies:                    0
% 3.02/0.99  qbf_prep_cycles:                        0
% 3.02/0.99  
% 3.02/0.99  ------ BMC1
% 3.02/0.99  
% 3.02/0.99  bmc1_current_bound:                     -1
% 3.02/0.99  bmc1_last_solved_bound:                 -1
% 3.02/0.99  bmc1_unsat_core_size:                   -1
% 3.02/0.99  bmc1_unsat_core_parents_size:           -1
% 3.02/0.99  bmc1_merge_next_fun:                    0
% 3.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation
% 3.02/0.99  
% 3.02/0.99  inst_num_of_clauses:                    493
% 3.02/0.99  inst_num_in_passive:                    71
% 3.02/0.99  inst_num_in_active:                     277
% 3.02/0.99  inst_num_in_unprocessed:                147
% 3.02/0.99  inst_num_of_loops:                      350
% 3.02/0.99  inst_num_of_learning_restarts:          0
% 3.02/0.99  inst_num_moves_active_passive:          70
% 3.02/0.99  inst_lit_activity:                      0
% 3.02/0.99  inst_lit_activity_moves:                0
% 3.02/0.99  inst_num_tautologies:                   0
% 3.02/0.99  inst_num_prop_implied:                  0
% 3.02/0.99  inst_num_existing_simplified:           0
% 3.02/0.99  inst_num_eq_res_simplified:             0
% 3.02/0.99  inst_num_child_elim:                    0
% 3.02/0.99  inst_num_of_dismatching_blockings:      108
% 3.02/0.99  inst_num_of_non_proper_insts:           507
% 3.02/0.99  inst_num_of_duplicates:                 0
% 3.02/0.99  inst_inst_num_from_inst_to_res:         0
% 3.02/0.99  inst_dismatching_checking_time:         0.
% 3.02/0.99  
% 3.02/0.99  ------ Resolution
% 3.02/0.99  
% 3.02/0.99  res_num_of_clauses:                     0
% 3.02/0.99  res_num_in_passive:                     0
% 3.02/0.99  res_num_in_active:                      0
% 3.02/0.99  res_num_of_loops:                       152
% 3.02/0.99  res_forward_subset_subsumed:            79
% 3.02/0.99  res_backward_subset_subsumed:           4
% 3.02/0.99  res_forward_subsumed:                   0
% 3.02/0.99  res_backward_subsumed:                  0
% 3.02/0.99  res_forward_subsumption_resolution:     0
% 3.02/0.99  res_backward_subsumption_resolution:    0
% 3.02/0.99  res_clause_to_clause_subsumption:       180
% 3.02/0.99  res_orphan_elimination:                 0
% 3.02/0.99  res_tautology_del:                      33
% 3.02/0.99  res_num_eq_res_simplified:              0
% 3.02/0.99  res_num_sel_changes:                    0
% 3.02/0.99  res_moves_from_active_to_pass:          0
% 3.02/0.99  
% 3.02/0.99  ------ Superposition
% 3.02/0.99  
% 3.02/0.99  sup_time_total:                         0.
% 3.02/0.99  sup_time_generating:                    0.
% 3.02/0.99  sup_time_sim_full:                      0.
% 3.02/0.99  sup_time_sim_immed:                     0.
% 3.02/0.99  
% 3.02/0.99  sup_num_of_clauses:                     87
% 3.02/0.99  sup_num_in_active:                      51
% 3.02/0.99  sup_num_in_passive:                     36
% 3.02/0.99  sup_num_of_loops:                       69
% 3.02/0.99  sup_fw_superposition:                   80
% 3.02/0.99  sup_bw_superposition:                   14
% 3.02/0.99  sup_immediate_simplified:               17
% 3.02/0.99  sup_given_eliminated:                   0
% 3.02/0.99  comparisons_done:                       0
% 3.02/0.99  comparisons_avoided:                    20
% 3.02/0.99  
% 3.02/0.99  ------ Simplifications
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  sim_fw_subset_subsumed:                 4
% 3.02/0.99  sim_bw_subset_subsumed:                 5
% 3.02/0.99  sim_fw_subsumed:                        3
% 3.02/0.99  sim_bw_subsumed:                        1
% 3.02/0.99  sim_fw_subsumption_res:                 4
% 3.02/0.99  sim_bw_subsumption_res:                 0
% 3.02/0.99  sim_tautology_del:                      4
% 3.02/0.99  sim_eq_tautology_del:                   10
% 3.02/0.99  sim_eq_res_simp:                        2
% 3.02/0.99  sim_fw_demodulated:                     8
% 3.02/0.99  sim_bw_demodulated:                     14
% 3.02/0.99  sim_light_normalised:                   2
% 3.02/0.99  sim_joinable_taut:                      0
% 3.02/0.99  sim_joinable_simp:                      0
% 3.02/0.99  sim_ac_normalised:                      0
% 3.02/0.99  sim_smt_subsumption:                    0
% 3.02/0.99  
%------------------------------------------------------------------------------
