%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:05 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 416 expanded)
%              Number of clauses        :   89 ( 144 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :   23
%              Number of atoms          :  589 (1988 expanded)
%              Number of equality atoms :  207 ( 448 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f50,plain,(
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

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ m1_subset_1(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ m1_subset_1(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f33,f52,f51])).

fof(f91,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f53])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
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

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f90,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2167,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_856,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_39])).

cnf(c_857,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_856])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_859,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_857,c_38])).

cnf(c_2158,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2162,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4394,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_2158,c_2162])).

cnf(c_4509,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_859,c_4394])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2165,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7352,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4509,c_2165])).

cnf(c_43,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2444,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2445,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2444])).

cnf(c_7689,plain,
    ( r2_hidden(sK2(X0,X1,sK6),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7352,c_43,c_2445])).

cnf(c_7690,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK6),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_7689])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2169,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7698,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK2(X0,X1,sK6),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7690,c_2169])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2161,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3826,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_2158,c_2161])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2159,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4513,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3826,c_2159])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2166,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_551,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_40])).

cnf(c_552,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_2157,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_553,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_2484,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2157,c_43,c_553,c_2445])).

cnf(c_2485,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_2484])).

cnf(c_9116,plain,
    ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2166,c_2485])).

cnf(c_10490,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9116,c_43,c_2445])).

cnf(c_10491,plain,
    ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10490])).

cnf(c_10504,plain,
    ( k1_funct_1(sK6,sK2(sK7,sK5,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_4513,c_10491])).

cnf(c_36,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2160,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10570,plain,
    ( m1_subset_1(sK2(sK7,sK5,sK6),sK3) != iProver_top
    | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10504,c_2160])).

cnf(c_10807,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7698,c_10570])).

cnf(c_10952,plain,
    ( r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10807,c_4513])).

cnf(c_10953,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_10952])).

cnf(c_10958,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_10953])).

cnf(c_10961,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10958,c_43,c_2445,c_4513])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5243,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3826,c_2163])).

cnf(c_6422,plain,
    ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5243,c_43])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_988,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_1058,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_537,c_988])).

cnf(c_2152,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_6429,plain,
    ( r1_tarski(k9_relat_1(sK6,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6422,c_2152])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2174,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6435,plain,
    ( k2_xboole_0(k9_relat_1(sK6,X0),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_6429,c_2174])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2180,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6700,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6435,c_2180])).

cnf(c_6712,plain,
    ( r2_hidden(sK7,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4513,c_6700])).

cnf(c_10970,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10961,c_6712])).

cnf(c_1401,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2504,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | X1 != k7_relset_1(sK3,sK4,sK6,sK5)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2858,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | X0 != k7_relset_1(sK3,sK4,sK6,sK5)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2504])).

cnf(c_6379,plain,
    ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0))
    | k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0) != k7_relset_1(sK3,sK4,sK6,sK5)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_6381,plain,
    ( k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0) != k7_relset_1(sK3,sK4,sK6,sK5)
    | sK7 != sK7
    | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
    | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6379])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3600,plain,
    ( k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0) = k7_relset_1(sK3,sK4,sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1399,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2859,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2478,plain,
    ( ~ r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | ~ r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2479,plain,
    ( r2_hidden(sK7,X0) != iProver_top
    | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
    | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2478])).

cnf(c_2481,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
    | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0)) != iProver_top
    | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2479])).

cnf(c_44,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10970,c_6381,c_3600,c_2859,c_2481,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:51 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 3.49/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/1.00  
% 3.49/1.00  ------  iProver source info
% 3.49/1.00  
% 3.49/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.49/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/1.00  git: non_committed_changes: false
% 3.49/1.00  git: last_make_outside_of_git: false
% 3.49/1.00  
% 3.49/1.00  ------ 
% 3.49/1.00  
% 3.49/1.00  ------ Input Options
% 3.49/1.00  
% 3.49/1.00  --out_options                           all
% 3.49/1.00  --tptp_safe_out                         true
% 3.49/1.00  --problem_path                          ""
% 3.49/1.00  --include_path                          ""
% 3.49/1.00  --clausifier                            res/vclausify_rel
% 3.49/1.00  --clausifier_options                    --mode clausify
% 3.49/1.00  --stdin                                 false
% 3.49/1.00  --stats_out                             all
% 3.49/1.00  
% 3.49/1.00  ------ General Options
% 3.49/1.00  
% 3.49/1.00  --fof                                   false
% 3.49/1.00  --time_out_real                         305.
% 3.49/1.00  --time_out_virtual                      -1.
% 3.49/1.00  --symbol_type_check                     false
% 3.49/1.00  --clausify_out                          false
% 3.49/1.00  --sig_cnt_out                           false
% 3.49/1.00  --trig_cnt_out                          false
% 3.49/1.00  --trig_cnt_out_tolerance                1.
% 3.49/1.00  --trig_cnt_out_sk_spl                   false
% 3.49/1.00  --abstr_cl_out                          false
% 3.49/1.00  
% 3.49/1.00  ------ Global Options
% 3.49/1.00  
% 3.49/1.00  --schedule                              default
% 3.49/1.00  --add_important_lit                     false
% 3.49/1.00  --prop_solver_per_cl                    1000
% 3.49/1.00  --min_unsat_core                        false
% 3.49/1.00  --soft_assumptions                      false
% 3.49/1.00  --soft_lemma_size                       3
% 3.49/1.00  --prop_impl_unit_size                   0
% 3.49/1.00  --prop_impl_unit                        []
% 3.49/1.00  --share_sel_clauses                     true
% 3.49/1.00  --reset_solvers                         false
% 3.49/1.00  --bc_imp_inh                            [conj_cone]
% 3.49/1.00  --conj_cone_tolerance                   3.
% 3.49/1.00  --extra_neg_conj                        none
% 3.49/1.00  --large_theory_mode                     true
% 3.49/1.00  --prolific_symb_bound                   200
% 3.49/1.00  --lt_threshold                          2000
% 3.49/1.00  --clause_weak_htbl                      true
% 3.49/1.00  --gc_record_bc_elim                     false
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing Options
% 3.49/1.00  
% 3.49/1.00  --preprocessing_flag                    true
% 3.49/1.00  --time_out_prep_mult                    0.1
% 3.49/1.00  --splitting_mode                        input
% 3.49/1.00  --splitting_grd                         true
% 3.49/1.00  --splitting_cvd                         false
% 3.49/1.00  --splitting_cvd_svl                     false
% 3.49/1.00  --splitting_nvd                         32
% 3.49/1.00  --sub_typing                            true
% 3.49/1.00  --prep_gs_sim                           true
% 3.49/1.00  --prep_unflatten                        true
% 3.49/1.00  --prep_res_sim                          true
% 3.49/1.00  --prep_upred                            true
% 3.49/1.00  --prep_sem_filter                       exhaustive
% 3.49/1.00  --prep_sem_filter_out                   false
% 3.49/1.00  --pred_elim                             true
% 3.49/1.00  --res_sim_input                         true
% 3.49/1.00  --eq_ax_congr_red                       true
% 3.49/1.00  --pure_diseq_elim                       true
% 3.49/1.00  --brand_transform                       false
% 3.49/1.00  --non_eq_to_eq                          false
% 3.49/1.00  --prep_def_merge                        true
% 3.49/1.00  --prep_def_merge_prop_impl              false
% 3.49/1.00  --prep_def_merge_mbd                    true
% 3.49/1.00  --prep_def_merge_tr_red                 false
% 3.49/1.00  --prep_def_merge_tr_cl                  false
% 3.49/1.00  --smt_preprocessing                     true
% 3.49/1.00  --smt_ac_axioms                         fast
% 3.49/1.00  --preprocessed_out                      false
% 3.49/1.00  --preprocessed_stats                    false
% 3.49/1.00  
% 3.49/1.00  ------ Abstraction refinement Options
% 3.49/1.00  
% 3.49/1.00  --abstr_ref                             []
% 3.49/1.00  --abstr_ref_prep                        false
% 3.49/1.00  --abstr_ref_until_sat                   false
% 3.49/1.00  --abstr_ref_sig_restrict                funpre
% 3.49/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.00  --abstr_ref_under                       []
% 3.49/1.00  
% 3.49/1.00  ------ SAT Options
% 3.49/1.00  
% 3.49/1.00  --sat_mode                              false
% 3.49/1.00  --sat_fm_restart_options                ""
% 3.49/1.00  --sat_gr_def                            false
% 3.49/1.00  --sat_epr_types                         true
% 3.49/1.00  --sat_non_cyclic_types                  false
% 3.49/1.00  --sat_finite_models                     false
% 3.49/1.00  --sat_fm_lemmas                         false
% 3.49/1.00  --sat_fm_prep                           false
% 3.49/1.00  --sat_fm_uc_incr                        true
% 3.49/1.00  --sat_out_model                         small
% 3.49/1.00  --sat_out_clauses                       false
% 3.49/1.00  
% 3.49/1.00  ------ QBF Options
% 3.49/1.00  
% 3.49/1.00  --qbf_mode                              false
% 3.49/1.00  --qbf_elim_univ                         false
% 3.49/1.00  --qbf_dom_inst                          none
% 3.49/1.00  --qbf_dom_pre_inst                      false
% 3.49/1.00  --qbf_sk_in                             false
% 3.49/1.00  --qbf_pred_elim                         true
% 3.49/1.00  --qbf_split                             512
% 3.49/1.00  
% 3.49/1.00  ------ BMC1 Options
% 3.49/1.00  
% 3.49/1.00  --bmc1_incremental                      false
% 3.49/1.00  --bmc1_axioms                           reachable_all
% 3.49/1.00  --bmc1_min_bound                        0
% 3.49/1.00  --bmc1_max_bound                        -1
% 3.49/1.00  --bmc1_max_bound_default                -1
% 3.49/1.00  --bmc1_symbol_reachability              true
% 3.49/1.00  --bmc1_property_lemmas                  false
% 3.49/1.00  --bmc1_k_induction                      false
% 3.49/1.00  --bmc1_non_equiv_states                 false
% 3.49/1.00  --bmc1_deadlock                         false
% 3.49/1.00  --bmc1_ucm                              false
% 3.49/1.00  --bmc1_add_unsat_core                   none
% 3.49/1.00  --bmc1_unsat_core_children              false
% 3.49/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.00  --bmc1_out_stat                         full
% 3.49/1.00  --bmc1_ground_init                      false
% 3.49/1.00  --bmc1_pre_inst_next_state              false
% 3.49/1.00  --bmc1_pre_inst_state                   false
% 3.49/1.00  --bmc1_pre_inst_reach_state             false
% 3.49/1.00  --bmc1_out_unsat_core                   false
% 3.49/1.00  --bmc1_aig_witness_out                  false
% 3.49/1.00  --bmc1_verbose                          false
% 3.49/1.00  --bmc1_dump_clauses_tptp                false
% 3.49/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.00  --bmc1_dump_file                        -
% 3.49/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.00  --bmc1_ucm_extend_mode                  1
% 3.49/1.00  --bmc1_ucm_init_mode                    2
% 3.49/1.00  --bmc1_ucm_cone_mode                    none
% 3.49/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.00  --bmc1_ucm_relax_model                  4
% 3.49/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.00  --bmc1_ucm_layered_model                none
% 3.49/1.00  --bmc1_ucm_max_lemma_size               10
% 3.49/1.00  
% 3.49/1.00  ------ AIG Options
% 3.49/1.00  
% 3.49/1.00  --aig_mode                              false
% 3.49/1.00  
% 3.49/1.00  ------ Instantiation Options
% 3.49/1.00  
% 3.49/1.00  --instantiation_flag                    true
% 3.49/1.00  --inst_sos_flag                         false
% 3.49/1.00  --inst_sos_phase                        true
% 3.49/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel_side                     num_symb
% 3.49/1.00  --inst_solver_per_active                1400
% 3.49/1.00  --inst_solver_calls_frac                1.
% 3.49/1.00  --inst_passive_queue_type               priority_queues
% 3.49/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.00  --inst_passive_queues_freq              [25;2]
% 3.49/1.00  --inst_dismatching                      true
% 3.49/1.00  --inst_eager_unprocessed_to_passive     true
% 3.49/1.00  --inst_prop_sim_given                   true
% 3.49/1.00  --inst_prop_sim_new                     false
% 3.49/1.00  --inst_subs_new                         false
% 3.49/1.00  --inst_eq_res_simp                      false
% 3.49/1.00  --inst_subs_given                       false
% 3.49/1.00  --inst_orphan_elimination               true
% 3.49/1.00  --inst_learning_loop_flag               true
% 3.49/1.00  --inst_learning_start                   3000
% 3.49/1.00  --inst_learning_factor                  2
% 3.49/1.00  --inst_start_prop_sim_after_learn       3
% 3.49/1.00  --inst_sel_renew                        solver
% 3.49/1.00  --inst_lit_activity_flag                true
% 3.49/1.00  --inst_restr_to_given                   false
% 3.49/1.00  --inst_activity_threshold               500
% 3.49/1.00  --inst_out_proof                        true
% 3.49/1.00  
% 3.49/1.00  ------ Resolution Options
% 3.49/1.00  
% 3.49/1.00  --resolution_flag                       true
% 3.49/1.00  --res_lit_sel                           adaptive
% 3.49/1.00  --res_lit_sel_side                      none
% 3.49/1.00  --res_ordering                          kbo
% 3.49/1.00  --res_to_prop_solver                    active
% 3.49/1.00  --res_prop_simpl_new                    false
% 3.49/1.00  --res_prop_simpl_given                  true
% 3.49/1.00  --res_passive_queue_type                priority_queues
% 3.49/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.00  --res_passive_queues_freq               [15;5]
% 3.49/1.00  --res_forward_subs                      full
% 3.49/1.00  --res_backward_subs                     full
% 3.49/1.00  --res_forward_subs_resolution           true
% 3.49/1.00  --res_backward_subs_resolution          true
% 3.49/1.00  --res_orphan_elimination                true
% 3.49/1.00  --res_time_limit                        2.
% 3.49/1.00  --res_out_proof                         true
% 3.49/1.00  
% 3.49/1.00  ------ Superposition Options
% 3.49/1.00  
% 3.49/1.00  --superposition_flag                    true
% 3.49/1.00  --sup_passive_queue_type                priority_queues
% 3.49/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.00  --demod_completeness_check              fast
% 3.49/1.00  --demod_use_ground                      true
% 3.49/1.00  --sup_to_prop_solver                    passive
% 3.49/1.00  --sup_prop_simpl_new                    true
% 3.49/1.00  --sup_prop_simpl_given                  true
% 3.49/1.00  --sup_fun_splitting                     false
% 3.49/1.00  --sup_smt_interval                      50000
% 3.49/1.00  
% 3.49/1.00  ------ Superposition Simplification Setup
% 3.49/1.00  
% 3.49/1.00  --sup_indices_passive                   []
% 3.49/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.00  --sup_full_bw                           [BwDemod]
% 3.49/1.00  --sup_immed_triv                        [TrivRules]
% 3.49/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.00  --sup_immed_bw_main                     []
% 3.49/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.00  
% 3.49/1.00  ------ Combination Options
% 3.49/1.00  
% 3.49/1.00  --comb_res_mult                         3
% 3.49/1.00  --comb_sup_mult                         2
% 3.49/1.00  --comb_inst_mult                        10
% 3.49/1.00  
% 3.49/1.00  ------ Debug Options
% 3.49/1.00  
% 3.49/1.00  --dbg_backtrace                         false
% 3.49/1.00  --dbg_dump_prop_clauses                 false
% 3.49/1.00  --dbg_dump_prop_clauses_file            -
% 3.49/1.00  --dbg_out_stat                          false
% 3.49/1.00  ------ Parsing...
% 3.49/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/1.00  ------ Proving...
% 3.49/1.00  ------ Problem Properties 
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  clauses                                 35
% 3.49/1.00  conjectures                             3
% 3.49/1.00  EPR                                     1
% 3.49/1.00  Horn                                    27
% 3.49/1.00  unary                                   3
% 3.49/1.00  binary                                  12
% 3.49/1.00  lits                                    91
% 3.49/1.00  lits eq                                 18
% 3.49/1.00  fd_pure                                 0
% 3.49/1.00  fd_pseudo                               0
% 3.49/1.00  fd_cond                                 0
% 3.49/1.00  fd_pseudo_cond                          6
% 3.49/1.00  AC symbols                              0
% 3.49/1.00  
% 3.49/1.00  ------ Schedule dynamic 5 is on 
% 3.49/1.00  
% 3.49/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  ------ 
% 3.49/1.00  Current options:
% 3.49/1.00  ------ 
% 3.49/1.00  
% 3.49/1.00  ------ Input Options
% 3.49/1.00  
% 3.49/1.00  --out_options                           all
% 3.49/1.00  --tptp_safe_out                         true
% 3.49/1.00  --problem_path                          ""
% 3.49/1.00  --include_path                          ""
% 3.49/1.00  --clausifier                            res/vclausify_rel
% 3.49/1.00  --clausifier_options                    --mode clausify
% 3.49/1.00  --stdin                                 false
% 3.49/1.00  --stats_out                             all
% 3.49/1.00  
% 3.49/1.00  ------ General Options
% 3.49/1.00  
% 3.49/1.00  --fof                                   false
% 3.49/1.00  --time_out_real                         305.
% 3.49/1.00  --time_out_virtual                      -1.
% 3.49/1.00  --symbol_type_check                     false
% 3.49/1.00  --clausify_out                          false
% 3.49/1.00  --sig_cnt_out                           false
% 3.49/1.00  --trig_cnt_out                          false
% 3.49/1.00  --trig_cnt_out_tolerance                1.
% 3.49/1.00  --trig_cnt_out_sk_spl                   false
% 3.49/1.00  --abstr_cl_out                          false
% 3.49/1.00  
% 3.49/1.00  ------ Global Options
% 3.49/1.00  
% 3.49/1.00  --schedule                              default
% 3.49/1.00  --add_important_lit                     false
% 3.49/1.00  --prop_solver_per_cl                    1000
% 3.49/1.00  --min_unsat_core                        false
% 3.49/1.00  --soft_assumptions                      false
% 3.49/1.00  --soft_lemma_size                       3
% 3.49/1.00  --prop_impl_unit_size                   0
% 3.49/1.00  --prop_impl_unit                        []
% 3.49/1.00  --share_sel_clauses                     true
% 3.49/1.00  --reset_solvers                         false
% 3.49/1.00  --bc_imp_inh                            [conj_cone]
% 3.49/1.00  --conj_cone_tolerance                   3.
% 3.49/1.00  --extra_neg_conj                        none
% 3.49/1.00  --large_theory_mode                     true
% 3.49/1.00  --prolific_symb_bound                   200
% 3.49/1.00  --lt_threshold                          2000
% 3.49/1.00  --clause_weak_htbl                      true
% 3.49/1.00  --gc_record_bc_elim                     false
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing Options
% 3.49/1.00  
% 3.49/1.00  --preprocessing_flag                    true
% 3.49/1.00  --time_out_prep_mult                    0.1
% 3.49/1.00  --splitting_mode                        input
% 3.49/1.00  --splitting_grd                         true
% 3.49/1.00  --splitting_cvd                         false
% 3.49/1.00  --splitting_cvd_svl                     false
% 3.49/1.00  --splitting_nvd                         32
% 3.49/1.00  --sub_typing                            true
% 3.49/1.00  --prep_gs_sim                           true
% 3.49/1.00  --prep_unflatten                        true
% 3.49/1.00  --prep_res_sim                          true
% 3.49/1.00  --prep_upred                            true
% 3.49/1.00  --prep_sem_filter                       exhaustive
% 3.49/1.00  --prep_sem_filter_out                   false
% 3.49/1.00  --pred_elim                             true
% 3.49/1.00  --res_sim_input                         true
% 3.49/1.00  --eq_ax_congr_red                       true
% 3.49/1.00  --pure_diseq_elim                       true
% 3.49/1.00  --brand_transform                       false
% 3.49/1.00  --non_eq_to_eq                          false
% 3.49/1.00  --prep_def_merge                        true
% 3.49/1.00  --prep_def_merge_prop_impl              false
% 3.49/1.00  --prep_def_merge_mbd                    true
% 3.49/1.00  --prep_def_merge_tr_red                 false
% 3.49/1.00  --prep_def_merge_tr_cl                  false
% 3.49/1.00  --smt_preprocessing                     true
% 3.49/1.00  --smt_ac_axioms                         fast
% 3.49/1.00  --preprocessed_out                      false
% 3.49/1.00  --preprocessed_stats                    false
% 3.49/1.00  
% 3.49/1.00  ------ Abstraction refinement Options
% 3.49/1.00  
% 3.49/1.00  --abstr_ref                             []
% 3.49/1.00  --abstr_ref_prep                        false
% 3.49/1.00  --abstr_ref_until_sat                   false
% 3.49/1.00  --abstr_ref_sig_restrict                funpre
% 3.49/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.00  --abstr_ref_under                       []
% 3.49/1.00  
% 3.49/1.00  ------ SAT Options
% 3.49/1.00  
% 3.49/1.00  --sat_mode                              false
% 3.49/1.00  --sat_fm_restart_options                ""
% 3.49/1.00  --sat_gr_def                            false
% 3.49/1.00  --sat_epr_types                         true
% 3.49/1.00  --sat_non_cyclic_types                  false
% 3.49/1.00  --sat_finite_models                     false
% 3.49/1.00  --sat_fm_lemmas                         false
% 3.49/1.00  --sat_fm_prep                           false
% 3.49/1.00  --sat_fm_uc_incr                        true
% 3.49/1.00  --sat_out_model                         small
% 3.49/1.00  --sat_out_clauses                       false
% 3.49/1.00  
% 3.49/1.00  ------ QBF Options
% 3.49/1.00  
% 3.49/1.00  --qbf_mode                              false
% 3.49/1.00  --qbf_elim_univ                         false
% 3.49/1.00  --qbf_dom_inst                          none
% 3.49/1.00  --qbf_dom_pre_inst                      false
% 3.49/1.00  --qbf_sk_in                             false
% 3.49/1.00  --qbf_pred_elim                         true
% 3.49/1.00  --qbf_split                             512
% 3.49/1.00  
% 3.49/1.00  ------ BMC1 Options
% 3.49/1.00  
% 3.49/1.00  --bmc1_incremental                      false
% 3.49/1.00  --bmc1_axioms                           reachable_all
% 3.49/1.00  --bmc1_min_bound                        0
% 3.49/1.00  --bmc1_max_bound                        -1
% 3.49/1.00  --bmc1_max_bound_default                -1
% 3.49/1.00  --bmc1_symbol_reachability              true
% 3.49/1.00  --bmc1_property_lemmas                  false
% 3.49/1.00  --bmc1_k_induction                      false
% 3.49/1.00  --bmc1_non_equiv_states                 false
% 3.49/1.00  --bmc1_deadlock                         false
% 3.49/1.00  --bmc1_ucm                              false
% 3.49/1.00  --bmc1_add_unsat_core                   none
% 3.49/1.00  --bmc1_unsat_core_children              false
% 3.49/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.00  --bmc1_out_stat                         full
% 3.49/1.00  --bmc1_ground_init                      false
% 3.49/1.00  --bmc1_pre_inst_next_state              false
% 3.49/1.00  --bmc1_pre_inst_state                   false
% 3.49/1.00  --bmc1_pre_inst_reach_state             false
% 3.49/1.00  --bmc1_out_unsat_core                   false
% 3.49/1.00  --bmc1_aig_witness_out                  false
% 3.49/1.00  --bmc1_verbose                          false
% 3.49/1.00  --bmc1_dump_clauses_tptp                false
% 3.49/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.00  --bmc1_dump_file                        -
% 3.49/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.00  --bmc1_ucm_extend_mode                  1
% 3.49/1.00  --bmc1_ucm_init_mode                    2
% 3.49/1.00  --bmc1_ucm_cone_mode                    none
% 3.49/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.00  --bmc1_ucm_relax_model                  4
% 3.49/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.00  --bmc1_ucm_layered_model                none
% 3.49/1.00  --bmc1_ucm_max_lemma_size               10
% 3.49/1.00  
% 3.49/1.00  ------ AIG Options
% 3.49/1.00  
% 3.49/1.00  --aig_mode                              false
% 3.49/1.00  
% 3.49/1.00  ------ Instantiation Options
% 3.49/1.00  
% 3.49/1.00  --instantiation_flag                    true
% 3.49/1.00  --inst_sos_flag                         false
% 3.49/1.00  --inst_sos_phase                        true
% 3.49/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.00  --inst_lit_sel_side                     none
% 3.49/1.00  --inst_solver_per_active                1400
% 3.49/1.00  --inst_solver_calls_frac                1.
% 3.49/1.00  --inst_passive_queue_type               priority_queues
% 3.49/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.00  --inst_passive_queues_freq              [25;2]
% 3.49/1.00  --inst_dismatching                      true
% 3.49/1.00  --inst_eager_unprocessed_to_passive     true
% 3.49/1.00  --inst_prop_sim_given                   true
% 3.49/1.00  --inst_prop_sim_new                     false
% 3.49/1.00  --inst_subs_new                         false
% 3.49/1.00  --inst_eq_res_simp                      false
% 3.49/1.00  --inst_subs_given                       false
% 3.49/1.00  --inst_orphan_elimination               true
% 3.49/1.00  --inst_learning_loop_flag               true
% 3.49/1.00  --inst_learning_start                   3000
% 3.49/1.00  --inst_learning_factor                  2
% 3.49/1.00  --inst_start_prop_sim_after_learn       3
% 3.49/1.00  --inst_sel_renew                        solver
% 3.49/1.00  --inst_lit_activity_flag                true
% 3.49/1.00  --inst_restr_to_given                   false
% 3.49/1.00  --inst_activity_threshold               500
% 3.49/1.00  --inst_out_proof                        true
% 3.49/1.00  
% 3.49/1.00  ------ Resolution Options
% 3.49/1.00  
% 3.49/1.00  --resolution_flag                       false
% 3.49/1.00  --res_lit_sel                           adaptive
% 3.49/1.00  --res_lit_sel_side                      none
% 3.49/1.00  --res_ordering                          kbo
% 3.49/1.00  --res_to_prop_solver                    active
% 3.49/1.00  --res_prop_simpl_new                    false
% 3.49/1.00  --res_prop_simpl_given                  true
% 3.49/1.00  --res_passive_queue_type                priority_queues
% 3.49/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.00  --res_passive_queues_freq               [15;5]
% 3.49/1.00  --res_forward_subs                      full
% 3.49/1.00  --res_backward_subs                     full
% 3.49/1.00  --res_forward_subs_resolution           true
% 3.49/1.00  --res_backward_subs_resolution          true
% 3.49/1.00  --res_orphan_elimination                true
% 3.49/1.00  --res_time_limit                        2.
% 3.49/1.00  --res_out_proof                         true
% 3.49/1.00  
% 3.49/1.00  ------ Superposition Options
% 3.49/1.00  
% 3.49/1.00  --superposition_flag                    true
% 3.49/1.00  --sup_passive_queue_type                priority_queues
% 3.49/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.00  --demod_completeness_check              fast
% 3.49/1.00  --demod_use_ground                      true
% 3.49/1.00  --sup_to_prop_solver                    passive
% 3.49/1.00  --sup_prop_simpl_new                    true
% 3.49/1.00  --sup_prop_simpl_given                  true
% 3.49/1.00  --sup_fun_splitting                     false
% 3.49/1.00  --sup_smt_interval                      50000
% 3.49/1.00  
% 3.49/1.00  ------ Superposition Simplification Setup
% 3.49/1.00  
% 3.49/1.00  --sup_indices_passive                   []
% 3.49/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.00  --sup_full_bw                           [BwDemod]
% 3.49/1.00  --sup_immed_triv                        [TrivRules]
% 3.49/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.00  --sup_immed_bw_main                     []
% 3.49/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.00  
% 3.49/1.00  ------ Combination Options
% 3.49/1.00  
% 3.49/1.00  --comb_res_mult                         3
% 3.49/1.00  --comb_sup_mult                         2
% 3.49/1.00  --comb_inst_mult                        10
% 3.49/1.00  
% 3.49/1.00  ------ Debug Options
% 3.49/1.00  
% 3.49/1.00  --dbg_backtrace                         false
% 3.49/1.00  --dbg_dump_prop_clauses                 false
% 3.49/1.00  --dbg_dump_prop_clauses_file            -
% 3.49/1.00  --dbg_out_stat                          false
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  ------ Proving...
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  % SZS status Theorem for theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  fof(f9,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f23,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.49/1.00    inference(ennf_transformation,[],[f9])).
% 3.49/1.00  
% 3.49/1.00  fof(f44,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.49/1.00    inference(nnf_transformation,[],[f23])).
% 3.49/1.00  
% 3.49/1.00  fof(f45,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.49/1.00    inference(rectify,[],[f44])).
% 3.49/1.00  
% 3.49/1.00  fof(f46,plain,(
% 3.49/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 3.49/1.00    introduced(choice_axiom,[])).
% 3.49/1.00  
% 3.49/1.00  fof(f47,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.49/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).
% 3.49/1.00  
% 3.49/1.00  fof(f75,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f47])).
% 3.49/1.00  
% 3.49/1.00  fof(f15,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f30,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(ennf_transformation,[],[f15])).
% 3.49/1.00  
% 3.49/1.00  fof(f31,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(flattening,[],[f30])).
% 3.49/1.00  
% 3.49/1.00  fof(f50,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(nnf_transformation,[],[f31])).
% 3.49/1.00  
% 3.49/1.00  fof(f84,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f50])).
% 3.49/1.00  
% 3.49/1.00  fof(f16,conjecture,(
% 3.49/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f17,negated_conjecture,(
% 3.49/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.49/1.00    inference(negated_conjecture,[],[f16])).
% 3.49/1.00  
% 3.49/1.00  fof(f32,plain,(
% 3.49/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.49/1.00    inference(ennf_transformation,[],[f17])).
% 3.49/1.00  
% 3.49/1.00  fof(f33,plain,(
% 3.49/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.49/1.00    inference(flattening,[],[f32])).
% 3.49/1.00  
% 3.49/1.00  fof(f52,plain,(
% 3.49/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.49/1.00    introduced(choice_axiom,[])).
% 3.49/1.00  
% 3.49/1.00  fof(f51,plain,(
% 3.49/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.49/1.00    introduced(choice_axiom,[])).
% 3.49/1.00  
% 3.49/1.00  fof(f53,plain,(
% 3.49/1.00    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.49/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f33,f52,f51])).
% 3.49/1.00  
% 3.49/1.00  fof(f91,plain,(
% 3.49/1.00    v1_funct_2(sK6,sK3,sK4)),
% 3.49/1.00    inference(cnf_transformation,[],[f53])).
% 3.49/1.00  
% 3.49/1.00  fof(f92,plain,(
% 3.49/1.00    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.49/1.00    inference(cnf_transformation,[],[f53])).
% 3.49/1.00  
% 3.49/1.00  fof(f13,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f28,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(ennf_transformation,[],[f13])).
% 3.49/1.00  
% 3.49/1.00  fof(f82,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f28])).
% 3.49/1.00  
% 3.49/1.00  fof(f73,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f47])).
% 3.49/1.00  
% 3.49/1.00  fof(f11,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f26,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(ennf_transformation,[],[f11])).
% 3.49/1.00  
% 3.49/1.00  fof(f80,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f26])).
% 3.49/1.00  
% 3.49/1.00  fof(f7,axiom,(
% 3.49/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f20,plain,(
% 3.49/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.49/1.00    inference(ennf_transformation,[],[f7])).
% 3.49/1.00  
% 3.49/1.00  fof(f71,plain,(
% 3.49/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f20])).
% 3.49/1.00  
% 3.49/1.00  fof(f14,axiom,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f29,plain,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(ennf_transformation,[],[f14])).
% 3.49/1.00  
% 3.49/1.00  fof(f83,plain,(
% 3.49/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f29])).
% 3.49/1.00  
% 3.49/1.00  fof(f93,plain,(
% 3.49/1.00    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 3.49/1.00    inference(cnf_transformation,[],[f53])).
% 3.49/1.00  
% 3.49/1.00  fof(f74,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f47])).
% 3.49/1.00  
% 3.49/1.00  fof(f10,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f24,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.49/1.00    inference(ennf_transformation,[],[f10])).
% 3.49/1.00  
% 3.49/1.00  fof(f25,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.49/1.00    inference(flattening,[],[f24])).
% 3.49/1.00  
% 3.49/1.00  fof(f48,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.49/1.00    inference(nnf_transformation,[],[f25])).
% 3.49/1.00  
% 3.49/1.00  fof(f49,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.49/1.00    inference(flattening,[],[f48])).
% 3.49/1.00  
% 3.49/1.00  fof(f78,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f49])).
% 3.49/1.00  
% 3.49/1.00  fof(f90,plain,(
% 3.49/1.00    v1_funct_1(sK6)),
% 3.49/1.00    inference(cnf_transformation,[],[f53])).
% 3.49/1.00  
% 3.49/1.00  fof(f94,plain,(
% 3.49/1.00    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f53])).
% 3.49/1.00  
% 3.49/1.00  fof(f12,axiom,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f27,plain,(
% 3.49/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.49/1.00    inference(ennf_transformation,[],[f12])).
% 3.49/1.00  
% 3.49/1.00  fof(f81,plain,(
% 3.49/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f27])).
% 3.49/1.00  
% 3.49/1.00  fof(f6,axiom,(
% 3.49/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f70,plain,(
% 3.49/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f6])).
% 3.49/1.00  
% 3.49/1.00  fof(f8,axiom,(
% 3.49/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f21,plain,(
% 3.49/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.49/1.00    inference(ennf_transformation,[],[f8])).
% 3.49/1.00  
% 3.49/1.00  fof(f22,plain,(
% 3.49/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.49/1.00    inference(flattening,[],[f21])).
% 3.49/1.00  
% 3.49/1.00  fof(f72,plain,(
% 3.49/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f22])).
% 3.49/1.00  
% 3.49/1.00  fof(f5,axiom,(
% 3.49/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f40,plain,(
% 3.49/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.49/1.00    inference(nnf_transformation,[],[f5])).
% 3.49/1.00  
% 3.49/1.00  fof(f41,plain,(
% 3.49/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.49/1.00    inference(rectify,[],[f40])).
% 3.49/1.00  
% 3.49/1.00  fof(f42,plain,(
% 3.49/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.49/1.00    introduced(choice_axiom,[])).
% 3.49/1.00  
% 3.49/1.00  fof(f43,plain,(
% 3.49/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.49/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.49/1.00  
% 3.49/1.00  fof(f66,plain,(
% 3.49/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.49/1.00    inference(cnf_transformation,[],[f43])).
% 3.49/1.00  
% 3.49/1.00  fof(f99,plain,(
% 3.49/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.49/1.00    inference(equality_resolution,[],[f66])).
% 3.49/1.00  
% 3.49/1.00  fof(f3,axiom,(
% 3.49/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f19,plain,(
% 3.49/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.49/1.00    inference(ennf_transformation,[],[f3])).
% 3.49/1.00  
% 3.49/1.00  fof(f64,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f19])).
% 3.49/1.00  
% 3.49/1.00  fof(f1,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f34,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.49/1.00    inference(nnf_transformation,[],[f1])).
% 3.49/1.00  
% 3.49/1.00  fof(f35,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.49/1.00    inference(flattening,[],[f34])).
% 3.49/1.00  
% 3.49/1.00  fof(f36,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.49/1.00    inference(rectify,[],[f35])).
% 3.49/1.00  
% 3.49/1.00  fof(f37,plain,(
% 3.49/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.49/1.00    introduced(choice_axiom,[])).
% 3.49/1.00  
% 3.49/1.00  fof(f38,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.49/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.49/1.00  
% 3.49/1.00  fof(f55,plain,(
% 3.49/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.49/1.00    inference(cnf_transformation,[],[f38])).
% 3.49/1.00  
% 3.49/1.00  fof(f96,plain,(
% 3.49/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.49/1.00    inference(equality_resolution,[],[f55])).
% 3.49/1.00  
% 3.49/1.00  fof(f4,axiom,(
% 3.49/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f65,plain,(
% 3.49/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.49/1.00    inference(cnf_transformation,[],[f4])).
% 3.49/1.00  
% 3.49/1.00  fof(f2,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f18,plain,(
% 3.49/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.49/1.00    inference(ennf_transformation,[],[f2])).
% 3.49/1.00  
% 3.49/1.00  fof(f39,plain,(
% 3.49/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.49/1.00    inference(nnf_transformation,[],[f18])).
% 3.49/1.00  
% 3.49/1.00  fof(f61,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f39])).
% 3.49/1.00  
% 3.49/1.00  cnf(c_20,plain,
% 3.49/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.49/1.00      | r2_hidden(sK2(X0,X2,X1),X2)
% 3.49/1.00      | ~ v1_relat_1(X1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2167,plain,
% 3.49/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.49/1.00      | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_35,plain,
% 3.49/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.49/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.49/1.00      | k1_xboole_0 = X2 ),
% 3.49/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_39,negated_conjecture,
% 3.49/1.00      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.49/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_856,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.49/1.00      | sK4 != X2
% 3.49/1.00      | sK3 != X1
% 3.49/1.00      | sK6 != X0
% 3.49/1.00      | k1_xboole_0 = X2 ),
% 3.49/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_39]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_857,plain,
% 3.49/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.49/1.00      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.49/1.00      | k1_xboole_0 = sK4 ),
% 3.49/1.00      inference(unflattening,[status(thm)],[c_856]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_38,negated_conjecture,
% 3.49/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.49/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_859,plain,
% 3.49/1.00      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_857,c_38]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2158,plain,
% 3.49/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_28,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2162,plain,
% 3.49/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.49/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4394,plain,
% 3.49/1.00      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_2158,c_2162]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4509,plain,
% 3.49/1.00      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_859,c_4394]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_22,plain,
% 3.49/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.49/1.00      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
% 3.49/1.00      | ~ v1_relat_1(X1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2165,plain,
% 3.49/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.49/1.00      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7352,plain,
% 3.49/1.00      ( sK4 = k1_xboole_0
% 3.49/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.49/1.00      | r2_hidden(sK2(X0,X1,sK6),sK3) = iProver_top
% 3.49/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_4509,c_2165]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_43,plain,
% 3.49/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_26,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | v1_relat_1(X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2444,plain,
% 3.49/1.00      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.49/1.00      | v1_relat_1(sK6) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2445,plain,
% 3.49/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.49/1.00      | v1_relat_1(sK6) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_2444]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7689,plain,
% 3.49/1.00      ( r2_hidden(sK2(X0,X1,sK6),sK3) = iProver_top
% 3.49/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.49/1.00      | sK4 = k1_xboole_0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_7352,c_43,c_2445]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7690,plain,
% 3.49/1.00      ( sK4 = k1_xboole_0
% 3.49/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.49/1.00      | r2_hidden(sK2(X0,X1,sK6),sK3) = iProver_top ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_7689]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_17,plain,
% 3.49/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2169,plain,
% 3.49/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.49/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7698,plain,
% 3.49/1.00      ( sK4 = k1_xboole_0
% 3.49/1.00      | m1_subset_1(sK2(X0,X1,sK6),sK3) = iProver_top
% 3.49/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_7690,c_2169]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_29,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.49/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2161,plain,
% 3.49/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.49/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3826,plain,
% 3.49/1.00      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_2158,c_2161]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_37,negated_conjecture,
% 3.49/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2159,plain,
% 3.49/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4513,plain,
% 3.49/1.00      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_3826,c_2159]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_21,plain,
% 3.49/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.49/1.00      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 3.49/1.00      | ~ v1_relat_1(X1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2166,plain,
% 3.49/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.49/1.00      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
% 3.49/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_24,plain,
% 3.49/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.49/1.00      | ~ v1_funct_1(X2)
% 3.49/1.00      | ~ v1_relat_1(X2)
% 3.49/1.00      | k1_funct_1(X2,X0) = X1 ),
% 3.49/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_40,negated_conjecture,
% 3.49/1.00      ( v1_funct_1(sK6) ),
% 3.49/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_551,plain,
% 3.49/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.49/1.00      | ~ v1_relat_1(X2)
% 3.49/1.00      | k1_funct_1(X2,X0) = X1
% 3.49/1.00      | sK6 != X2 ),
% 3.49/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_40]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_552,plain,
% 3.49/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 3.49/1.00      | ~ v1_relat_1(sK6)
% 3.49/1.00      | k1_funct_1(sK6,X0) = X1 ),
% 3.49/1.00      inference(unflattening,[status(thm)],[c_551]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2157,plain,
% 3.49/1.00      ( k1_funct_1(sK6,X0) = X1
% 3.49/1.00      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.49/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_553,plain,
% 3.49/1.00      ( k1_funct_1(sK6,X0) = X1
% 3.49/1.00      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.49/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2484,plain,
% 3.49/1.00      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.49/1.00      | k1_funct_1(sK6,X0) = X1 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_2157,c_43,c_553,c_2445]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2485,plain,
% 3.49/1.00      ( k1_funct_1(sK6,X0) = X1
% 3.49/1.00      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_2484]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_9116,plain,
% 3.49/1.00      ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
% 3.49/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.49/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_2166,c_2485]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10490,plain,
% 3.49/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.49/1.00      | k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_9116,c_43,c_2445]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10491,plain,
% 3.49/1.00      ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
% 3.49/1.00      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_10490]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10504,plain,
% 3.49/1.00      ( k1_funct_1(sK6,sK2(sK7,sK5,sK6)) = sK7 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_4513,c_10491]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_36,negated_conjecture,
% 3.49/1.00      ( ~ m1_subset_1(X0,sK3)
% 3.49/1.00      | ~ r2_hidden(X0,sK5)
% 3.49/1.00      | k1_funct_1(sK6,X0) != sK7 ),
% 3.49/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2160,plain,
% 3.49/1.00      ( k1_funct_1(sK6,X0) != sK7
% 3.49/1.00      | m1_subset_1(X0,sK3) != iProver_top
% 3.49/1.00      | r2_hidden(X0,sK5) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10570,plain,
% 3.49/1.00      ( m1_subset_1(sK2(sK7,sK5,sK6),sK3) != iProver_top
% 3.49/1.00      | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_10504,c_2160]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10807,plain,
% 3.49/1.00      ( sK4 = k1_xboole_0
% 3.49/1.00      | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top
% 3.49/1.00      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_7698,c_10570]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10952,plain,
% 3.49/1.00      ( r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top
% 3.49/1.00      | sK4 = k1_xboole_0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_10807,c_4513]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10953,plain,
% 3.49/1.00      ( sK4 = k1_xboole_0
% 3.49/1.00      | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top ),
% 3.49/1.00      inference(renaming,[status(thm)],[c_10952]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10958,plain,
% 3.49/1.00      ( sK4 = k1_xboole_0
% 3.49/1.00      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 3.49/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_2167,c_10953]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10961,plain,
% 3.49/1.00      ( sK4 = k1_xboole_0 ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_10958,c_43,c_2445,c_4513]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_27,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.49/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2163,plain,
% 3.49/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.49/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_5243,plain,
% 3.49/1.00      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top
% 3.49/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_3826,c_2163]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6422,plain,
% 3.49/1.00      ( m1_subset_1(k9_relat_1(sK6,X0),k1_zfmisc_1(sK4)) = iProver_top ),
% 3.49/1.00      inference(global_propositional_subsumption,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_5243,c_43]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_16,plain,
% 3.49/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_18,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_536,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 3.49/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_537,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/1.00      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.49/1.00      inference(unflattening,[status(thm)],[c_536]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_15,plain,
% 3.49/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_988,plain,
% 3.49/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.49/1.00      inference(prop_impl,[status(thm)],[c_15]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1058,plain,
% 3.49/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.49/1.00      inference(bin_hyper_res,[status(thm)],[c_537,c_988]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2152,plain,
% 3.49/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.49/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6429,plain,
% 3.49/1.00      ( r1_tarski(k9_relat_1(sK6,X0),sK4) = iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_6422,c_2152]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10,plain,
% 3.49/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.49/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2174,plain,
% 3.49/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6435,plain,
% 3.49/1.00      ( k2_xboole_0(k9_relat_1(sK6,X0),sK4) = sK4 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_6429,c_2174]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4,plain,
% 3.49/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2180,plain,
% 3.49/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.49/1.00      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6700,plain,
% 3.49/1.00      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.49/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_6435,c_2180]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6712,plain,
% 3.49/1.00      ( r2_hidden(sK7,sK4) = iProver_top ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_4513,c_6700]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_10970,plain,
% 3.49/1.00      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_10961,c_6712]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1401,plain,
% 3.49/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.49/1.00      theory(equality) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2504,plain,
% 3.49/1.00      ( r2_hidden(X0,X1)
% 3.49/1.00      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 3.49/1.00      | X1 != k7_relset_1(sK3,sK4,sK6,sK5)
% 3.49/1.00      | X0 != sK7 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_1401]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2858,plain,
% 3.49/1.00      ( r2_hidden(sK7,X0)
% 3.49/1.00      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 3.49/1.00      | X0 != k7_relset_1(sK3,sK4,sK6,sK5)
% 3.49/1.00      | sK7 != sK7 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_2504]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6379,plain,
% 3.49/1.00      ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 3.49/1.00      | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0))
% 3.49/1.00      | k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0) != k7_relset_1(sK3,sK4,sK6,sK5)
% 3.49/1.00      | sK7 != sK7 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_2858]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6381,plain,
% 3.49/1.00      ( k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0) != k7_relset_1(sK3,sK4,sK6,sK5)
% 3.49/1.00      | sK7 != sK7
% 3.49/1.00      | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
% 3.49/1.00      | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0)) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_6379]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_11,plain,
% 3.49/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.49/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3600,plain,
% 3.49/1.00      ( k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0) = k7_relset_1(sK3,sK4,sK6,sK5) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1399,plain,( X0 = X0 ),theory(equality) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2859,plain,
% 3.49/1.00      ( sK7 = sK7 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_1399]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8,plain,
% 3.49/1.00      ( ~ r2_hidden(X0,X1)
% 3.49/1.00      | ~ r2_hidden(X0,X2)
% 3.49/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2478,plain,
% 3.49/1.00      ( ~ r2_hidden(sK7,X0)
% 3.49/1.00      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 3.49/1.00      | ~ r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),X0)) ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2479,plain,
% 3.49/1.00      ( r2_hidden(sK7,X0) != iProver_top
% 3.49/1.00      | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
% 3.49/1.00      | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),X0)) != iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_2478]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2481,plain,
% 3.49/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
% 3.49/1.00      | r2_hidden(sK7,k5_xboole_0(k7_relset_1(sK3,sK4,sK6,sK5),k1_xboole_0)) != iProver_top
% 3.49/1.00      | r2_hidden(sK7,k1_xboole_0) != iProver_top ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_2479]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_44,plain,
% 3.49/1.00      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 3.49/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(contradiction,plain,
% 3.49/1.00      ( $false ),
% 3.49/1.00      inference(minisat,
% 3.49/1.00                [status(thm)],
% 3.49/1.00                [c_10970,c_6381,c_3600,c_2859,c_2481,c_44]) ).
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  ------                               Statistics
% 3.49/1.00  
% 3.49/1.00  ------ General
% 3.49/1.00  
% 3.49/1.00  abstr_ref_over_cycles:                  0
% 3.49/1.00  abstr_ref_under_cycles:                 0
% 3.49/1.00  gc_basic_clause_elim:                   0
% 3.49/1.00  forced_gc_time:                         0
% 3.49/1.00  parsing_time:                           0.013
% 3.49/1.00  unif_index_cands_time:                  0.
% 3.49/1.00  unif_index_add_time:                    0.
% 3.49/1.00  orderings_time:                         0.
% 3.49/1.00  out_proof_time:                         0.011
% 3.49/1.00  total_time:                             0.32
% 3.49/1.00  num_of_symbols:                         57
% 3.49/1.00  num_of_terms:                           11033
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing
% 3.49/1.00  
% 3.49/1.00  num_of_splits:                          0
% 3.49/1.00  num_of_split_atoms:                     0
% 3.49/1.00  num_of_reused_defs:                     0
% 3.49/1.00  num_eq_ax_congr_red:                    49
% 3.49/1.00  num_of_sem_filtered_clauses:            1
% 3.49/1.00  num_of_subtypes:                        0
% 3.49/1.00  monotx_restored_types:                  0
% 3.49/1.00  sat_num_of_epr_types:                   0
% 3.49/1.00  sat_num_of_non_cyclic_types:            0
% 3.49/1.00  sat_guarded_non_collapsed_types:        0
% 3.49/1.00  num_pure_diseq_elim:                    0
% 3.49/1.00  simp_replaced_by:                       0
% 3.49/1.00  res_preprocessed:                       175
% 3.49/1.00  prep_upred:                             0
% 3.49/1.00  prep_unflattend:                        59
% 3.49/1.00  smt_new_axioms:                         0
% 3.49/1.00  pred_elim_cands:                        4
% 3.49/1.00  pred_elim:                              3
% 3.49/1.00  pred_elim_cl:                           6
% 3.49/1.00  pred_elim_cycles:                       8
% 3.49/1.00  merged_defs:                            8
% 3.49/1.00  merged_defs_ncl:                        0
% 3.49/1.00  bin_hyper_res:                          9
% 3.49/1.00  prep_cycles:                            4
% 3.49/1.00  pred_elim_time:                         0.011
% 3.49/1.00  splitting_time:                         0.
% 3.49/1.00  sem_filter_time:                        0.
% 3.49/1.00  monotx_time:                            0.001
% 3.49/1.00  subtype_inf_time:                       0.
% 3.49/1.00  
% 3.49/1.00  ------ Problem properties
% 3.49/1.00  
% 3.49/1.00  clauses:                                35
% 3.49/1.00  conjectures:                            3
% 3.49/1.00  epr:                                    1
% 3.49/1.00  horn:                                   27
% 3.49/1.00  ground:                                 5
% 3.49/1.00  unary:                                  3
% 3.49/1.00  binary:                                 12
% 3.49/1.00  lits:                                   91
% 3.49/1.00  lits_eq:                                18
% 3.49/1.00  fd_pure:                                0
% 3.49/1.00  fd_pseudo:                              0
% 3.49/1.00  fd_cond:                                0
% 3.49/1.00  fd_pseudo_cond:                         6
% 3.49/1.00  ac_symbols:                             0
% 3.49/1.00  
% 3.49/1.00  ------ Propositional Solver
% 3.49/1.00  
% 3.49/1.00  prop_solver_calls:                      27
% 3.49/1.00  prop_fast_solver_calls:                 1202
% 3.49/1.00  smt_solver_calls:                       0
% 3.49/1.00  smt_fast_solver_calls:                  0
% 3.49/1.00  prop_num_of_clauses:                    4306
% 3.49/1.00  prop_preprocess_simplified:             11820
% 3.49/1.00  prop_fo_subsumed:                       11
% 3.49/1.00  prop_solver_time:                       0.
% 3.49/1.00  smt_solver_time:                        0.
% 3.49/1.00  smt_fast_solver_time:                   0.
% 3.49/1.00  prop_fast_solver_time:                  0.
% 3.49/1.00  prop_unsat_core_time:                   0.
% 3.49/1.00  
% 3.49/1.00  ------ QBF
% 3.49/1.00  
% 3.49/1.00  qbf_q_res:                              0
% 3.49/1.00  qbf_num_tautologies:                    0
% 3.49/1.00  qbf_prep_cycles:                        0
% 3.49/1.00  
% 3.49/1.00  ------ BMC1
% 3.49/1.00  
% 3.49/1.00  bmc1_current_bound:                     -1
% 3.49/1.00  bmc1_last_solved_bound:                 -1
% 3.49/1.00  bmc1_unsat_core_size:                   -1
% 3.49/1.00  bmc1_unsat_core_parents_size:           -1
% 3.49/1.00  bmc1_merge_next_fun:                    0
% 3.49/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.49/1.00  
% 3.49/1.00  ------ Instantiation
% 3.49/1.00  
% 3.49/1.00  inst_num_of_clauses:                    1061
% 3.49/1.00  inst_num_in_passive:                    533
% 3.49/1.00  inst_num_in_active:                     321
% 3.49/1.00  inst_num_in_unprocessed:                207
% 3.49/1.00  inst_num_of_loops:                      350
% 3.49/1.00  inst_num_of_learning_restarts:          0
% 3.49/1.00  inst_num_moves_active_passive:          28
% 3.49/1.00  inst_lit_activity:                      0
% 3.49/1.00  inst_lit_activity_moves:                0
% 3.49/1.00  inst_num_tautologies:                   0
% 3.49/1.00  inst_num_prop_implied:                  0
% 3.49/1.00  inst_num_existing_simplified:           0
% 3.49/1.00  inst_num_eq_res_simplified:             0
% 3.49/1.00  inst_num_child_elim:                    0
% 3.49/1.00  inst_num_of_dismatching_blockings:      498
% 3.49/1.00  inst_num_of_non_proper_insts:           889
% 3.49/1.00  inst_num_of_duplicates:                 0
% 3.49/1.00  inst_inst_num_from_inst_to_res:         0
% 3.49/1.00  inst_dismatching_checking_time:         0.
% 3.49/1.00  
% 3.49/1.00  ------ Resolution
% 3.49/1.00  
% 3.49/1.00  res_num_of_clauses:                     0
% 3.49/1.00  res_num_in_passive:                     0
% 3.49/1.00  res_num_in_active:                      0
% 3.49/1.00  res_num_of_loops:                       179
% 3.49/1.00  res_forward_subset_subsumed:            141
% 3.49/1.00  res_backward_subset_subsumed:           0
% 3.49/1.00  res_forward_subsumed:                   0
% 3.49/1.00  res_backward_subsumed:                  0
% 3.49/1.00  res_forward_subsumption_resolution:     0
% 3.49/1.00  res_backward_subsumption_resolution:    0
% 3.49/1.00  res_clause_to_clause_subsumption:       639
% 3.49/1.00  res_orphan_elimination:                 0
% 3.49/1.00  res_tautology_del:                      62
% 3.49/1.00  res_num_eq_res_simplified:              0
% 3.49/1.00  res_num_sel_changes:                    0
% 3.49/1.00  res_moves_from_active_to_pass:          0
% 3.49/1.00  
% 3.49/1.00  ------ Superposition
% 3.49/1.00  
% 3.49/1.00  sup_time_total:                         0.
% 3.49/1.00  sup_time_generating:                    0.
% 3.49/1.00  sup_time_sim_full:                      0.
% 3.49/1.00  sup_time_sim_immed:                     0.
% 3.49/1.00  
% 3.49/1.00  sup_num_of_clauses:                     129
% 3.49/1.00  sup_num_in_active:                      43
% 3.49/1.00  sup_num_in_passive:                     86
% 3.49/1.00  sup_num_of_loops:                       69
% 3.49/1.00  sup_fw_superposition:                   59
% 3.49/1.00  sup_bw_superposition:                   86
% 3.49/1.00  sup_immediate_simplified:               8
% 3.49/1.00  sup_given_eliminated:                   0
% 3.49/1.00  comparisons_done:                       0
% 3.49/1.00  comparisons_avoided:                    5
% 3.49/1.00  
% 3.49/1.00  ------ Simplifications
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  sim_fw_subset_subsumed:                 4
% 3.49/1.00  sim_bw_subset_subsumed:                 7
% 3.49/1.00  sim_fw_subsumed:                        2
% 3.49/1.00  sim_bw_subsumed:                        2
% 3.49/1.00  sim_fw_subsumption_res:                 1
% 3.49/1.00  sim_bw_subsumption_res:                 0
% 3.49/1.00  sim_tautology_del:                      21
% 3.49/1.00  sim_eq_tautology_del:                   2
% 3.49/1.00  sim_eq_res_simp:                        7
% 3.49/1.00  sim_fw_demodulated:                     0
% 3.49/1.00  sim_bw_demodulated:                     23
% 3.49/1.00  sim_light_normalised:                   0
% 3.49/1.00  sim_joinable_taut:                      0
% 3.49/1.00  sim_joinable_simp:                      0
% 3.49/1.00  sim_ac_normalised:                      0
% 3.49/1.00  sim_smt_subsumption:                    0
% 3.49/1.00  
%------------------------------------------------------------------------------
