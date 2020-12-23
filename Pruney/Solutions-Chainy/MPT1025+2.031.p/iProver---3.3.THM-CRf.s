%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:06 EST 2020

% Result     : Theorem 23.41s
% Output     : CNFRefutation 23.41s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 423 expanded)
%              Number of clauses        :   76 ( 137 expanded)
%              Number of leaves         :   19 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  476 (2053 expanded)
%              Number of equality atoms :  168 ( 447 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK11
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK11,k7_relset_1(X0,X1,X3,X2)) ) ) ),
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
              ( k1_funct_1(sK10,X5) != X4
              | ~ r2_hidden(X5,sK9)
              | ~ m1_subset_1(X5,sK7) )
          & r2_hidden(X4,k7_relset_1(sK7,sK8,sK10,sK9)) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      & v1_funct_2(sK10,sK7,sK8)
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ! [X5] :
        ( k1_funct_1(sK10,X5) != sK11
        | ~ r2_hidden(X5,sK9)
        | ~ m1_subset_1(X5,sK7) )
    & r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9))
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK10,sK7,sK8)
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f30,f52,f51])).

fof(f87,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_2(sK10,sK7,sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,(
    r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) ),
    inference(cnf_transformation,[],[f53])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f21])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X5] :
      ( k1_funct_1(sK10,X5) != sK11
      | ~ r2_hidden(X5,sK9)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK6(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f48])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1414,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1417,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2652,plain,
    ( k1_relset_1(sK7,sK8,sK10) = sK7
    | sK8 = k1_xboole_0
    | v1_funct_2(sK10,sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_1417])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK10,sK7,sK8) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2668,plain,
    ( ~ v1_funct_2(sK10,sK7,sK8)
    | k1_relset_1(sK7,sK8,sK10) = sK7
    | sK8 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2652])).

cnf(c_3415,plain,
    ( sK8 = k1_xboole_0
    | k1_relset_1(sK7,sK8,sK10) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2652,c_34,c_2668])).

cnf(c_3416,plain,
    ( k1_relset_1(sK7,sK8,sK10) = sK7
    | sK8 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3415])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1427,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2761,plain,
    ( k1_relset_1(sK7,sK8,sK10) = k1_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_1414,c_1427])).

cnf(c_3417,plain,
    ( k1_relat_1(sK10) = sK7
    | sK8 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3416,c_2761])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1431,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5033,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK10),sK7) = iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_1431])).

cnf(c_38,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1748,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1749,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1748])).

cnf(c_5377,plain,
    ( r2_hidden(sK4(X0,X1,sK10),sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5033,c_38,c_1749])).

cnf(c_5378,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | r2_hidden(sK4(X0,X1,sK10),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_5377])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1441,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5388,plain,
    ( sK8 = k1_xboole_0
    | m1_subset_1(sK4(X0,X1,sK10),sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5378,c_1441])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1426,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2957,plain,
    ( k7_relset_1(sK7,sK8,sK10,X0) = k9_relat_1(sK10,X0) ),
    inference(superposition,[status(thm)],[c_1414,c_1426])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1415,plain,
    ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3218,plain,
    ( r2_hidden(sK11,k9_relat_1(sK10,sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2957,c_1415])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1432,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1429,plain,
    ( k1_funct_1(X0,X1) = X2
    | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6389,plain,
    ( k1_funct_1(X0,sK4(X1,X2,X0)) = X1
    | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_1429])).

cnf(c_83556,plain,
    ( k1_funct_1(sK10,sK4(sK11,sK9,sK10)) = sK11
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_6389])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3234,plain,
    ( r2_hidden(sK11,k9_relat_1(sK10,sK9)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3218])).

cnf(c_14078,plain,
    ( r2_hidden(k4_tarski(sK4(sK11,sK9,sK10),sK11),sK10)
    | ~ r2_hidden(sK11,k9_relat_1(sK10,sK9))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_38147,plain,
    ( ~ r2_hidden(k4_tarski(sK4(sK11,sK9,sK10),sK11),sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | k1_funct_1(sK10,sK4(sK11,sK9,sK10)) = sK11 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_85190,plain,
    ( k1_funct_1(sK10,sK4(sK11,sK9,sK10)) = sK11 ),
    inference(global_propositional_subsumption,[status(thm)],[c_83556,c_35,c_33,c_1748,c_3234,c_14078,c_38147])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ r2_hidden(X0,sK9)
    | k1_funct_1(sK10,X0) != sK11 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1416,plain,
    ( k1_funct_1(sK10,X0) != sK11
    | m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_85197,plain,
    ( m1_subset_1(sK4(sK11,sK9,sK10),sK7) != iProver_top
    | r2_hidden(sK4(sK11,sK9,sK10),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_85190,c_1416])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14080,plain,
    ( r2_hidden(sK4(sK11,sK9,sK10),sK9)
    | ~ r2_hidden(sK11,k9_relat_1(sK10,sK9))
    | ~ v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14081,plain,
    ( r2_hidden(sK4(sK11,sK9,sK10),sK9) = iProver_top
    | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14080])).

cnf(c_85937,plain,
    ( m1_subset_1(sK4(sK11,sK9,sK10),sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_85197,c_38,c_1749,c_3218,c_14081])).

cnf(c_85942,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5388,c_85937])).

cnf(c_652,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_18568,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_18570,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18568])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1444,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1445,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2422,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1444,c_1445])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK6(X3,X1,X2),X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1425,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK6(X3,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6273,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK6(X0,sK7,sK8),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1414,c_1425])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_252,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_253,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_252])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_253])).

cnf(c_1411,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_6658,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r1_tarski(sK8,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6273,c_1411])).

cnf(c_7146,plain,
    ( r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | r1_tarski(sK8,X2) != iProver_top
    | v1_relat_1(sK10) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_6658])).

cnf(c_16451,plain,
    ( r1_tarski(sK8,X2) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7146,c_38,c_1749])).

cnf(c_16452,plain,
    ( r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | r1_tarski(sK8,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_16451])).

cnf(c_16467,plain,
    ( r1_tarski(sK8,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3218,c_16452])).

cnf(c_16521,plain,
    ( v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_16467])).

cnf(c_16524,plain,
    ( ~ v1_xboole_0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16521])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_85942,c_18570,c_16524,c_3218,c_3])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 18:45:26 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 23.41/3.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.41/3.48  
% 23.41/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.41/3.48  
% 23.41/3.48  ------  iProver source info
% 23.41/3.48  
% 23.41/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.41/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.41/3.48  git: non_committed_changes: false
% 23.41/3.48  git: last_make_outside_of_git: false
% 23.41/3.48  
% 23.41/3.48  ------ 
% 23.41/3.48  ------ Parsing...
% 23.41/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.41/3.48  
% 23.41/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.41/3.48  
% 23.41/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.41/3.48  
% 23.41/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.41/3.48  ------ Proving...
% 23.41/3.48  ------ Problem Properties 
% 23.41/3.48  
% 23.41/3.48  
% 23.41/3.48  clauses                                 35
% 23.41/3.48  conjectures                             5
% 23.41/3.48  EPR                                     6
% 23.41/3.48  Horn                                    29
% 23.41/3.48  unary                                   5
% 23.41/3.48  binary                                  10
% 23.41/3.48  lits                                    92
% 23.41/3.48  lits eq                                 16
% 23.41/3.48  fd_pure                                 0
% 23.41/3.48  fd_pseudo                               0
% 23.41/3.48  fd_cond                                 3
% 23.41/3.48  fd_pseudo_cond                          3
% 23.41/3.48  AC symbols                              0
% 23.41/3.48  
% 23.41/3.48  ------ Input Options Time Limit: Unbounded
% 23.41/3.48  
% 23.41/3.48  
% 23.41/3.48  ------ 
% 23.41/3.48  Current options:
% 23.41/3.48  ------ 
% 23.41/3.48  
% 23.41/3.48  
% 23.41/3.48  
% 23.41/3.48  
% 23.41/3.48  ------ Proving...
% 23.41/3.48  
% 23.41/3.48  
% 23.41/3.48  % SZS status Theorem for theBenchmark.p
% 23.41/3.48  
% 23.41/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.41/3.48  
% 23.41/3.48  fof(f14,conjecture,(
% 23.41/3.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.48  
% 23.41/3.48  fof(f15,negated_conjecture,(
% 23.41/3.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 23.41/3.48    inference(negated_conjecture,[],[f14])).
% 23.41/3.48  
% 23.41/3.48  fof(f29,plain,(
% 23.41/3.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 23.41/3.48    inference(ennf_transformation,[],[f15])).
% 23.41/3.48  
% 23.41/3.48  fof(f30,plain,(
% 23.41/3.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 23.41/3.48    inference(flattening,[],[f29])).
% 23.41/3.48  
% 23.41/3.48  fof(f52,plain,(
% 23.41/3.48    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK11 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK11,k7_relset_1(X0,X1,X3,X2)))) )),
% 23.41/3.48    introduced(choice_axiom,[])).
% 23.41/3.48  
% 23.41/3.48  fof(f51,plain,(
% 23.41/3.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK9) | ~m1_subset_1(X5,sK7)) & r2_hidden(X4,k7_relset_1(sK7,sK8,sK10,sK9))) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK10,sK7,sK8) & v1_funct_1(sK10))),
% 23.41/3.48    introduced(choice_axiom,[])).
% 23.41/3.48  
% 23.41/3.48  fof(f53,plain,(
% 23.41/3.48    (! [X5] : (k1_funct_1(sK10,X5) != sK11 | ~r2_hidden(X5,sK9) | ~m1_subset_1(X5,sK7)) & r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9))) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK10,sK7,sK8) & v1_funct_1(sK10)),
% 23.41/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f30,f52,f51])).
% 23.41/3.48  
% 23.41/3.48  fof(f87,plain,(
% 23.41/3.48    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 23.41/3.48    inference(cnf_transformation,[],[f53])).
% 23.41/3.48  
% 23.41/3.48  fof(f13,axiom,(
% 23.41/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.48  
% 23.41/3.48  fof(f27,plain,(
% 23.41/3.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.41/3.48    inference(ennf_transformation,[],[f13])).
% 23.41/3.48  
% 23.41/3.48  fof(f28,plain,(
% 23.41/3.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.41/3.48    inference(flattening,[],[f27])).
% 23.41/3.48  
% 23.41/3.48  fof(f50,plain,(
% 23.41/3.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.41/3.48    inference(nnf_transformation,[],[f28])).
% 23.41/3.48  
% 23.41/3.48  fof(f79,plain,(
% 23.41/3.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.41/3.48    inference(cnf_transformation,[],[f50])).
% 23.41/3.48  
% 23.41/3.48  fof(f86,plain,(
% 23.41/3.48    v1_funct_2(sK10,sK7,sK8)),
% 23.41/3.48    inference(cnf_transformation,[],[f53])).
% 23.41/3.48  
% 23.41/3.48  fof(f10,axiom,(
% 23.41/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.48  
% 23.41/3.48  fof(f23,plain,(
% 23.41/3.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.41/3.48    inference(ennf_transformation,[],[f10])).
% 23.41/3.48  
% 23.41/3.48  fof(f74,plain,(
% 23.41/3.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.41/3.48    inference(cnf_transformation,[],[f23])).
% 23.41/3.48  
% 23.41/3.48  fof(f7,axiom,(
% 23.41/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.48  
% 23.41/3.48  fof(f19,plain,(
% 23.41/3.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 23.41/3.48    inference(ennf_transformation,[],[f7])).
% 23.41/3.48  
% 23.41/3.48  fof(f42,plain,(
% 23.41/3.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 23.41/3.48    inference(nnf_transformation,[],[f19])).
% 23.41/3.48  
% 23.41/3.48  fof(f43,plain,(
% 23.41/3.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 23.41/3.48    inference(rectify,[],[f42])).
% 23.41/3.48  
% 23.41/3.48  fof(f44,plain,(
% 23.41/3.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 23.41/3.48    introduced(choice_axiom,[])).
% 23.41/3.48  
% 23.41/3.48  fof(f45,plain,(
% 23.41/3.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 23.41/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 23.41/3.48  
% 23.41/3.48  fof(f66,plain,(
% 23.41/3.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 23.41/3.48    inference(cnf_transformation,[],[f45])).
% 23.41/3.48  
% 23.41/3.48  fof(f9,axiom,(
% 23.41/3.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.48  
% 23.41/3.48  fof(f22,plain,(
% 23.41/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.41/3.48    inference(ennf_transformation,[],[f9])).
% 23.41/3.48  
% 23.41/3.48  fof(f73,plain,(
% 23.41/3.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.41/3.48    inference(cnf_transformation,[],[f22])).
% 23.41/3.48  
% 23.41/3.48  fof(f3,axiom,(
% 23.41/3.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.48  
% 23.41/3.48  fof(f17,plain,(
% 23.41/3.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 23.41/3.48    inference(ennf_transformation,[],[f3])).
% 23.41/3.48  
% 23.41/3.48  fof(f58,plain,(
% 23.41/3.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 23.41/3.48    inference(cnf_transformation,[],[f17])).
% 23.41/3.48  
% 23.41/3.48  fof(f11,axiom,(
% 23.41/3.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.48  
% 23.41/3.48  fof(f24,plain,(
% 23.41/3.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.41/3.48    inference(ennf_transformation,[],[f11])).
% 23.41/3.48  
% 23.41/3.48  fof(f75,plain,(
% 23.41/3.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.41/3.48    inference(cnf_transformation,[],[f24])).
% 23.41/3.48  
% 23.41/3.48  fof(f88,plain,(
% 23.41/3.48    r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9))),
% 23.41/3.48    inference(cnf_transformation,[],[f53])).
% 23.41/3.48  
% 23.41/3.48  fof(f67,plain,(
% 23.41/3.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 23.41/3.48    inference(cnf_transformation,[],[f45])).
% 23.41/3.48  
% 23.41/3.48  fof(f8,axiom,(
% 23.41/3.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 23.41/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.49  
% 23.41/3.49  fof(f20,plain,(
% 23.41/3.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 23.41/3.49    inference(ennf_transformation,[],[f8])).
% 23.41/3.49  
% 23.41/3.49  fof(f21,plain,(
% 23.41/3.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 23.41/3.49    inference(flattening,[],[f20])).
% 23.41/3.49  
% 23.41/3.49  fof(f46,plain,(
% 23.41/3.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 23.41/3.49    inference(nnf_transformation,[],[f21])).
% 23.41/3.49  
% 23.41/3.49  fof(f47,plain,(
% 23.41/3.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 23.41/3.49    inference(flattening,[],[f46])).
% 23.41/3.49  
% 23.41/3.49  fof(f71,plain,(
% 23.41/3.49    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 23.41/3.49    inference(cnf_transformation,[],[f47])).
% 23.41/3.49  
% 23.41/3.49  fof(f85,plain,(
% 23.41/3.49    v1_funct_1(sK10)),
% 23.41/3.49    inference(cnf_transformation,[],[f53])).
% 23.41/3.49  
% 23.41/3.49  fof(f89,plain,(
% 23.41/3.49    ( ! [X5] : (k1_funct_1(sK10,X5) != sK11 | ~r2_hidden(X5,sK9) | ~m1_subset_1(X5,sK7)) )),
% 23.41/3.49    inference(cnf_transformation,[],[f53])).
% 23.41/3.49  
% 23.41/3.49  fof(f68,plain,(
% 23.41/3.49    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 23.41/3.49    inference(cnf_transformation,[],[f45])).
% 23.41/3.49  
% 23.41/3.49  fof(f1,axiom,(
% 23.41/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.41/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.49  
% 23.41/3.49  fof(f16,plain,(
% 23.41/3.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.41/3.49    inference(ennf_transformation,[],[f1])).
% 23.41/3.49  
% 23.41/3.49  fof(f31,plain,(
% 23.41/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.41/3.49    inference(nnf_transformation,[],[f16])).
% 23.41/3.49  
% 23.41/3.49  fof(f32,plain,(
% 23.41/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.41/3.49    inference(rectify,[],[f31])).
% 23.41/3.49  
% 23.41/3.49  fof(f33,plain,(
% 23.41/3.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.41/3.49    introduced(choice_axiom,[])).
% 23.41/3.49  
% 23.41/3.49  fof(f34,plain,(
% 23.41/3.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.41/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 23.41/3.49  
% 23.41/3.49  fof(f55,plain,(
% 23.41/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.41/3.49    inference(cnf_transformation,[],[f34])).
% 23.41/3.49  
% 23.41/3.49  fof(f56,plain,(
% 23.41/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.41/3.49    inference(cnf_transformation,[],[f34])).
% 23.41/3.49  
% 23.41/3.49  fof(f12,axiom,(
% 23.41/3.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 23.41/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.49  
% 23.41/3.49  fof(f25,plain,(
% 23.41/3.49    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.41/3.49    inference(ennf_transformation,[],[f12])).
% 23.41/3.49  
% 23.41/3.49  fof(f26,plain,(
% 23.41/3.49    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.41/3.49    inference(flattening,[],[f25])).
% 23.41/3.49  
% 23.41/3.49  fof(f48,plain,(
% 23.41/3.49    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0))),
% 23.41/3.49    introduced(choice_axiom,[])).
% 23.41/3.49  
% 23.41/3.49  fof(f49,plain,(
% 23.41/3.49    ! [X0,X1,X2,X3] : ((r2_hidden(sK6(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 23.41/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f48])).
% 23.41/3.49  
% 23.41/3.49  fof(f78,plain,(
% 23.41/3.49    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 23.41/3.49    inference(cnf_transformation,[],[f49])).
% 23.41/3.49  
% 23.41/3.49  fof(f5,axiom,(
% 23.41/3.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 23.41/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.49  
% 23.41/3.49  fof(f18,plain,(
% 23.41/3.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 23.41/3.49    inference(ennf_transformation,[],[f5])).
% 23.41/3.49  
% 23.41/3.49  fof(f61,plain,(
% 23.41/3.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 23.41/3.49    inference(cnf_transformation,[],[f18])).
% 23.41/3.49  
% 23.41/3.49  fof(f4,axiom,(
% 23.41/3.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.41/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.49  
% 23.41/3.49  fof(f35,plain,(
% 23.41/3.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.41/3.49    inference(nnf_transformation,[],[f4])).
% 23.41/3.49  
% 23.41/3.49  fof(f60,plain,(
% 23.41/3.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.41/3.49    inference(cnf_transformation,[],[f35])).
% 23.41/3.49  
% 23.41/3.49  fof(f2,axiom,(
% 23.41/3.49    v1_xboole_0(k1_xboole_0)),
% 23.41/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.41/3.49  
% 23.41/3.49  fof(f57,plain,(
% 23.41/3.49    v1_xboole_0(k1_xboole_0)),
% 23.41/3.49    inference(cnf_transformation,[],[f2])).
% 23.41/3.49  
% 23.41/3.49  cnf(c_33,negated_conjecture,
% 23.41/3.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 23.41/3.49      inference(cnf_transformation,[],[f87]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1414,plain,
% 23.41/3.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_30,plain,
% 23.41/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.41/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.41/3.49      | k1_relset_1(X1,X2,X0) = X1
% 23.41/3.49      | k1_xboole_0 = X2 ),
% 23.41/3.49      inference(cnf_transformation,[],[f79]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1417,plain,
% 23.41/3.49      ( k1_relset_1(X0,X1,X2) = X0
% 23.41/3.49      | k1_xboole_0 = X1
% 23.41/3.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 23.41/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_2652,plain,
% 23.41/3.49      ( k1_relset_1(sK7,sK8,sK10) = sK7
% 23.41/3.49      | sK8 = k1_xboole_0
% 23.41/3.49      | v1_funct_2(sK10,sK7,sK8) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_1414,c_1417]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_34,negated_conjecture,
% 23.41/3.49      ( v1_funct_2(sK10,sK7,sK8) ),
% 23.41/3.49      inference(cnf_transformation,[],[f86]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_2668,plain,
% 23.41/3.49      ( ~ v1_funct_2(sK10,sK7,sK8)
% 23.41/3.49      | k1_relset_1(sK7,sK8,sK10) = sK7
% 23.41/3.49      | sK8 = k1_xboole_0 ),
% 23.41/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_2652]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_3415,plain,
% 23.41/3.49      ( sK8 = k1_xboole_0 | k1_relset_1(sK7,sK8,sK10) = sK7 ),
% 23.41/3.49      inference(global_propositional_subsumption,
% 23.41/3.49                [status(thm)],
% 23.41/3.49                [c_2652,c_34,c_2668]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_3416,plain,
% 23.41/3.49      ( k1_relset_1(sK7,sK8,sK10) = sK7 | sK8 = k1_xboole_0 ),
% 23.41/3.49      inference(renaming,[status(thm)],[c_3415]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_20,plain,
% 23.41/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.41/3.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 23.41/3.49      inference(cnf_transformation,[],[f74]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1427,plain,
% 23.41/3.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 23.41/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_2761,plain,
% 23.41/3.49      ( k1_relset_1(sK7,sK8,sK10) = k1_relat_1(sK10) ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_1414,c_1427]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_3417,plain,
% 23.41/3.49      ( k1_relat_1(sK10) = sK7 | sK8 = k1_xboole_0 ),
% 23.41/3.49      inference(demodulation,[status(thm)],[c_3416,c_2761]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_15,plain,
% 23.41/3.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 23.41/3.49      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1))
% 23.41/3.49      | ~ v1_relat_1(X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f66]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1431,plain,
% 23.41/3.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 23.41/3.49      | r2_hidden(sK4(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 23.41/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_5033,plain,
% 23.41/3.49      ( sK8 = k1_xboole_0
% 23.41/3.49      | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 23.41/3.49      | r2_hidden(sK4(X0,X1,sK10),sK7) = iProver_top
% 23.41/3.49      | v1_relat_1(sK10) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_3417,c_1431]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_38,plain,
% 23.41/3.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_19,plain,
% 23.41/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.41/3.49      | v1_relat_1(X0) ),
% 23.41/3.49      inference(cnf_transformation,[],[f73]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1748,plain,
% 23.41/3.49      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 23.41/3.49      | v1_relat_1(sK10) ),
% 23.41/3.49      inference(instantiation,[status(thm)],[c_19]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1749,plain,
% 23.41/3.49      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 23.41/3.49      | v1_relat_1(sK10) = iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_1748]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_5377,plain,
% 23.41/3.49      ( r2_hidden(sK4(X0,X1,sK10),sK7) = iProver_top
% 23.41/3.49      | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 23.41/3.49      | sK8 = k1_xboole_0 ),
% 23.41/3.49      inference(global_propositional_subsumption,
% 23.41/3.49                [status(thm)],
% 23.41/3.49                [c_5033,c_38,c_1749]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_5378,plain,
% 23.41/3.49      ( sK8 = k1_xboole_0
% 23.41/3.49      | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 23.41/3.49      | r2_hidden(sK4(X0,X1,sK10),sK7) = iProver_top ),
% 23.41/3.49      inference(renaming,[status(thm)],[c_5377]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_4,plain,
% 23.41/3.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1441,plain,
% 23.41/3.49      ( m1_subset_1(X0,X1) = iProver_top
% 23.41/3.49      | r2_hidden(X0,X1) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_5388,plain,
% 23.41/3.49      ( sK8 = k1_xboole_0
% 23.41/3.49      | m1_subset_1(sK4(X0,X1,sK10),sK7) = iProver_top
% 23.41/3.49      | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_5378,c_1441]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_21,plain,
% 23.41/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.41/3.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 23.41/3.49      inference(cnf_transformation,[],[f75]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1426,plain,
% 23.41/3.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 23.41/3.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_2957,plain,
% 23.41/3.49      ( k7_relset_1(sK7,sK8,sK10,X0) = k9_relat_1(sK10,X0) ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_1414,c_1426]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_32,negated_conjecture,
% 23.41/3.49      ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) ),
% 23.41/3.49      inference(cnf_transformation,[],[f88]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1415,plain,
% 23.41/3.49      ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) = iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_3218,plain,
% 23.41/3.49      ( r2_hidden(sK11,k9_relat_1(sK10,sK9)) = iProver_top ),
% 23.41/3.49      inference(demodulation,[status(thm)],[c_2957,c_1415]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_14,plain,
% 23.41/3.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 23.41/3.49      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1)
% 23.41/3.49      | ~ v1_relat_1(X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1432,plain,
% 23.41/3.49      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 23.41/3.49      | r2_hidden(k4_tarski(sK4(X0,X2,X1),X0),X1) = iProver_top
% 23.41/3.49      | v1_relat_1(X1) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_17,plain,
% 23.41/3.49      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 23.41/3.49      | ~ v1_funct_1(X2)
% 23.41/3.49      | ~ v1_relat_1(X2)
% 23.41/3.49      | k1_funct_1(X2,X0) = X1 ),
% 23.41/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1429,plain,
% 23.41/3.49      ( k1_funct_1(X0,X1) = X2
% 23.41/3.49      | r2_hidden(k4_tarski(X1,X2),X0) != iProver_top
% 23.41/3.49      | v1_funct_1(X0) != iProver_top
% 23.41/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_6389,plain,
% 23.41/3.49      ( k1_funct_1(X0,sK4(X1,X2,X0)) = X1
% 23.41/3.49      | r2_hidden(X1,k9_relat_1(X0,X2)) != iProver_top
% 23.41/3.49      | v1_funct_1(X0) != iProver_top
% 23.41/3.49      | v1_relat_1(X0) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_1432,c_1429]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_83556,plain,
% 23.41/3.49      ( k1_funct_1(sK10,sK4(sK11,sK9,sK10)) = sK11
% 23.41/3.49      | v1_funct_1(sK10) != iProver_top
% 23.41/3.49      | v1_relat_1(sK10) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_3218,c_6389]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_35,negated_conjecture,
% 23.41/3.49      ( v1_funct_1(sK10) ),
% 23.41/3.49      inference(cnf_transformation,[],[f85]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_3234,plain,
% 23.41/3.49      ( r2_hidden(sK11,k9_relat_1(sK10,sK9)) ),
% 23.41/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_3218]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_14078,plain,
% 23.41/3.49      ( r2_hidden(k4_tarski(sK4(sK11,sK9,sK10),sK11),sK10)
% 23.41/3.49      | ~ r2_hidden(sK11,k9_relat_1(sK10,sK9))
% 23.41/3.49      | ~ v1_relat_1(sK10) ),
% 23.41/3.49      inference(instantiation,[status(thm)],[c_14]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_38147,plain,
% 23.41/3.49      ( ~ r2_hidden(k4_tarski(sK4(sK11,sK9,sK10),sK11),sK10)
% 23.41/3.49      | ~ v1_funct_1(sK10)
% 23.41/3.49      | ~ v1_relat_1(sK10)
% 23.41/3.49      | k1_funct_1(sK10,sK4(sK11,sK9,sK10)) = sK11 ),
% 23.41/3.49      inference(instantiation,[status(thm)],[c_17]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_85190,plain,
% 23.41/3.49      ( k1_funct_1(sK10,sK4(sK11,sK9,sK10)) = sK11 ),
% 23.41/3.49      inference(global_propositional_subsumption,
% 23.41/3.49                [status(thm)],
% 23.41/3.49                [c_83556,c_35,c_33,c_1748,c_3234,c_14078,c_38147]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_31,negated_conjecture,
% 23.41/3.49      ( ~ m1_subset_1(X0,sK7)
% 23.41/3.49      | ~ r2_hidden(X0,sK9)
% 23.41/3.49      | k1_funct_1(sK10,X0) != sK11 ),
% 23.41/3.49      inference(cnf_transformation,[],[f89]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1416,plain,
% 23.41/3.49      ( k1_funct_1(sK10,X0) != sK11
% 23.41/3.49      | m1_subset_1(X0,sK7) != iProver_top
% 23.41/3.49      | r2_hidden(X0,sK9) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_85197,plain,
% 23.41/3.49      ( m1_subset_1(sK4(sK11,sK9,sK10),sK7) != iProver_top
% 23.41/3.49      | r2_hidden(sK4(sK11,sK9,sK10),sK9) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_85190,c_1416]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_13,plain,
% 23.41/3.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 23.41/3.49      | r2_hidden(sK4(X0,X2,X1),X2)
% 23.41/3.49      | ~ v1_relat_1(X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f68]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_14080,plain,
% 23.41/3.49      ( r2_hidden(sK4(sK11,sK9,sK10),sK9)
% 23.41/3.49      | ~ r2_hidden(sK11,k9_relat_1(sK10,sK9))
% 23.41/3.49      | ~ v1_relat_1(sK10) ),
% 23.41/3.49      inference(instantiation,[status(thm)],[c_13]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_14081,plain,
% 23.41/3.49      ( r2_hidden(sK4(sK11,sK9,sK10),sK9) = iProver_top
% 23.41/3.49      | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top
% 23.41/3.49      | v1_relat_1(sK10) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_14080]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_85937,plain,
% 23.41/3.49      ( m1_subset_1(sK4(sK11,sK9,sK10),sK7) != iProver_top ),
% 23.41/3.49      inference(global_propositional_subsumption,
% 23.41/3.49                [status(thm)],
% 23.41/3.49                [c_85197,c_38,c_1749,c_3218,c_14081]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_85942,plain,
% 23.41/3.49      ( sK8 = k1_xboole_0
% 23.41/3.49      | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_5388,c_85937]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_652,plain,
% 23.41/3.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 23.41/3.49      theory(equality) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_18568,plain,
% 23.41/3.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 23.41/3.49      inference(instantiation,[status(thm)],[c_652]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_18570,plain,
% 23.41/3.49      ( v1_xboole_0(sK8)
% 23.41/3.49      | ~ v1_xboole_0(k1_xboole_0)
% 23.41/3.49      | sK8 != k1_xboole_0 ),
% 23.41/3.49      inference(instantiation,[status(thm)],[c_18568]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1,plain,
% 23.41/3.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f55]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1444,plain,
% 23.41/3.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.41/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_0,plain,
% 23.41/3.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f56]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1445,plain,
% 23.41/3.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 23.41/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_2422,plain,
% 23.41/3.49      ( r1_tarski(X0,X0) = iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_1444,c_1445]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_22,plain,
% 23.41/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.41/3.49      | ~ r2_hidden(X3,X0)
% 23.41/3.49      | r2_hidden(sK6(X3,X1,X2),X2) ),
% 23.41/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1425,plain,
% 23.41/3.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 23.41/3.49      | r2_hidden(X3,X0) != iProver_top
% 23.41/3.49      | r2_hidden(sK6(X3,X1,X2),X2) = iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_6273,plain,
% 23.41/3.49      ( r2_hidden(X0,sK10) != iProver_top
% 23.41/3.49      | r2_hidden(sK6(X0,sK7,sK8),sK8) = iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_1414,c_1425]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_7,plain,
% 23.41/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.41/3.49      | ~ r2_hidden(X2,X0)
% 23.41/3.49      | ~ v1_xboole_0(X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_5,plain,
% 23.41/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.41/3.49      inference(cnf_transformation,[],[f60]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_252,plain,
% 23.41/3.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.41/3.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_253,plain,
% 23.41/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.41/3.49      inference(renaming,[status(thm)],[c_252]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_324,plain,
% 23.41/3.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 23.41/3.49      inference(bin_hyper_res,[status(thm)],[c_7,c_253]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_1411,plain,
% 23.41/3.49      ( r2_hidden(X0,X1) != iProver_top
% 23.41/3.49      | r1_tarski(X1,X2) != iProver_top
% 23.41/3.49      | v1_xboole_0(X2) != iProver_top ),
% 23.41/3.49      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_6658,plain,
% 23.41/3.49      ( r2_hidden(X0,sK10) != iProver_top
% 23.41/3.49      | r1_tarski(sK8,X1) != iProver_top
% 23.41/3.49      | v1_xboole_0(X1) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_6273,c_1411]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_7146,plain,
% 23.41/3.49      ( r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 23.41/3.49      | r1_tarski(sK8,X2) != iProver_top
% 23.41/3.49      | v1_relat_1(sK10) != iProver_top
% 23.41/3.49      | v1_xboole_0(X2) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_1432,c_6658]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_16451,plain,
% 23.41/3.49      ( r1_tarski(sK8,X2) != iProver_top
% 23.41/3.49      | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 23.41/3.49      | v1_xboole_0(X2) != iProver_top ),
% 23.41/3.49      inference(global_propositional_subsumption,
% 23.41/3.49                [status(thm)],
% 23.41/3.49                [c_7146,c_38,c_1749]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_16452,plain,
% 23.41/3.49      ( r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 23.41/3.49      | r1_tarski(sK8,X2) != iProver_top
% 23.41/3.49      | v1_xboole_0(X2) != iProver_top ),
% 23.41/3.49      inference(renaming,[status(thm)],[c_16451]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_16467,plain,
% 23.41/3.49      ( r1_tarski(sK8,X0) != iProver_top
% 23.41/3.49      | v1_xboole_0(X0) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_3218,c_16452]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_16521,plain,
% 23.41/3.49      ( v1_xboole_0(sK8) != iProver_top ),
% 23.41/3.49      inference(superposition,[status(thm)],[c_2422,c_16467]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_16524,plain,
% 23.41/3.49      ( ~ v1_xboole_0(sK8) ),
% 23.41/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_16521]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(c_3,plain,
% 23.41/3.49      ( v1_xboole_0(k1_xboole_0) ),
% 23.41/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.41/3.49  
% 23.41/3.49  cnf(contradiction,plain,
% 23.41/3.49      ( $false ),
% 23.41/3.49      inference(minisat,
% 23.41/3.49                [status(thm)],
% 23.41/3.49                [c_85942,c_18570,c_16524,c_3218,c_3]) ).
% 23.41/3.49  
% 23.41/3.49  
% 23.41/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.41/3.49  
% 23.41/3.49  ------                               Statistics
% 23.41/3.49  
% 23.41/3.49  ------ Selected
% 23.41/3.49  
% 23.41/3.49  total_time:                             2.626
% 23.41/3.49  
%------------------------------------------------------------------------------
