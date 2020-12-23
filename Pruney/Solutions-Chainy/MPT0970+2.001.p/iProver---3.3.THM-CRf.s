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
% DateTime   : Thu Dec  3 12:00:45 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 460 expanded)
%              Number of clauses        :   84 ( 146 expanded)
%              Number of leaves         :   22 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          :  588 (2310 expanded)
%              Number of equality atoms :  232 ( 768 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK9(X3)) = X3
        & r2_hidden(sK9(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK6,sK7,sK8) != sK7
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK8,X4) = X3
              & r2_hidden(X4,sK6) )
          | ~ r2_hidden(X3,sK7) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK8,sK6,sK7)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k2_relset_1(sK6,sK7,sK8) != sK7
    & ! [X3] :
        ( ( k1_funct_1(sK8,sK9(X3)) = X3
          & r2_hidden(sK9(X3),sK6) )
        | ~ r2_hidden(X3,sK7) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f27,f48,f47])).

fof(f84,plain,(
    ! [X3] :
      ( r2_hidden(sK9(X3),sK6)
      | ~ r2_hidden(X3,sK7) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f41])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK4(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
            & r2_hidden(sK5(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f44,f43])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK5(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    k2_relset_1(sK6,sK7,sK8) != sK7 ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    ! [X3] :
      ( k1_funct_1(sK8,sK9(X3)) = X3
      | ~ r2_hidden(X3,sK7) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2)
                  & r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
                    & r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f39,f38,f37])).

fof(f63,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f89,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f90,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f81,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_33,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(sK9(X0),sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1937,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK9(X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK5(X2,X0),X2)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_473,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | k2_relset_1(X2,X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_474,plain,
    ( r2_hidden(sK5(X0,sK8),X0)
    | k2_relset_1(X1,X0,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1935,plain,
    ( k2_relset_1(X0,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK5(X1,sK8),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_3264,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1935])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_521,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_522,plain,
    ( k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_2166,plain,
    ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_522])).

cnf(c_3265,plain,
    ( k2_relat_1(sK8) = sK7
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3264,c_2166])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK6,sK7,sK8) != sK7 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1531,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2167,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_2168,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7)
    | k2_relset_1(sK6,sK7,sK8) = sK7
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_2172,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2168])).

cnf(c_12904,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3265,c_31,c_2167,c_2172])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,sK9(X0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1938,plain,
    ( k1_funct_1(sK8,sK9(X0)) = X0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_12910,plain,
    ( k1_funct_1(sK8,sK9(sK5(sK7,sK8))) = sK5(sK7,sK8) ),
    inference(superposition,[status(thm)],[c_12904,c_1938])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_437,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_438,plain,
    ( ~ v1_funct_2(sK8,X0,X1)
    | k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_1099,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != sK8
    | sK7 != X1
    | sK6 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_438])).

cnf(c_1100,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = sK7 ),
    inference(unflattening,[status(thm)],[c_1099])).

cnf(c_1175,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | k1_xboole_0 = sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_1100])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_530,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_531,plain,
    ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_2202,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_531])).

cnf(c_2347,plain,
    ( k1_relat_1(sK8) = sK6
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1175,c_2202])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_409,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_18])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_425,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_410,c_34])).

cnf(c_426,plain,
    ( r1_tarski(k2_relat_1(sK8),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_2169,plain,
    ( r1_tarski(k2_relat_1(sK8),sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_426])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2178,plain,
    ( ~ r1_tarski(k2_relset_1(sK6,sK7,sK8),sK7)
    | ~ r1_tarski(sK7,k2_relset_1(sK6,sK7,sK8))
    | k2_relset_1(sK6,sK7,sK8) = sK7 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1533,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2212,plain,
    ( ~ r1_tarski(X0,sK7)
    | r1_tarski(k2_relset_1(sK6,sK7,sK8),sK7)
    | k2_relset_1(sK6,sK7,sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_2359,plain,
    ( r1_tarski(k2_relset_1(sK6,sK7,sK8),sK7)
    | ~ r1_tarski(k2_relat_1(sK8),sK7)
    | k2_relset_1(sK6,sK7,sK8) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2212])).

cnf(c_2414,plain,
    ( ~ r1_tarski(X0,k2_relset_1(sK6,sK7,sK8))
    | r1_tarski(sK7,k2_relset_1(sK6,sK7,sK8))
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_2416,plain,
    ( r1_tarski(sK7,k2_relset_1(sK6,sK7,sK8))
    | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK6,sK7,sK8))
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2414])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2713,plain,
    ( r1_tarski(k1_xboole_0,k2_relset_1(sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4704,plain,
    ( k1_relat_1(sK8) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2347,c_31,c_2166,c_2167,c_2169,c_2178,c_2359,c_2416,c_2713])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_721,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_36])).

cnf(c_722,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_721])).

cnf(c_1928,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_723,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_539,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_540,plain,
    ( v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_2230,plain,
    ( v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_2231,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2230])).

cnf(c_3055,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1928,c_723,c_2167,c_2231])).

cnf(c_3056,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3055])).

cnf(c_4711,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4704,c_3056])).

cnf(c_12919,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) = iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),X0) != iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12910,c_4711])).

cnf(c_2244,plain,
    ( ~ r2_hidden(sK5(sK7,sK8),sK7)
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2245,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2244])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1940,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(X3,sK5(X2,X0)),X0)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_488,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
    | k2_relset_1(X3,X1,X2) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_489,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(X1,sK8)),sK8)
    | k2_relset_1(X2,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1934,plain,
    ( k2_relset_1(X0,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(k4_tarski(X2,sK5(X1,sK8)),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2669,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1934])).

cnf(c_2670,plain,
    ( k2_relat_1(sK8) = sK7
    | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2669,c_2166])).

cnf(c_2211,plain,
    ( k2_relat_1(sK8) != sK7 ),
    inference(demodulation,[status(thm)],[c_2166,c_31])).

cnf(c_3991,plain,
    ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2670,c_2211])).

cnf(c_3998,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1940,c_3991])).

cnf(c_13317,plain,
    ( r2_hidden(sK9(sK5(sK7,sK8)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12919,c_31,c_2167,c_2172,c_2231,c_2245,c_3998])).

cnf(c_13324,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1937,c_13317])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13324,c_2172,c_2167,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.31  % Computer   : n018.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 10:13:26 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 4.00/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.96  
% 4.00/0.96  ------  iProver source info
% 4.00/0.96  
% 4.00/0.96  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.96  git: non_committed_changes: false
% 4.00/0.96  git: last_make_outside_of_git: false
% 4.00/0.96  
% 4.00/0.96  ------ 
% 4.00/0.96  
% 4.00/0.96  ------ Input Options
% 4.00/0.96  
% 4.00/0.96  --out_options                           all
% 4.00/0.96  --tptp_safe_out                         true
% 4.00/0.96  --problem_path                          ""
% 4.00/0.96  --include_path                          ""
% 4.00/0.96  --clausifier                            res/vclausify_rel
% 4.00/0.96  --clausifier_options                    --mode clausify
% 4.00/0.96  --stdin                                 false
% 4.00/0.96  --stats_out                             all
% 4.00/0.96  
% 4.00/0.96  ------ General Options
% 4.00/0.96  
% 4.00/0.96  --fof                                   false
% 4.00/0.96  --time_out_real                         305.
% 4.00/0.96  --time_out_virtual                      -1.
% 4.00/0.96  --symbol_type_check                     false
% 4.00/0.96  --clausify_out                          false
% 4.00/0.96  --sig_cnt_out                           false
% 4.00/0.96  --trig_cnt_out                          false
% 4.00/0.96  --trig_cnt_out_tolerance                1.
% 4.00/0.96  --trig_cnt_out_sk_spl                   false
% 4.00/0.96  --abstr_cl_out                          false
% 4.00/0.96  
% 4.00/0.96  ------ Global Options
% 4.00/0.96  
% 4.00/0.96  --schedule                              default
% 4.00/0.96  --add_important_lit                     false
% 4.00/0.96  --prop_solver_per_cl                    1000
% 4.00/0.96  --min_unsat_core                        false
% 4.00/0.96  --soft_assumptions                      false
% 4.00/0.96  --soft_lemma_size                       3
% 4.00/0.96  --prop_impl_unit_size                   0
% 4.00/0.96  --prop_impl_unit                        []
% 4.00/0.96  --share_sel_clauses                     true
% 4.00/0.96  --reset_solvers                         false
% 4.00/0.96  --bc_imp_inh                            [conj_cone]
% 4.00/0.96  --conj_cone_tolerance                   3.
% 4.00/0.96  --extra_neg_conj                        none
% 4.00/0.96  --large_theory_mode                     true
% 4.00/0.96  --prolific_symb_bound                   200
% 4.00/0.96  --lt_threshold                          2000
% 4.00/0.96  --clause_weak_htbl                      true
% 4.00/0.96  --gc_record_bc_elim                     false
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing Options
% 4.00/0.96  
% 4.00/0.96  --preprocessing_flag                    true
% 4.00/0.96  --time_out_prep_mult                    0.1
% 4.00/0.96  --splitting_mode                        input
% 4.00/0.96  --splitting_grd                         true
% 4.00/0.96  --splitting_cvd                         false
% 4.00/0.96  --splitting_cvd_svl                     false
% 4.00/0.96  --splitting_nvd                         32
% 4.00/0.96  --sub_typing                            true
% 4.00/0.96  --prep_gs_sim                           true
% 4.00/0.96  --prep_unflatten                        true
% 4.00/0.96  --prep_res_sim                          true
% 4.00/0.96  --prep_upred                            true
% 4.00/0.96  --prep_sem_filter                       exhaustive
% 4.00/0.96  --prep_sem_filter_out                   false
% 4.00/0.96  --pred_elim                             true
% 4.00/0.96  --res_sim_input                         true
% 4.00/0.96  --eq_ax_congr_red                       true
% 4.00/0.96  --pure_diseq_elim                       true
% 4.00/0.96  --brand_transform                       false
% 4.00/0.96  --non_eq_to_eq                          false
% 4.00/0.96  --prep_def_merge                        true
% 4.00/0.96  --prep_def_merge_prop_impl              false
% 4.00/0.96  --prep_def_merge_mbd                    true
% 4.00/0.96  --prep_def_merge_tr_red                 false
% 4.00/0.96  --prep_def_merge_tr_cl                  false
% 4.00/0.96  --smt_preprocessing                     true
% 4.00/0.96  --smt_ac_axioms                         fast
% 4.00/0.96  --preprocessed_out                      false
% 4.00/0.96  --preprocessed_stats                    false
% 4.00/0.96  
% 4.00/0.96  ------ Abstraction refinement Options
% 4.00/0.96  
% 4.00/0.96  --abstr_ref                             []
% 4.00/0.96  --abstr_ref_prep                        false
% 4.00/0.96  --abstr_ref_until_sat                   false
% 4.00/0.96  --abstr_ref_sig_restrict                funpre
% 4.00/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.96  --abstr_ref_under                       []
% 4.00/0.96  
% 4.00/0.96  ------ SAT Options
% 4.00/0.96  
% 4.00/0.96  --sat_mode                              false
% 4.00/0.96  --sat_fm_restart_options                ""
% 4.00/0.96  --sat_gr_def                            false
% 4.00/0.96  --sat_epr_types                         true
% 4.00/0.96  --sat_non_cyclic_types                  false
% 4.00/0.96  --sat_finite_models                     false
% 4.00/0.96  --sat_fm_lemmas                         false
% 4.00/0.96  --sat_fm_prep                           false
% 4.00/0.96  --sat_fm_uc_incr                        true
% 4.00/0.96  --sat_out_model                         small
% 4.00/0.96  --sat_out_clauses                       false
% 4.00/0.96  
% 4.00/0.96  ------ QBF Options
% 4.00/0.96  
% 4.00/0.96  --qbf_mode                              false
% 4.00/0.96  --qbf_elim_univ                         false
% 4.00/0.96  --qbf_dom_inst                          none
% 4.00/0.96  --qbf_dom_pre_inst                      false
% 4.00/0.96  --qbf_sk_in                             false
% 4.00/0.96  --qbf_pred_elim                         true
% 4.00/0.96  --qbf_split                             512
% 4.00/0.96  
% 4.00/0.96  ------ BMC1 Options
% 4.00/0.96  
% 4.00/0.96  --bmc1_incremental                      false
% 4.00/0.96  --bmc1_axioms                           reachable_all
% 4.00/0.96  --bmc1_min_bound                        0
% 4.00/0.96  --bmc1_max_bound                        -1
% 4.00/0.96  --bmc1_max_bound_default                -1
% 4.00/0.96  --bmc1_symbol_reachability              true
% 4.00/0.96  --bmc1_property_lemmas                  false
% 4.00/0.96  --bmc1_k_induction                      false
% 4.00/0.96  --bmc1_non_equiv_states                 false
% 4.00/0.96  --bmc1_deadlock                         false
% 4.00/0.96  --bmc1_ucm                              false
% 4.00/0.96  --bmc1_add_unsat_core                   none
% 4.00/0.96  --bmc1_unsat_core_children              false
% 4.00/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.96  --bmc1_out_stat                         full
% 4.00/0.96  --bmc1_ground_init                      false
% 4.00/0.96  --bmc1_pre_inst_next_state              false
% 4.00/0.96  --bmc1_pre_inst_state                   false
% 4.00/0.96  --bmc1_pre_inst_reach_state             false
% 4.00/0.96  --bmc1_out_unsat_core                   false
% 4.00/0.96  --bmc1_aig_witness_out                  false
% 4.00/0.96  --bmc1_verbose                          false
% 4.00/0.96  --bmc1_dump_clauses_tptp                false
% 4.00/0.96  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.96  --bmc1_dump_file                        -
% 4.00/0.96  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.96  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.96  --bmc1_ucm_extend_mode                  1
% 4.00/0.96  --bmc1_ucm_init_mode                    2
% 4.00/0.96  --bmc1_ucm_cone_mode                    none
% 4.00/0.96  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.96  --bmc1_ucm_relax_model                  4
% 4.00/0.96  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.96  --bmc1_ucm_layered_model                none
% 4.00/0.96  --bmc1_ucm_max_lemma_size               10
% 4.00/0.96  
% 4.00/0.96  ------ AIG Options
% 4.00/0.96  
% 4.00/0.96  --aig_mode                              false
% 4.00/0.96  
% 4.00/0.96  ------ Instantiation Options
% 4.00/0.96  
% 4.00/0.96  --instantiation_flag                    true
% 4.00/0.96  --inst_sos_flag                         false
% 4.00/0.96  --inst_sos_phase                        true
% 4.00/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.96  --inst_lit_sel_side                     num_symb
% 4.00/0.96  --inst_solver_per_active                1400
% 4.00/0.96  --inst_solver_calls_frac                1.
% 4.00/0.96  --inst_passive_queue_type               priority_queues
% 4.00/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.96  --inst_passive_queues_freq              [25;2]
% 4.00/0.96  --inst_dismatching                      true
% 4.00/0.96  --inst_eager_unprocessed_to_passive     true
% 4.00/0.96  --inst_prop_sim_given                   true
% 4.00/0.96  --inst_prop_sim_new                     false
% 4.00/0.96  --inst_subs_new                         false
% 4.00/0.96  --inst_eq_res_simp                      false
% 4.00/0.96  --inst_subs_given                       false
% 4.00/0.96  --inst_orphan_elimination               true
% 4.00/0.96  --inst_learning_loop_flag               true
% 4.00/0.96  --inst_learning_start                   3000
% 4.00/0.96  --inst_learning_factor                  2
% 4.00/0.96  --inst_start_prop_sim_after_learn       3
% 4.00/0.96  --inst_sel_renew                        solver
% 4.00/0.96  --inst_lit_activity_flag                true
% 4.00/0.96  --inst_restr_to_given                   false
% 4.00/0.96  --inst_activity_threshold               500
% 4.00/0.96  --inst_out_proof                        true
% 4.00/0.96  
% 4.00/0.96  ------ Resolution Options
% 4.00/0.96  
% 4.00/0.96  --resolution_flag                       true
% 4.00/0.96  --res_lit_sel                           adaptive
% 4.00/0.96  --res_lit_sel_side                      none
% 4.00/0.96  --res_ordering                          kbo
% 4.00/0.96  --res_to_prop_solver                    active
% 4.00/0.96  --res_prop_simpl_new                    false
% 4.00/0.96  --res_prop_simpl_given                  true
% 4.00/0.96  --res_passive_queue_type                priority_queues
% 4.00/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.96  --res_passive_queues_freq               [15;5]
% 4.00/0.96  --res_forward_subs                      full
% 4.00/0.96  --res_backward_subs                     full
% 4.00/0.96  --res_forward_subs_resolution           true
% 4.00/0.96  --res_backward_subs_resolution          true
% 4.00/0.96  --res_orphan_elimination                true
% 4.00/0.96  --res_time_limit                        2.
% 4.00/0.96  --res_out_proof                         true
% 4.00/0.96  
% 4.00/0.96  ------ Superposition Options
% 4.00/0.96  
% 4.00/0.96  --superposition_flag                    true
% 4.00/0.96  --sup_passive_queue_type                priority_queues
% 4.00/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.96  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.96  --demod_completeness_check              fast
% 4.00/0.96  --demod_use_ground                      true
% 4.00/0.96  --sup_to_prop_solver                    passive
% 4.00/0.96  --sup_prop_simpl_new                    true
% 4.00/0.96  --sup_prop_simpl_given                  true
% 4.00/0.96  --sup_fun_splitting                     false
% 4.00/0.96  --sup_smt_interval                      50000
% 4.00/0.96  
% 4.00/0.96  ------ Superposition Simplification Setup
% 4.00/0.96  
% 4.00/0.96  --sup_indices_passive                   []
% 4.00/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.96  --sup_full_bw                           [BwDemod]
% 4.00/0.96  --sup_immed_triv                        [TrivRules]
% 4.00/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.96  --sup_immed_bw_main                     []
% 4.00/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.96  
% 4.00/0.96  ------ Combination Options
% 4.00/0.96  
% 4.00/0.96  --comb_res_mult                         3
% 4.00/0.96  --comb_sup_mult                         2
% 4.00/0.96  --comb_inst_mult                        10
% 4.00/0.96  
% 4.00/0.96  ------ Debug Options
% 4.00/0.96  
% 4.00/0.96  --dbg_backtrace                         false
% 4.00/0.96  --dbg_dump_prop_clauses                 false
% 4.00/0.96  --dbg_dump_prop_clauses_file            -
% 4.00/0.96  --dbg_out_stat                          false
% 4.00/0.96  ------ Parsing...
% 4.00/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.96  ------ Proving...
% 4.00/0.96  ------ Problem Properties 
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  clauses                                 28
% 4.00/0.96  conjectures                             3
% 4.00/0.96  EPR                                     3
% 4.00/0.96  Horn                                    22
% 4.00/0.96  unary                                   3
% 4.00/0.96  binary                                  7
% 4.00/0.96  lits                                    82
% 4.00/0.96  lits eq                                 31
% 4.00/0.96  fd_pure                                 0
% 4.00/0.96  fd_pseudo                               0
% 4.00/0.96  fd_cond                                 0
% 4.00/0.96  fd_pseudo_cond                          5
% 4.00/0.96  AC symbols                              0
% 4.00/0.96  
% 4.00/0.96  ------ Schedule dynamic 5 is on 
% 4.00/0.96  
% 4.00/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ 
% 4.00/0.96  Current options:
% 4.00/0.96  ------ 
% 4.00/0.96  
% 4.00/0.96  ------ Input Options
% 4.00/0.96  
% 4.00/0.96  --out_options                           all
% 4.00/0.96  --tptp_safe_out                         true
% 4.00/0.96  --problem_path                          ""
% 4.00/0.96  --include_path                          ""
% 4.00/0.96  --clausifier                            res/vclausify_rel
% 4.00/0.96  --clausifier_options                    --mode clausify
% 4.00/0.96  --stdin                                 false
% 4.00/0.96  --stats_out                             all
% 4.00/0.96  
% 4.00/0.96  ------ General Options
% 4.00/0.96  
% 4.00/0.96  --fof                                   false
% 4.00/0.96  --time_out_real                         305.
% 4.00/0.96  --time_out_virtual                      -1.
% 4.00/0.96  --symbol_type_check                     false
% 4.00/0.96  --clausify_out                          false
% 4.00/0.96  --sig_cnt_out                           false
% 4.00/0.96  --trig_cnt_out                          false
% 4.00/0.96  --trig_cnt_out_tolerance                1.
% 4.00/0.96  --trig_cnt_out_sk_spl                   false
% 4.00/0.96  --abstr_cl_out                          false
% 4.00/0.96  
% 4.00/0.96  ------ Global Options
% 4.00/0.96  
% 4.00/0.96  --schedule                              default
% 4.00/0.96  --add_important_lit                     false
% 4.00/0.96  --prop_solver_per_cl                    1000
% 4.00/0.96  --min_unsat_core                        false
% 4.00/0.96  --soft_assumptions                      false
% 4.00/0.96  --soft_lemma_size                       3
% 4.00/0.96  --prop_impl_unit_size                   0
% 4.00/0.96  --prop_impl_unit                        []
% 4.00/0.96  --share_sel_clauses                     true
% 4.00/0.96  --reset_solvers                         false
% 4.00/0.96  --bc_imp_inh                            [conj_cone]
% 4.00/0.96  --conj_cone_tolerance                   3.
% 4.00/0.96  --extra_neg_conj                        none
% 4.00/0.96  --large_theory_mode                     true
% 4.00/0.96  --prolific_symb_bound                   200
% 4.00/0.96  --lt_threshold                          2000
% 4.00/0.96  --clause_weak_htbl                      true
% 4.00/0.96  --gc_record_bc_elim                     false
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing Options
% 4.00/0.96  
% 4.00/0.96  --preprocessing_flag                    true
% 4.00/0.96  --time_out_prep_mult                    0.1
% 4.00/0.96  --splitting_mode                        input
% 4.00/0.96  --splitting_grd                         true
% 4.00/0.96  --splitting_cvd                         false
% 4.00/0.96  --splitting_cvd_svl                     false
% 4.00/0.96  --splitting_nvd                         32
% 4.00/0.96  --sub_typing                            true
% 4.00/0.96  --prep_gs_sim                           true
% 4.00/0.96  --prep_unflatten                        true
% 4.00/0.96  --prep_res_sim                          true
% 4.00/0.96  --prep_upred                            true
% 4.00/0.96  --prep_sem_filter                       exhaustive
% 4.00/0.96  --prep_sem_filter_out                   false
% 4.00/0.96  --pred_elim                             true
% 4.00/0.96  --res_sim_input                         true
% 4.00/0.96  --eq_ax_congr_red                       true
% 4.00/0.96  --pure_diseq_elim                       true
% 4.00/0.96  --brand_transform                       false
% 4.00/0.96  --non_eq_to_eq                          false
% 4.00/0.96  --prep_def_merge                        true
% 4.00/0.96  --prep_def_merge_prop_impl              false
% 4.00/0.96  --prep_def_merge_mbd                    true
% 4.00/0.96  --prep_def_merge_tr_red                 false
% 4.00/0.96  --prep_def_merge_tr_cl                  false
% 4.00/0.96  --smt_preprocessing                     true
% 4.00/0.96  --smt_ac_axioms                         fast
% 4.00/0.96  --preprocessed_out                      false
% 4.00/0.96  --preprocessed_stats                    false
% 4.00/0.96  
% 4.00/0.96  ------ Abstraction refinement Options
% 4.00/0.96  
% 4.00/0.96  --abstr_ref                             []
% 4.00/0.96  --abstr_ref_prep                        false
% 4.00/0.96  --abstr_ref_until_sat                   false
% 4.00/0.96  --abstr_ref_sig_restrict                funpre
% 4.00/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.96  --abstr_ref_under                       []
% 4.00/0.96  
% 4.00/0.96  ------ SAT Options
% 4.00/0.96  
% 4.00/0.96  --sat_mode                              false
% 4.00/0.96  --sat_fm_restart_options                ""
% 4.00/0.96  --sat_gr_def                            false
% 4.00/0.96  --sat_epr_types                         true
% 4.00/0.96  --sat_non_cyclic_types                  false
% 4.00/0.96  --sat_finite_models                     false
% 4.00/0.96  --sat_fm_lemmas                         false
% 4.00/0.96  --sat_fm_prep                           false
% 4.00/0.96  --sat_fm_uc_incr                        true
% 4.00/0.96  --sat_out_model                         small
% 4.00/0.96  --sat_out_clauses                       false
% 4.00/0.96  
% 4.00/0.96  ------ QBF Options
% 4.00/0.96  
% 4.00/0.96  --qbf_mode                              false
% 4.00/0.96  --qbf_elim_univ                         false
% 4.00/0.96  --qbf_dom_inst                          none
% 4.00/0.96  --qbf_dom_pre_inst                      false
% 4.00/0.96  --qbf_sk_in                             false
% 4.00/0.96  --qbf_pred_elim                         true
% 4.00/0.96  --qbf_split                             512
% 4.00/0.96  
% 4.00/0.96  ------ BMC1 Options
% 4.00/0.96  
% 4.00/0.96  --bmc1_incremental                      false
% 4.00/0.96  --bmc1_axioms                           reachable_all
% 4.00/0.96  --bmc1_min_bound                        0
% 4.00/0.96  --bmc1_max_bound                        -1
% 4.00/0.96  --bmc1_max_bound_default                -1
% 4.00/0.96  --bmc1_symbol_reachability              true
% 4.00/0.96  --bmc1_property_lemmas                  false
% 4.00/0.96  --bmc1_k_induction                      false
% 4.00/0.96  --bmc1_non_equiv_states                 false
% 4.00/0.96  --bmc1_deadlock                         false
% 4.00/0.96  --bmc1_ucm                              false
% 4.00/0.96  --bmc1_add_unsat_core                   none
% 4.00/0.96  --bmc1_unsat_core_children              false
% 4.00/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.96  --bmc1_out_stat                         full
% 4.00/0.96  --bmc1_ground_init                      false
% 4.00/0.96  --bmc1_pre_inst_next_state              false
% 4.00/0.96  --bmc1_pre_inst_state                   false
% 4.00/0.96  --bmc1_pre_inst_reach_state             false
% 4.00/0.96  --bmc1_out_unsat_core                   false
% 4.00/0.96  --bmc1_aig_witness_out                  false
% 4.00/0.96  --bmc1_verbose                          false
% 4.00/0.96  --bmc1_dump_clauses_tptp                false
% 4.00/0.96  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.96  --bmc1_dump_file                        -
% 4.00/0.96  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.96  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.96  --bmc1_ucm_extend_mode                  1
% 4.00/0.96  --bmc1_ucm_init_mode                    2
% 4.00/0.96  --bmc1_ucm_cone_mode                    none
% 4.00/0.96  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.96  --bmc1_ucm_relax_model                  4
% 4.00/0.96  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.96  --bmc1_ucm_layered_model                none
% 4.00/0.96  --bmc1_ucm_max_lemma_size               10
% 4.00/0.96  
% 4.00/0.96  ------ AIG Options
% 4.00/0.96  
% 4.00/0.96  --aig_mode                              false
% 4.00/0.96  
% 4.00/0.96  ------ Instantiation Options
% 4.00/0.96  
% 4.00/0.96  --instantiation_flag                    true
% 4.00/0.96  --inst_sos_flag                         false
% 4.00/0.96  --inst_sos_phase                        true
% 4.00/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.96  --inst_lit_sel_side                     none
% 4.00/0.96  --inst_solver_per_active                1400
% 4.00/0.96  --inst_solver_calls_frac                1.
% 4.00/0.96  --inst_passive_queue_type               priority_queues
% 4.00/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.96  --inst_passive_queues_freq              [25;2]
% 4.00/0.96  --inst_dismatching                      true
% 4.00/0.96  --inst_eager_unprocessed_to_passive     true
% 4.00/0.96  --inst_prop_sim_given                   true
% 4.00/0.96  --inst_prop_sim_new                     false
% 4.00/0.96  --inst_subs_new                         false
% 4.00/0.96  --inst_eq_res_simp                      false
% 4.00/0.96  --inst_subs_given                       false
% 4.00/0.96  --inst_orphan_elimination               true
% 4.00/0.96  --inst_learning_loop_flag               true
% 4.00/0.96  --inst_learning_start                   3000
% 4.00/0.96  --inst_learning_factor                  2
% 4.00/0.96  --inst_start_prop_sim_after_learn       3
% 4.00/0.96  --inst_sel_renew                        solver
% 4.00/0.96  --inst_lit_activity_flag                true
% 4.00/0.96  --inst_restr_to_given                   false
% 4.00/0.96  --inst_activity_threshold               500
% 4.00/0.96  --inst_out_proof                        true
% 4.00/0.96  
% 4.00/0.96  ------ Resolution Options
% 4.00/0.96  
% 4.00/0.96  --resolution_flag                       false
% 4.00/0.96  --res_lit_sel                           adaptive
% 4.00/0.96  --res_lit_sel_side                      none
% 4.00/0.96  --res_ordering                          kbo
% 4.00/0.96  --res_to_prop_solver                    active
% 4.00/0.96  --res_prop_simpl_new                    false
% 4.00/0.96  --res_prop_simpl_given                  true
% 4.00/0.96  --res_passive_queue_type                priority_queues
% 4.00/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.96  --res_passive_queues_freq               [15;5]
% 4.00/0.96  --res_forward_subs                      full
% 4.00/0.96  --res_backward_subs                     full
% 4.00/0.96  --res_forward_subs_resolution           true
% 4.00/0.96  --res_backward_subs_resolution          true
% 4.00/0.96  --res_orphan_elimination                true
% 4.00/0.96  --res_time_limit                        2.
% 4.00/0.96  --res_out_proof                         true
% 4.00/0.96  
% 4.00/0.96  ------ Superposition Options
% 4.00/0.96  
% 4.00/0.96  --superposition_flag                    true
% 4.00/0.96  --sup_passive_queue_type                priority_queues
% 4.00/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.96  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.96  --demod_completeness_check              fast
% 4.00/0.96  --demod_use_ground                      true
% 4.00/0.96  --sup_to_prop_solver                    passive
% 4.00/0.96  --sup_prop_simpl_new                    true
% 4.00/0.96  --sup_prop_simpl_given                  true
% 4.00/0.96  --sup_fun_splitting                     false
% 4.00/0.96  --sup_smt_interval                      50000
% 4.00/0.96  
% 4.00/0.96  ------ Superposition Simplification Setup
% 4.00/0.96  
% 4.00/0.96  --sup_indices_passive                   []
% 4.00/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.96  --sup_full_bw                           [BwDemod]
% 4.00/0.96  --sup_immed_triv                        [TrivRules]
% 4.00/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.96  --sup_immed_bw_main                     []
% 4.00/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.96  
% 4.00/0.96  ------ Combination Options
% 4.00/0.96  
% 4.00/0.96  --comb_res_mult                         3
% 4.00/0.96  --comb_sup_mult                         2
% 4.00/0.96  --comb_inst_mult                        10
% 4.00/0.96  
% 4.00/0.96  ------ Debug Options
% 4.00/0.96  
% 4.00/0.96  --dbg_backtrace                         false
% 4.00/0.96  --dbg_dump_prop_clauses                 false
% 4.00/0.96  --dbg_dump_prop_clauses_file            -
% 4.00/0.96  --dbg_out_stat                          false
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  ------ Proving...
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  % SZS status Theorem for theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  fof(f12,conjecture,(
% 4.00/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f13,negated_conjecture,(
% 4.00/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 4.00/0.96    inference(negated_conjecture,[],[f12])).
% 4.00/0.96  
% 4.00/0.96  fof(f26,plain,(
% 4.00/0.96    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.00/0.96    inference(ennf_transformation,[],[f13])).
% 4.00/0.96  
% 4.00/0.96  fof(f27,plain,(
% 4.00/0.96    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 4.00/0.96    inference(flattening,[],[f26])).
% 4.00/0.96  
% 4.00/0.96  fof(f48,plain,(
% 4.00/0.96    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK9(X3)) = X3 & r2_hidden(sK9(X3),X0)))) )),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f47,plain,(
% 4.00/0.96    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK6,sK7,sK8) != sK7 & ! [X3] : (? [X4] : (k1_funct_1(sK8,X4) = X3 & r2_hidden(X4,sK6)) | ~r2_hidden(X3,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f49,plain,(
% 4.00/0.96    k2_relset_1(sK6,sK7,sK8) != sK7 & ! [X3] : ((k1_funct_1(sK8,sK9(X3)) = X3 & r2_hidden(sK9(X3),sK6)) | ~r2_hidden(X3,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8)),
% 4.00/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f27,f48,f47])).
% 4.00/0.96  
% 4.00/0.96  fof(f84,plain,(
% 4.00/0.96    ( ! [X3] : (r2_hidden(sK9(X3),sK6) | ~r2_hidden(X3,sK7)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f49])).
% 4.00/0.96  
% 4.00/0.96  fof(f10,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f23,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(ennf_transformation,[],[f10])).
% 4.00/0.96  
% 4.00/0.96  fof(f41,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(nnf_transformation,[],[f23])).
% 4.00/0.96  
% 4.00/0.96  fof(f42,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(rectify,[],[f41])).
% 4.00/0.96  
% 4.00/0.96  fof(f44,plain,(
% 4.00/0.96    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f43,plain,(
% 4.00/0.96    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f45,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f44,f43])).
% 4.00/0.96  
% 4.00/0.96  fof(f72,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK5(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.96    inference(cnf_transformation,[],[f45])).
% 4.00/0.96  
% 4.00/0.96  fof(f83,plain,(
% 4.00/0.96    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 4.00/0.96    inference(cnf_transformation,[],[f49])).
% 4.00/0.96  
% 4.00/0.96  fof(f9,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f22,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(ennf_transformation,[],[f9])).
% 4.00/0.96  
% 4.00/0.96  fof(f71,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.96    inference(cnf_transformation,[],[f22])).
% 4.00/0.96  
% 4.00/0.96  fof(f86,plain,(
% 4.00/0.96    k2_relset_1(sK6,sK7,sK8) != sK7),
% 4.00/0.96    inference(cnf_transformation,[],[f49])).
% 4.00/0.96  
% 4.00/0.96  fof(f85,plain,(
% 4.00/0.96    ( ! [X3] : (k1_funct_1(sK8,sK9(X3)) = X3 | ~r2_hidden(X3,sK7)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f49])).
% 4.00/0.96  
% 4.00/0.96  fof(f82,plain,(
% 4.00/0.96    v1_funct_2(sK8,sK6,sK7)),
% 4.00/0.96    inference(cnf_transformation,[],[f49])).
% 4.00/0.96  
% 4.00/0.96  fof(f11,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f24,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(ennf_transformation,[],[f11])).
% 4.00/0.96  
% 4.00/0.96  fof(f25,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(flattening,[],[f24])).
% 4.00/0.96  
% 4.00/0.96  fof(f46,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(nnf_transformation,[],[f25])).
% 4.00/0.96  
% 4.00/0.96  fof(f75,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.96    inference(cnf_transformation,[],[f46])).
% 4.00/0.96  
% 4.00/0.96  fof(f8,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f21,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(ennf_transformation,[],[f8])).
% 4.00/0.96  
% 4.00/0.96  fof(f70,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.96    inference(cnf_transformation,[],[f21])).
% 4.00/0.96  
% 4.00/0.96  fof(f3,axiom,(
% 4.00/0.96    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f15,plain,(
% 4.00/0.96    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.00/0.96    inference(ennf_transformation,[],[f3])).
% 4.00/0.96  
% 4.00/0.96  fof(f30,plain,(
% 4.00/0.96    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.00/0.96    inference(nnf_transformation,[],[f15])).
% 4.00/0.96  
% 4.00/0.96  fof(f54,plain,(
% 4.00/0.96    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f30])).
% 4.00/0.96  
% 4.00/0.96  fof(f7,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f14,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.00/0.96    inference(pure_predicate_removal,[],[f7])).
% 4.00/0.96  
% 4.00/0.96  fof(f20,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(ennf_transformation,[],[f14])).
% 4.00/0.96  
% 4.00/0.96  fof(f69,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.96    inference(cnf_transformation,[],[f20])).
% 4.00/0.96  
% 4.00/0.96  fof(f6,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f19,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.96    inference(ennf_transformation,[],[f6])).
% 4.00/0.96  
% 4.00/0.96  fof(f68,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.96    inference(cnf_transformation,[],[f19])).
% 4.00/0.96  
% 4.00/0.96  fof(f1,axiom,(
% 4.00/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f28,plain,(
% 4.00/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.00/0.96    inference(nnf_transformation,[],[f1])).
% 4.00/0.96  
% 4.00/0.96  fof(f29,plain,(
% 4.00/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.00/0.96    inference(flattening,[],[f28])).
% 4.00/0.96  
% 4.00/0.96  fof(f52,plain,(
% 4.00/0.96    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f29])).
% 4.00/0.96  
% 4.00/0.96  fof(f2,axiom,(
% 4.00/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f53,plain,(
% 4.00/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f2])).
% 4.00/0.96  
% 4.00/0.96  fof(f5,axiom,(
% 4.00/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f17,plain,(
% 4.00/0.96    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.00/0.96    inference(ennf_transformation,[],[f5])).
% 4.00/0.96  
% 4.00/0.96  fof(f18,plain,(
% 4.00/0.96    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.00/0.96    inference(flattening,[],[f17])).
% 4.00/0.96  
% 4.00/0.96  fof(f35,plain,(
% 4.00/0.96    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.00/0.96    inference(nnf_transformation,[],[f18])).
% 4.00/0.96  
% 4.00/0.96  fof(f36,plain,(
% 4.00/0.96    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.00/0.96    inference(rectify,[],[f35])).
% 4.00/0.96  
% 4.00/0.96  fof(f39,plain,(
% 4.00/0.96    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f38,plain,(
% 4.00/0.96    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f37,plain,(
% 4.00/0.96    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f40,plain,(
% 4.00/0.96    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.00/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f39,f38,f37])).
% 4.00/0.96  
% 4.00/0.96  fof(f63,plain,(
% 4.00/0.96    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f40])).
% 4.00/0.96  
% 4.00/0.96  fof(f89,plain,(
% 4.00/0.96    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.96    inference(equality_resolution,[],[f63])).
% 4.00/0.96  
% 4.00/0.96  fof(f90,plain,(
% 4.00/0.96    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.96    inference(equality_resolution,[],[f89])).
% 4.00/0.96  
% 4.00/0.96  fof(f81,plain,(
% 4.00/0.96    v1_funct_1(sK8)),
% 4.00/0.96    inference(cnf_transformation,[],[f49])).
% 4.00/0.96  
% 4.00/0.96  fof(f4,axiom,(
% 4.00/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 4.00/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.96  
% 4.00/0.96  fof(f16,plain,(
% 4.00/0.96    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 4.00/0.96    inference(ennf_transformation,[],[f4])).
% 4.00/0.96  
% 4.00/0.96  fof(f31,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.00/0.96    inference(nnf_transformation,[],[f16])).
% 4.00/0.96  
% 4.00/0.96  fof(f32,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.00/0.96    inference(rectify,[],[f31])).
% 4.00/0.96  
% 4.00/0.96  fof(f33,plain,(
% 4.00/0.96    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 4.00/0.96    introduced(choice_axiom,[])).
% 4.00/0.96  
% 4.00/0.96  fof(f34,plain,(
% 4.00/0.96    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 4.00/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 4.00/0.96  
% 4.00/0.96  fof(f57,plain,(
% 4.00/0.96    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.00/0.96    inference(cnf_transformation,[],[f34])).
% 4.00/0.96  
% 4.00/0.96  fof(f73,plain,(
% 4.00/0.96    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.96    inference(cnf_transformation,[],[f45])).
% 4.00/0.96  
% 4.00/0.96  cnf(c_33,negated_conjecture,
% 4.00/0.96      ( ~ r2_hidden(X0,sK7) | r2_hidden(sK9(X0),sK6) ),
% 4.00/0.96      inference(cnf_transformation,[],[f84]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1937,plain,
% 4.00/0.96      ( r2_hidden(X0,sK7) != iProver_top
% 4.00/0.96      | r2_hidden(sK9(X0),sK6) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_24,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | r2_hidden(sK5(X2,X0),X2)
% 4.00/0.96      | k2_relset_1(X1,X2,X0) = X2 ),
% 4.00/0.96      inference(cnf_transformation,[],[f72]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_34,negated_conjecture,
% 4.00/0.96      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 4.00/0.96      inference(cnf_transformation,[],[f83]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_473,plain,
% 4.00/0.96      ( r2_hidden(sK5(X0,X1),X0)
% 4.00/0.96      | k2_relset_1(X2,X0,X1) = X0
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != X1 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_474,plain,
% 4.00/0.96      ( r2_hidden(sK5(X0,sK8),X0)
% 4.00/0.96      | k2_relset_1(X1,X0,sK8) = X0
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_473]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1935,plain,
% 4.00/0.96      ( k2_relset_1(X0,X1,sK8) = X1
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | r2_hidden(sK5(X1,sK8),X1) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3264,plain,
% 4.00/0.96      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 4.00/0.96      | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 4.00/0.96      inference(equality_resolution,[status(thm)],[c_1935]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_21,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.00/0.96      inference(cnf_transformation,[],[f71]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_521,plain,
% 4.00/0.96      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != X2 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_522,plain,
% 4.00/0.96      ( k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_521]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2166,plain,
% 4.00/0.96      ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
% 4.00/0.96      inference(equality_resolution,[status(thm)],[c_522]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3265,plain,
% 4.00/0.96      ( k2_relat_1(sK8) = sK7
% 4.00/0.96      | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 4.00/0.96      inference(demodulation,[status(thm)],[c_3264,c_2166]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_31,negated_conjecture,
% 4.00/0.96      ( k2_relset_1(sK6,sK7,sK8) != sK7 ),
% 4.00/0.96      inference(cnf_transformation,[],[f86]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1531,plain,( X0 = X0 ),theory(equality) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2167,plain,
% 4.00/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_1531]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2168,plain,
% 4.00/0.96      ( r2_hidden(sK5(sK7,sK8),sK7)
% 4.00/0.96      | k2_relset_1(sK6,sK7,sK8) = sK7
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_474]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2172,plain,
% 4.00/0.96      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_2168]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_12904,plain,
% 4.00/0.96      ( r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_3265,c_31,c_2167,c_2172]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_32,negated_conjecture,
% 4.00/0.96      ( ~ r2_hidden(X0,sK7) | k1_funct_1(sK8,sK9(X0)) = X0 ),
% 4.00/0.96      inference(cnf_transformation,[],[f85]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1938,plain,
% 4.00/0.96      ( k1_funct_1(sK8,sK9(X0)) = X0 | r2_hidden(X0,sK7) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_12910,plain,
% 4.00/0.96      ( k1_funct_1(sK8,sK9(sK5(sK7,sK8))) = sK5(sK7,sK8) ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_12904,c_1938]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_35,negated_conjecture,
% 4.00/0.96      ( v1_funct_2(sK8,sK6,sK7) ),
% 4.00/0.96      inference(cnf_transformation,[],[f82]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_30,plain,
% 4.00/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 4.00/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | k1_relset_1(X1,X2,X0) = X1
% 4.00/0.96      | k1_xboole_0 = X2 ),
% 4.00/0.96      inference(cnf_transformation,[],[f75]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_437,plain,
% 4.00/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 4.00/0.96      | k1_relset_1(X1,X2,X0) = X1
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != X0
% 4.00/0.96      | k1_xboole_0 = X2 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_438,plain,
% 4.00/0.96      ( ~ v1_funct_2(sK8,X0,X1)
% 4.00/0.96      | k1_relset_1(X0,X1,sK8) = X0
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | k1_xboole_0 = X1 ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_437]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1099,plain,
% 4.00/0.96      ( k1_relset_1(X0,X1,sK8) = X0
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != sK8
% 4.00/0.96      | sK7 != X1
% 4.00/0.96      | sK6 != X0
% 4.00/0.96      | k1_xboole_0 = X1 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_35,c_438]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1100,plain,
% 4.00/0.96      ( k1_relset_1(sK6,sK7,sK8) = sK6
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | k1_xboole_0 = sK7 ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_1099]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1175,plain,
% 4.00/0.96      ( k1_relset_1(sK6,sK7,sK8) = sK6 | k1_xboole_0 = sK7 ),
% 4.00/0.96      inference(equality_resolution_simp,[status(thm)],[c_1100]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_20,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.00/0.96      inference(cnf_transformation,[],[f70]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_530,plain,
% 4.00/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != X2 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_531,plain,
% 4.00/0.96      ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_530]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2202,plain,
% 4.00/0.96      ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
% 4.00/0.96      inference(equality_resolution,[status(thm)],[c_531]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2347,plain,
% 4.00/0.96      ( k1_relat_1(sK8) = sK6 | sK7 = k1_xboole_0 ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_1175,c_2202]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_5,plain,
% 4.00/0.96      ( ~ v5_relat_1(X0,X1)
% 4.00/0.96      | r1_tarski(k2_relat_1(X0),X1)
% 4.00/0.96      | ~ v1_relat_1(X0) ),
% 4.00/0.96      inference(cnf_transformation,[],[f54]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_19,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | v5_relat_1(X0,X2) ),
% 4.00/0.96      inference(cnf_transformation,[],[f69]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_404,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | r1_tarski(k2_relat_1(X3),X4)
% 4.00/0.96      | ~ v1_relat_1(X3)
% 4.00/0.96      | X0 != X3
% 4.00/0.96      | X2 != X4 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_405,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | r1_tarski(k2_relat_1(X0),X2)
% 4.00/0.96      | ~ v1_relat_1(X0) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_404]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_18,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | v1_relat_1(X0) ),
% 4.00/0.96      inference(cnf_transformation,[],[f68]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_409,plain,
% 4.00/0.96      ( r1_tarski(k2_relat_1(X0),X2)
% 4.00/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_405,c_18]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_410,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | r1_tarski(k2_relat_1(X0),X2) ),
% 4.00/0.96      inference(renaming,[status(thm)],[c_409]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_425,plain,
% 4.00/0.96      ( r1_tarski(k2_relat_1(X0),X1)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != X0 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_410,c_34]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_426,plain,
% 4.00/0.96      ( r1_tarski(k2_relat_1(sK8),X0)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_425]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2169,plain,
% 4.00/0.96      ( r1_tarski(k2_relat_1(sK8),sK7)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_426]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_0,plain,
% 4.00/0.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.00/0.96      inference(cnf_transformation,[],[f52]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2178,plain,
% 4.00/0.96      ( ~ r1_tarski(k2_relset_1(sK6,sK7,sK8),sK7)
% 4.00/0.96      | ~ r1_tarski(sK7,k2_relset_1(sK6,sK7,sK8))
% 4.00/0.96      | k2_relset_1(sK6,sK7,sK8) = sK7 ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_0]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1533,plain,
% 4.00/0.96      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 4.00/0.96      theory(equality) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2212,plain,
% 4.00/0.96      ( ~ r1_tarski(X0,sK7)
% 4.00/0.96      | r1_tarski(k2_relset_1(sK6,sK7,sK8),sK7)
% 4.00/0.96      | k2_relset_1(sK6,sK7,sK8) != X0 ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_1533]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2359,plain,
% 4.00/0.96      ( r1_tarski(k2_relset_1(sK6,sK7,sK8),sK7)
% 4.00/0.96      | ~ r1_tarski(k2_relat_1(sK8),sK7)
% 4.00/0.96      | k2_relset_1(sK6,sK7,sK8) != k2_relat_1(sK8) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_2212]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2414,plain,
% 4.00/0.96      ( ~ r1_tarski(X0,k2_relset_1(sK6,sK7,sK8))
% 4.00/0.96      | r1_tarski(sK7,k2_relset_1(sK6,sK7,sK8))
% 4.00/0.96      | sK7 != X0 ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_1533]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2416,plain,
% 4.00/0.96      ( r1_tarski(sK7,k2_relset_1(sK6,sK7,sK8))
% 4.00/0.96      | ~ r1_tarski(k1_xboole_0,k2_relset_1(sK6,sK7,sK8))
% 4.00/0.96      | sK7 != k1_xboole_0 ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_2414]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3,plain,
% 4.00/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 4.00/0.96      inference(cnf_transformation,[],[f53]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2713,plain,
% 4.00/0.96      ( r1_tarski(k1_xboole_0,k2_relset_1(sK6,sK7,sK8)) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_3]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_4704,plain,
% 4.00/0.96      ( k1_relat_1(sK8) = sK6 ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_2347,c_31,c_2166,c_2167,c_2169,c_2178,c_2359,c_2416,
% 4.00/0.96                 c_2713]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_14,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,X1)
% 4.00/0.96      | ~ r2_hidden(X0,k1_relat_1(X2))
% 4.00/0.96      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 4.00/0.96      | ~ v1_funct_1(X2)
% 4.00/0.96      | ~ v1_relat_1(X2) ),
% 4.00/0.96      inference(cnf_transformation,[],[f90]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_36,negated_conjecture,
% 4.00/0.96      ( v1_funct_1(sK8) ),
% 4.00/0.96      inference(cnf_transformation,[],[f81]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_721,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,X1)
% 4.00/0.96      | ~ r2_hidden(X0,k1_relat_1(X2))
% 4.00/0.96      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 4.00/0.96      | ~ v1_relat_1(X2)
% 4.00/0.96      | sK8 != X2 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_14,c_36]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_722,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,X1)
% 4.00/0.96      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 4.00/0.96      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
% 4.00/0.96      | ~ v1_relat_1(sK8) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_721]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1928,plain,
% 4.00/0.96      ( r2_hidden(X0,X1) != iProver_top
% 4.00/0.96      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.00/0.96      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 4.00/0.96      | v1_relat_1(sK8) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_723,plain,
% 4.00/0.96      ( r2_hidden(X0,X1) != iProver_top
% 4.00/0.96      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.00/0.96      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 4.00/0.96      | v1_relat_1(sK8) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_539,plain,
% 4.00/0.96      ( v1_relat_1(X0)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != X0 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_540,plain,
% 4.00/0.96      ( v1_relat_1(sK8)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_539]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2230,plain,
% 4.00/0.96      ( v1_relat_1(sK8)
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_540]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2231,plain,
% 4.00/0.96      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | v1_relat_1(sK8) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_2230]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3055,plain,
% 4.00/0.96      ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 4.00/0.96      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.00/0.96      | r2_hidden(X0,X1) != iProver_top ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_1928,c_723,c_2167,c_2231]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3056,plain,
% 4.00/0.96      ( r2_hidden(X0,X1) != iProver_top
% 4.00/0.96      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 4.00/0.96      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
% 4.00/0.96      inference(renaming,[status(thm)],[c_3055]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_4711,plain,
% 4.00/0.96      ( r2_hidden(X0,X1) != iProver_top
% 4.00/0.96      | r2_hidden(X0,sK6) != iProver_top
% 4.00/0.96      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
% 4.00/0.96      inference(demodulation,[status(thm)],[c_4704,c_3056]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_12919,plain,
% 4.00/0.96      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) = iProver_top
% 4.00/0.96      | r2_hidden(sK9(sK5(sK7,sK8)),X0) != iProver_top
% 4.00/0.96      | r2_hidden(sK9(sK5(sK7,sK8)),sK6) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_12910,c_4711]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2244,plain,
% 4.00/0.96      ( ~ r2_hidden(sK5(sK7,sK8),sK7)
% 4.00/0.96      | r2_hidden(sK9(sK5(sK7,sK8)),sK6) ),
% 4.00/0.96      inference(instantiation,[status(thm)],[c_33]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2245,plain,
% 4.00/0.96      ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
% 4.00/0.96      | r2_hidden(sK9(sK5(sK7,sK8)),sK6) = iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_2244]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_8,plain,
% 4.00/0.96      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.00/0.96      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 4.00/0.96      | ~ v1_relat_1(X1) ),
% 4.00/0.96      inference(cnf_transformation,[],[f57]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1940,plain,
% 4.00/0.96      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 4.00/0.96      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 4.00/0.96      | v1_relat_1(X1) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_23,plain,
% 4.00/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.96      | ~ r2_hidden(k4_tarski(X3,sK5(X2,X0)),X0)
% 4.00/0.96      | k2_relset_1(X1,X2,X0) = X2 ),
% 4.00/0.96      inference(cnf_transformation,[],[f73]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_488,plain,
% 4.00/0.96      ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
% 4.00/0.96      | k2_relset_1(X3,X1,X2) = X1
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | sK8 != X2 ),
% 4.00/0.96      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_489,plain,
% 4.00/0.96      ( ~ r2_hidden(k4_tarski(X0,sK5(X1,sK8)),sK8)
% 4.00/0.96      | k2_relset_1(X2,X1,sK8) = X1
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 4.00/0.96      inference(unflattening,[status(thm)],[c_488]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_1934,plain,
% 4.00/0.96      ( k2_relset_1(X0,X1,sK8) = X1
% 4.00/0.96      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 4.00/0.96      | r2_hidden(k4_tarski(X2,sK5(X1,sK8)),sK8) != iProver_top ),
% 4.00/0.96      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2669,plain,
% 4.00/0.96      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 4.00/0.96      | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 4.00/0.96      inference(equality_resolution,[status(thm)],[c_1934]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2670,plain,
% 4.00/0.96      ( k2_relat_1(sK8) = sK7
% 4.00/0.96      | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 4.00/0.96      inference(demodulation,[status(thm)],[c_2669,c_2166]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_2211,plain,
% 4.00/0.96      ( k2_relat_1(sK8) != sK7 ),
% 4.00/0.96      inference(demodulation,[status(thm)],[c_2166,c_31]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3991,plain,
% 4.00/0.96      ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_2670,c_2211]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_3998,plain,
% 4.00/0.96      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top
% 4.00/0.96      | v1_relat_1(sK8) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_1940,c_3991]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13317,plain,
% 4.00/0.96      ( r2_hidden(sK9(sK5(sK7,sK8)),X0) != iProver_top ),
% 4.00/0.96      inference(global_propositional_subsumption,
% 4.00/0.96                [status(thm)],
% 4.00/0.96                [c_12919,c_31,c_2167,c_2172,c_2231,c_2245,c_3998]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(c_13324,plain,
% 4.00/0.96      ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top ),
% 4.00/0.96      inference(superposition,[status(thm)],[c_1937,c_13317]) ).
% 4.00/0.96  
% 4.00/0.96  cnf(contradiction,plain,
% 4.00/0.96      ( $false ),
% 4.00/0.96      inference(minisat,[status(thm)],[c_13324,c_2172,c_2167,c_31]) ).
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/0.96  
% 4.00/0.96  ------                               Statistics
% 4.00/0.96  
% 4.00/0.96  ------ General
% 4.00/0.96  
% 4.00/0.96  abstr_ref_over_cycles:                  0
% 4.00/0.96  abstr_ref_under_cycles:                 0
% 4.00/0.96  gc_basic_clause_elim:                   0
% 4.00/0.96  forced_gc_time:                         0
% 4.00/0.96  parsing_time:                           0.011
% 4.00/0.96  unif_index_cands_time:                  0.
% 4.00/0.96  unif_index_add_time:                    0.
% 4.00/0.96  orderings_time:                         0.
% 4.00/0.96  out_proof_time:                         0.015
% 4.00/0.96  total_time:                             0.426
% 4.00/0.96  num_of_symbols:                         58
% 4.00/0.96  num_of_terms:                           17128
% 4.00/0.96  
% 4.00/0.96  ------ Preprocessing
% 4.00/0.96  
% 4.00/0.96  num_of_splits:                          0
% 4.00/0.96  num_of_split_atoms:                     0
% 4.00/0.96  num_of_reused_defs:                     0
% 4.00/0.96  num_eq_ax_congr_red:                    55
% 4.00/0.96  num_of_sem_filtered_clauses:            1
% 4.00/0.96  num_of_subtypes:                        0
% 4.00/0.96  monotx_restored_types:                  0
% 4.00/0.96  sat_num_of_epr_types:                   0
% 4.00/0.96  sat_num_of_non_cyclic_types:            0
% 4.00/0.96  sat_guarded_non_collapsed_types:        0
% 4.00/0.96  num_pure_diseq_elim:                    0
% 4.00/0.96  simp_replaced_by:                       0
% 4.00/0.96  res_preprocessed:                       159
% 4.00/0.96  prep_upred:                             0
% 4.00/0.96  prep_unflattend:                        47
% 4.00/0.96  smt_new_axioms:                         0
% 4.00/0.96  pred_elim_cands:                        3
% 4.00/0.96  pred_elim:                              4
% 4.00/0.96  pred_elim_cl:                           8
% 4.00/0.96  pred_elim_cycles:                       7
% 4.00/0.96  merged_defs:                            0
% 4.00/0.96  merged_defs_ncl:                        0
% 4.00/0.96  bin_hyper_res:                          0
% 4.00/0.96  prep_cycles:                            4
% 4.00/0.96  pred_elim_time:                         0.021
% 4.00/0.96  splitting_time:                         0.
% 4.00/0.96  sem_filter_time:                        0.
% 4.00/0.96  monotx_time:                            0.
% 4.00/0.96  subtype_inf_time:                       0.
% 4.00/0.96  
% 4.00/0.96  ------ Problem properties
% 4.00/0.96  
% 4.00/0.96  clauses:                                28
% 4.00/0.96  conjectures:                            3
% 4.00/0.96  epr:                                    3
% 4.00/0.96  horn:                                   22
% 4.00/0.96  ground:                                 4
% 4.00/0.96  unary:                                  3
% 4.00/0.96  binary:                                 7
% 4.00/0.96  lits:                                   82
% 4.00/0.96  lits_eq:                                31
% 4.00/0.96  fd_pure:                                0
% 4.00/0.96  fd_pseudo:                              0
% 4.00/0.96  fd_cond:                                0
% 4.00/0.96  fd_pseudo_cond:                         5
% 4.00/0.96  ac_symbols:                             0
% 4.00/0.96  
% 4.00/0.96  ------ Propositional Solver
% 4.00/0.96  
% 4.00/0.96  prop_solver_calls:                      30
% 4.00/0.96  prop_fast_solver_calls:                 1477
% 4.00/0.96  smt_solver_calls:                       0
% 4.00/0.96  smt_fast_solver_calls:                  0
% 4.00/0.96  prop_num_of_clauses:                    4786
% 4.00/0.96  prop_preprocess_simplified:             8101
% 4.00/0.96  prop_fo_subsumed:                       25
% 4.00/0.96  prop_solver_time:                       0.
% 4.00/0.96  smt_solver_time:                        0.
% 4.00/0.96  smt_fast_solver_time:                   0.
% 4.00/0.96  prop_fast_solver_time:                  0.
% 4.00/0.96  prop_unsat_core_time:                   0.
% 4.00/0.96  
% 4.00/0.96  ------ QBF
% 4.00/0.96  
% 4.00/0.96  qbf_q_res:                              0
% 4.00/0.96  qbf_num_tautologies:                    0
% 4.00/0.96  qbf_prep_cycles:                        0
% 4.00/0.96  
% 4.00/0.96  ------ BMC1
% 4.00/0.96  
% 4.00/0.96  bmc1_current_bound:                     -1
% 4.00/0.96  bmc1_last_solved_bound:                 -1
% 4.00/0.96  bmc1_unsat_core_size:                   -1
% 4.00/0.96  bmc1_unsat_core_parents_size:           -1
% 4.00/0.96  bmc1_merge_next_fun:                    0
% 4.00/0.96  bmc1_unsat_core_clauses_time:           0.
% 4.00/0.96  
% 4.00/0.96  ------ Instantiation
% 4.00/0.96  
% 4.00/0.96  inst_num_of_clauses:                    852
% 4.00/0.96  inst_num_in_passive:                    342
% 4.00/0.96  inst_num_in_active:                     487
% 4.00/0.96  inst_num_in_unprocessed:                23
% 4.00/0.96  inst_num_of_loops:                      570
% 4.00/0.96  inst_num_of_learning_restarts:          0
% 4.00/0.96  inst_num_moves_active_passive:          78
% 4.00/0.96  inst_lit_activity:                      0
% 4.00/0.96  inst_lit_activity_moves:                0
% 4.00/0.96  inst_num_tautologies:                   0
% 4.00/0.96  inst_num_prop_implied:                  0
% 4.00/0.96  inst_num_existing_simplified:           0
% 4.00/0.96  inst_num_eq_res_simplified:             0
% 4.00/0.96  inst_num_child_elim:                    0
% 4.00/0.96  inst_num_of_dismatching_blockings:      185
% 4.00/0.96  inst_num_of_non_proper_insts:           873
% 4.00/0.96  inst_num_of_duplicates:                 0
% 4.00/0.96  inst_inst_num_from_inst_to_res:         0
% 4.00/0.96  inst_dismatching_checking_time:         0.
% 4.00/0.96  
% 4.00/0.96  ------ Resolution
% 4.00/0.96  
% 4.00/0.96  res_num_of_clauses:                     0
% 4.00/0.96  res_num_in_passive:                     0
% 4.00/0.96  res_num_in_active:                      0
% 4.00/0.96  res_num_of_loops:                       163
% 4.00/0.96  res_forward_subset_subsumed:            113
% 4.00/0.96  res_backward_subset_subsumed:           2
% 4.00/0.96  res_forward_subsumed:                   0
% 4.00/0.96  res_backward_subsumed:                  0
% 4.00/0.96  res_forward_subsumption_resolution:     0
% 4.00/0.96  res_backward_subsumption_resolution:    0
% 4.00/0.96  res_clause_to_clause_subsumption:       1222
% 4.00/0.96  res_orphan_elimination:                 0
% 4.00/0.96  res_tautology_del:                      113
% 4.00/0.96  res_num_eq_res_simplified:              1
% 4.00/0.96  res_num_sel_changes:                    0
% 4.00/0.96  res_moves_from_active_to_pass:          0
% 4.00/0.96  
% 4.00/0.96  ------ Superposition
% 4.00/0.96  
% 4.00/0.96  sup_time_total:                         0.
% 4.00/0.96  sup_time_generating:                    0.
% 4.00/0.96  sup_time_sim_full:                      0.
% 4.00/0.96  sup_time_sim_immed:                     0.
% 4.00/0.96  
% 4.00/0.96  sup_num_of_clauses:                     587
% 4.00/0.96  sup_num_in_active:                      103
% 4.00/0.96  sup_num_in_passive:                     484
% 4.00/0.96  sup_num_of_loops:                       113
% 4.00/0.96  sup_fw_superposition:                   502
% 4.00/0.96  sup_bw_superposition:                   77
% 4.00/0.96  sup_immediate_simplified:               23
% 4.00/0.96  sup_given_eliminated:                   0
% 4.00/0.96  comparisons_done:                       0
% 4.00/0.96  comparisons_avoided:                    22
% 4.00/0.96  
% 4.00/0.96  ------ Simplifications
% 4.00/0.96  
% 4.00/0.96  
% 4.00/0.96  sim_fw_subset_subsumed:                 1
% 4.00/0.96  sim_bw_subset_subsumed:                 1
% 4.00/0.96  sim_fw_subsumed:                        4
% 4.00/0.96  sim_bw_subsumed:                        4
% 4.00/0.96  sim_fw_subsumption_res:                 1
% 4.00/0.96  sim_bw_subsumption_res:                 0
% 4.00/0.96  sim_tautology_del:                      1
% 4.00/0.96  sim_eq_tautology_del:                   6
% 4.00/0.96  sim_eq_res_simp:                        0
% 4.00/0.96  sim_fw_demodulated:                     2
% 4.00/0.96  sim_bw_demodulated:                     10
% 4.00/0.96  sim_light_normalised:                   17
% 4.00/0.96  sim_joinable_taut:                      0
% 4.00/0.96  sim_joinable_simp:                      0
% 4.00/0.96  sim_ac_normalised:                      0
% 4.00/0.96  sim_smt_subsumption:                    0
% 4.00/0.96  
%------------------------------------------------------------------------------
