%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:57 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 606 expanded)
%              Number of clauses        :   52 ( 127 expanded)
%              Number of leaves         :   20 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  447 (2112 expanded)
%              Number of equality atoms :  200 ( 837 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
      & k1_xboole_0 != sK6
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
      & v1_funct_2(sK7,k1_tarski(sK5),sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6)
    & k1_xboole_0 != sK6
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
    & v1_funct_2(sK7,k1_tarski(sK5),sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f44])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f82])).

fof(f90,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    v1_funct_2(sK7,k1_tarski(sK5),sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f80,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f98,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f77,plain,(
    v1_funct_1(sK7) ),
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

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f82])).

fof(f94,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f88])).

fof(f95,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f94])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1718,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1721,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3064,plain,
    ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1718,c_1721])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X2
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_724,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
    | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_726,plain,
    ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_30,c_29])).

cnf(c_3245,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_3064,c_726])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1724,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2219,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_1724])).

cnf(c_3332,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3245,c_2219])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_250,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_318,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_251])).

cnf(c_1717,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_6652,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK7),sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_3332,c_1717])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_494,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_495,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_1712,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1732,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4289,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK7),X1) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1712,c_1732])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1719,plain,
    ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5604,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top
    | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4289,c_1719])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1727,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3352,plain,
    ( r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_1727])).

cnf(c_5737,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5604,c_3352])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1720,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2696,plain,
    ( k2_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1718,c_1720])).

cnf(c_3331,plain,
    ( k2_relset_1(k1_relat_1(sK7),sK6,sK7) = k2_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_3245,c_2696])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1722,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4174,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3331,c_1722])).

cnf(c_3334,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3245,c_1718])).

cnf(c_7874,plain,
    ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4174,c_3334])).

cnf(c_7879,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7874,c_1724])).

cnf(c_9460,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK7),sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6652,c_3352,c_5604,c_7879])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1723,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9465,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9460,c_1723])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:29:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.32/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.01  
% 2.32/1.01  ------  iProver source info
% 2.32/1.01  
% 2.32/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.01  git: non_committed_changes: false
% 2.32/1.01  git: last_make_outside_of_git: false
% 2.32/1.01  
% 2.32/1.01  ------ 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options
% 2.32/1.01  
% 2.32/1.01  --out_options                           all
% 2.32/1.01  --tptp_safe_out                         true
% 2.32/1.01  --problem_path                          ""
% 2.32/1.01  --include_path                          ""
% 2.32/1.01  --clausifier                            res/vclausify_rel
% 2.32/1.01  --clausifier_options                    --mode clausify
% 2.32/1.01  --stdin                                 false
% 2.32/1.01  --stats_out                             all
% 2.32/1.01  
% 2.32/1.01  ------ General Options
% 2.32/1.01  
% 2.32/1.01  --fof                                   false
% 2.32/1.01  --time_out_real                         305.
% 2.32/1.01  --time_out_virtual                      -1.
% 2.32/1.01  --symbol_type_check                     false
% 2.32/1.01  --clausify_out                          false
% 2.32/1.01  --sig_cnt_out                           false
% 2.32/1.01  --trig_cnt_out                          false
% 2.32/1.01  --trig_cnt_out_tolerance                1.
% 2.32/1.01  --trig_cnt_out_sk_spl                   false
% 2.32/1.01  --abstr_cl_out                          false
% 2.32/1.01  
% 2.32/1.01  ------ Global Options
% 2.32/1.01  
% 2.32/1.01  --schedule                              default
% 2.32/1.01  --add_important_lit                     false
% 2.32/1.01  --prop_solver_per_cl                    1000
% 2.32/1.01  --min_unsat_core                        false
% 2.32/1.01  --soft_assumptions                      false
% 2.32/1.01  --soft_lemma_size                       3
% 2.32/1.01  --prop_impl_unit_size                   0
% 2.32/1.01  --prop_impl_unit                        []
% 2.32/1.01  --share_sel_clauses                     true
% 2.32/1.01  --reset_solvers                         false
% 2.32/1.01  --bc_imp_inh                            [conj_cone]
% 2.32/1.01  --conj_cone_tolerance                   3.
% 2.32/1.01  --extra_neg_conj                        none
% 2.32/1.01  --large_theory_mode                     true
% 2.32/1.01  --prolific_symb_bound                   200
% 2.32/1.01  --lt_threshold                          2000
% 2.32/1.01  --clause_weak_htbl                      true
% 2.32/1.01  --gc_record_bc_elim                     false
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing Options
% 2.32/1.01  
% 2.32/1.01  --preprocessing_flag                    true
% 2.32/1.01  --time_out_prep_mult                    0.1
% 2.32/1.01  --splitting_mode                        input
% 2.32/1.01  --splitting_grd                         true
% 2.32/1.01  --splitting_cvd                         false
% 2.32/1.01  --splitting_cvd_svl                     false
% 2.32/1.01  --splitting_nvd                         32
% 2.32/1.01  --sub_typing                            true
% 2.32/1.01  --prep_gs_sim                           true
% 2.32/1.01  --prep_unflatten                        true
% 2.32/1.01  --prep_res_sim                          true
% 2.32/1.01  --prep_upred                            true
% 2.32/1.01  --prep_sem_filter                       exhaustive
% 2.32/1.01  --prep_sem_filter_out                   false
% 2.32/1.01  --pred_elim                             true
% 2.32/1.01  --res_sim_input                         true
% 2.32/1.01  --eq_ax_congr_red                       true
% 2.32/1.01  --pure_diseq_elim                       true
% 2.32/1.01  --brand_transform                       false
% 2.32/1.01  --non_eq_to_eq                          false
% 2.32/1.01  --prep_def_merge                        true
% 2.32/1.01  --prep_def_merge_prop_impl              false
% 2.32/1.01  --prep_def_merge_mbd                    true
% 2.32/1.01  --prep_def_merge_tr_red                 false
% 2.32/1.01  --prep_def_merge_tr_cl                  false
% 2.32/1.01  --smt_preprocessing                     true
% 2.32/1.01  --smt_ac_axioms                         fast
% 2.32/1.01  --preprocessed_out                      false
% 2.32/1.01  --preprocessed_stats                    false
% 2.32/1.01  
% 2.32/1.01  ------ Abstraction refinement Options
% 2.32/1.01  
% 2.32/1.01  --abstr_ref                             []
% 2.32/1.01  --abstr_ref_prep                        false
% 2.32/1.01  --abstr_ref_until_sat                   false
% 2.32/1.01  --abstr_ref_sig_restrict                funpre
% 2.32/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.01  --abstr_ref_under                       []
% 2.32/1.01  
% 2.32/1.01  ------ SAT Options
% 2.32/1.01  
% 2.32/1.01  --sat_mode                              false
% 2.32/1.01  --sat_fm_restart_options                ""
% 2.32/1.01  --sat_gr_def                            false
% 2.32/1.01  --sat_epr_types                         true
% 2.32/1.01  --sat_non_cyclic_types                  false
% 2.32/1.01  --sat_finite_models                     false
% 2.32/1.01  --sat_fm_lemmas                         false
% 2.32/1.01  --sat_fm_prep                           false
% 2.32/1.01  --sat_fm_uc_incr                        true
% 2.32/1.01  --sat_out_model                         small
% 2.32/1.01  --sat_out_clauses                       false
% 2.32/1.01  
% 2.32/1.01  ------ QBF Options
% 2.32/1.01  
% 2.32/1.01  --qbf_mode                              false
% 2.32/1.01  --qbf_elim_univ                         false
% 2.32/1.01  --qbf_dom_inst                          none
% 2.32/1.01  --qbf_dom_pre_inst                      false
% 2.32/1.01  --qbf_sk_in                             false
% 2.32/1.01  --qbf_pred_elim                         true
% 2.32/1.01  --qbf_split                             512
% 2.32/1.01  
% 2.32/1.01  ------ BMC1 Options
% 2.32/1.01  
% 2.32/1.01  --bmc1_incremental                      false
% 2.32/1.01  --bmc1_axioms                           reachable_all
% 2.32/1.01  --bmc1_min_bound                        0
% 2.32/1.01  --bmc1_max_bound                        -1
% 2.32/1.01  --bmc1_max_bound_default                -1
% 2.32/1.01  --bmc1_symbol_reachability              true
% 2.32/1.01  --bmc1_property_lemmas                  false
% 2.32/1.01  --bmc1_k_induction                      false
% 2.32/1.01  --bmc1_non_equiv_states                 false
% 2.32/1.01  --bmc1_deadlock                         false
% 2.32/1.01  --bmc1_ucm                              false
% 2.32/1.01  --bmc1_add_unsat_core                   none
% 2.32/1.01  --bmc1_unsat_core_children              false
% 2.32/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.01  --bmc1_out_stat                         full
% 2.32/1.01  --bmc1_ground_init                      false
% 2.32/1.01  --bmc1_pre_inst_next_state              false
% 2.32/1.01  --bmc1_pre_inst_state                   false
% 2.32/1.01  --bmc1_pre_inst_reach_state             false
% 2.32/1.01  --bmc1_out_unsat_core                   false
% 2.32/1.01  --bmc1_aig_witness_out                  false
% 2.32/1.01  --bmc1_verbose                          false
% 2.32/1.01  --bmc1_dump_clauses_tptp                false
% 2.32/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.01  --bmc1_dump_file                        -
% 2.32/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.01  --bmc1_ucm_extend_mode                  1
% 2.32/1.01  --bmc1_ucm_init_mode                    2
% 2.32/1.01  --bmc1_ucm_cone_mode                    none
% 2.32/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.01  --bmc1_ucm_relax_model                  4
% 2.32/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.01  --bmc1_ucm_layered_model                none
% 2.32/1.01  --bmc1_ucm_max_lemma_size               10
% 2.32/1.01  
% 2.32/1.01  ------ AIG Options
% 2.32/1.01  
% 2.32/1.01  --aig_mode                              false
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation Options
% 2.32/1.01  
% 2.32/1.01  --instantiation_flag                    true
% 2.32/1.01  --inst_sos_flag                         false
% 2.32/1.01  --inst_sos_phase                        true
% 2.32/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel_side                     num_symb
% 2.32/1.01  --inst_solver_per_active                1400
% 2.32/1.01  --inst_solver_calls_frac                1.
% 2.32/1.01  --inst_passive_queue_type               priority_queues
% 2.32/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.01  --inst_passive_queues_freq              [25;2]
% 2.32/1.01  --inst_dismatching                      true
% 2.32/1.01  --inst_eager_unprocessed_to_passive     true
% 2.32/1.01  --inst_prop_sim_given                   true
% 2.32/1.01  --inst_prop_sim_new                     false
% 2.32/1.01  --inst_subs_new                         false
% 2.32/1.01  --inst_eq_res_simp                      false
% 2.32/1.01  --inst_subs_given                       false
% 2.32/1.01  --inst_orphan_elimination               true
% 2.32/1.01  --inst_learning_loop_flag               true
% 2.32/1.01  --inst_learning_start                   3000
% 2.32/1.01  --inst_learning_factor                  2
% 2.32/1.01  --inst_start_prop_sim_after_learn       3
% 2.32/1.01  --inst_sel_renew                        solver
% 2.32/1.01  --inst_lit_activity_flag                true
% 2.32/1.01  --inst_restr_to_given                   false
% 2.32/1.01  --inst_activity_threshold               500
% 2.32/1.01  --inst_out_proof                        true
% 2.32/1.01  
% 2.32/1.01  ------ Resolution Options
% 2.32/1.01  
% 2.32/1.01  --resolution_flag                       true
% 2.32/1.01  --res_lit_sel                           adaptive
% 2.32/1.01  --res_lit_sel_side                      none
% 2.32/1.01  --res_ordering                          kbo
% 2.32/1.01  --res_to_prop_solver                    active
% 2.32/1.01  --res_prop_simpl_new                    false
% 2.32/1.01  --res_prop_simpl_given                  true
% 2.32/1.01  --res_passive_queue_type                priority_queues
% 2.32/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.01  --res_passive_queues_freq               [15;5]
% 2.32/1.01  --res_forward_subs                      full
% 2.32/1.01  --res_backward_subs                     full
% 2.32/1.01  --res_forward_subs_resolution           true
% 2.32/1.01  --res_backward_subs_resolution          true
% 2.32/1.01  --res_orphan_elimination                true
% 2.32/1.01  --res_time_limit                        2.
% 2.32/1.01  --res_out_proof                         true
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Options
% 2.32/1.01  
% 2.32/1.01  --superposition_flag                    true
% 2.32/1.01  --sup_passive_queue_type                priority_queues
% 2.32/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.01  --demod_completeness_check              fast
% 2.32/1.01  --demod_use_ground                      true
% 2.32/1.01  --sup_to_prop_solver                    passive
% 2.32/1.01  --sup_prop_simpl_new                    true
% 2.32/1.01  --sup_prop_simpl_given                  true
% 2.32/1.01  --sup_fun_splitting                     false
% 2.32/1.01  --sup_smt_interval                      50000
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Simplification Setup
% 2.32/1.01  
% 2.32/1.01  --sup_indices_passive                   []
% 2.32/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_full_bw                           [BwDemod]
% 2.32/1.01  --sup_immed_triv                        [TrivRules]
% 2.32/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_immed_bw_main                     []
% 2.32/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  
% 2.32/1.01  ------ Combination Options
% 2.32/1.01  
% 2.32/1.01  --comb_res_mult                         3
% 2.32/1.01  --comb_sup_mult                         2
% 2.32/1.01  --comb_inst_mult                        10
% 2.32/1.01  
% 2.32/1.01  ------ Debug Options
% 2.32/1.01  
% 2.32/1.01  --dbg_backtrace                         false
% 2.32/1.01  --dbg_dump_prop_clauses                 false
% 2.32/1.01  --dbg_dump_prop_clauses_file            -
% 2.32/1.01  --dbg_out_stat                          false
% 2.32/1.01  ------ Parsing...
% 2.32/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.01  ------ Proving...
% 2.32/1.01  ------ Problem Properties 
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  clauses                                 28
% 2.32/1.01  conjectures                             3
% 2.32/1.01  EPR                                     3
% 2.32/1.01  Horn                                    22
% 2.32/1.01  unary                                   7
% 2.32/1.01  binary                                  7
% 2.32/1.01  lits                                    69
% 2.32/1.01  lits eq                                 24
% 2.32/1.01  fd_pure                                 0
% 2.32/1.01  fd_pseudo                               0
% 2.32/1.01  fd_cond                                 3
% 2.32/1.01  fd_pseudo_cond                          3
% 2.32/1.01  AC symbols                              0
% 2.32/1.01  
% 2.32/1.01  ------ Schedule dynamic 5 is on 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  ------ 
% 2.32/1.01  Current options:
% 2.32/1.01  ------ 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options
% 2.32/1.01  
% 2.32/1.01  --out_options                           all
% 2.32/1.01  --tptp_safe_out                         true
% 2.32/1.01  --problem_path                          ""
% 2.32/1.01  --include_path                          ""
% 2.32/1.01  --clausifier                            res/vclausify_rel
% 2.32/1.01  --clausifier_options                    --mode clausify
% 2.32/1.01  --stdin                                 false
% 2.32/1.01  --stats_out                             all
% 2.32/1.01  
% 2.32/1.01  ------ General Options
% 2.32/1.01  
% 2.32/1.01  --fof                                   false
% 2.32/1.01  --time_out_real                         305.
% 2.32/1.01  --time_out_virtual                      -1.
% 2.32/1.01  --symbol_type_check                     false
% 2.32/1.01  --clausify_out                          false
% 2.32/1.01  --sig_cnt_out                           false
% 2.32/1.01  --trig_cnt_out                          false
% 2.32/1.01  --trig_cnt_out_tolerance                1.
% 2.32/1.01  --trig_cnt_out_sk_spl                   false
% 2.32/1.01  --abstr_cl_out                          false
% 2.32/1.01  
% 2.32/1.01  ------ Global Options
% 2.32/1.01  
% 2.32/1.01  --schedule                              default
% 2.32/1.01  --add_important_lit                     false
% 2.32/1.01  --prop_solver_per_cl                    1000
% 2.32/1.01  --min_unsat_core                        false
% 2.32/1.01  --soft_assumptions                      false
% 2.32/1.01  --soft_lemma_size                       3
% 2.32/1.01  --prop_impl_unit_size                   0
% 2.32/1.01  --prop_impl_unit                        []
% 2.32/1.01  --share_sel_clauses                     true
% 2.32/1.01  --reset_solvers                         false
% 2.32/1.01  --bc_imp_inh                            [conj_cone]
% 2.32/1.01  --conj_cone_tolerance                   3.
% 2.32/1.01  --extra_neg_conj                        none
% 2.32/1.01  --large_theory_mode                     true
% 2.32/1.01  --prolific_symb_bound                   200
% 2.32/1.01  --lt_threshold                          2000
% 2.32/1.01  --clause_weak_htbl                      true
% 2.32/1.01  --gc_record_bc_elim                     false
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing Options
% 2.32/1.01  
% 2.32/1.01  --preprocessing_flag                    true
% 2.32/1.01  --time_out_prep_mult                    0.1
% 2.32/1.01  --splitting_mode                        input
% 2.32/1.01  --splitting_grd                         true
% 2.32/1.01  --splitting_cvd                         false
% 2.32/1.01  --splitting_cvd_svl                     false
% 2.32/1.01  --splitting_nvd                         32
% 2.32/1.01  --sub_typing                            true
% 2.32/1.01  --prep_gs_sim                           true
% 2.32/1.01  --prep_unflatten                        true
% 2.32/1.01  --prep_res_sim                          true
% 2.32/1.01  --prep_upred                            true
% 2.32/1.01  --prep_sem_filter                       exhaustive
% 2.32/1.01  --prep_sem_filter_out                   false
% 2.32/1.01  --pred_elim                             true
% 2.32/1.01  --res_sim_input                         true
% 2.32/1.01  --eq_ax_congr_red                       true
% 2.32/1.01  --pure_diseq_elim                       true
% 2.32/1.01  --brand_transform                       false
% 2.32/1.01  --non_eq_to_eq                          false
% 2.32/1.01  --prep_def_merge                        true
% 2.32/1.01  --prep_def_merge_prop_impl              false
% 2.32/1.01  --prep_def_merge_mbd                    true
% 2.32/1.01  --prep_def_merge_tr_red                 false
% 2.32/1.01  --prep_def_merge_tr_cl                  false
% 2.32/1.01  --smt_preprocessing                     true
% 2.32/1.01  --smt_ac_axioms                         fast
% 2.32/1.01  --preprocessed_out                      false
% 2.32/1.01  --preprocessed_stats                    false
% 2.32/1.01  
% 2.32/1.01  ------ Abstraction refinement Options
% 2.32/1.01  
% 2.32/1.01  --abstr_ref                             []
% 2.32/1.01  --abstr_ref_prep                        false
% 2.32/1.01  --abstr_ref_until_sat                   false
% 2.32/1.01  --abstr_ref_sig_restrict                funpre
% 2.32/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.01  --abstr_ref_under                       []
% 2.32/1.01  
% 2.32/1.01  ------ SAT Options
% 2.32/1.01  
% 2.32/1.01  --sat_mode                              false
% 2.32/1.01  --sat_fm_restart_options                ""
% 2.32/1.01  --sat_gr_def                            false
% 2.32/1.01  --sat_epr_types                         true
% 2.32/1.01  --sat_non_cyclic_types                  false
% 2.32/1.01  --sat_finite_models                     false
% 2.32/1.01  --sat_fm_lemmas                         false
% 2.32/1.01  --sat_fm_prep                           false
% 2.32/1.01  --sat_fm_uc_incr                        true
% 2.32/1.01  --sat_out_model                         small
% 2.32/1.01  --sat_out_clauses                       false
% 2.32/1.01  
% 2.32/1.01  ------ QBF Options
% 2.32/1.01  
% 2.32/1.01  --qbf_mode                              false
% 2.32/1.01  --qbf_elim_univ                         false
% 2.32/1.01  --qbf_dom_inst                          none
% 2.32/1.01  --qbf_dom_pre_inst                      false
% 2.32/1.01  --qbf_sk_in                             false
% 2.32/1.01  --qbf_pred_elim                         true
% 2.32/1.01  --qbf_split                             512
% 2.32/1.01  
% 2.32/1.01  ------ BMC1 Options
% 2.32/1.01  
% 2.32/1.01  --bmc1_incremental                      false
% 2.32/1.01  --bmc1_axioms                           reachable_all
% 2.32/1.01  --bmc1_min_bound                        0
% 2.32/1.01  --bmc1_max_bound                        -1
% 2.32/1.01  --bmc1_max_bound_default                -1
% 2.32/1.01  --bmc1_symbol_reachability              true
% 2.32/1.01  --bmc1_property_lemmas                  false
% 2.32/1.01  --bmc1_k_induction                      false
% 2.32/1.01  --bmc1_non_equiv_states                 false
% 2.32/1.01  --bmc1_deadlock                         false
% 2.32/1.01  --bmc1_ucm                              false
% 2.32/1.01  --bmc1_add_unsat_core                   none
% 2.32/1.01  --bmc1_unsat_core_children              false
% 2.32/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.01  --bmc1_out_stat                         full
% 2.32/1.01  --bmc1_ground_init                      false
% 2.32/1.01  --bmc1_pre_inst_next_state              false
% 2.32/1.01  --bmc1_pre_inst_state                   false
% 2.32/1.01  --bmc1_pre_inst_reach_state             false
% 2.32/1.01  --bmc1_out_unsat_core                   false
% 2.32/1.01  --bmc1_aig_witness_out                  false
% 2.32/1.01  --bmc1_verbose                          false
% 2.32/1.01  --bmc1_dump_clauses_tptp                false
% 2.32/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.01  --bmc1_dump_file                        -
% 2.32/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.01  --bmc1_ucm_extend_mode                  1
% 2.32/1.01  --bmc1_ucm_init_mode                    2
% 2.32/1.01  --bmc1_ucm_cone_mode                    none
% 2.32/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.01  --bmc1_ucm_relax_model                  4
% 2.32/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.01  --bmc1_ucm_layered_model                none
% 2.32/1.01  --bmc1_ucm_max_lemma_size               10
% 2.32/1.01  
% 2.32/1.01  ------ AIG Options
% 2.32/1.01  
% 2.32/1.01  --aig_mode                              false
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation Options
% 2.32/1.01  
% 2.32/1.01  --instantiation_flag                    true
% 2.32/1.01  --inst_sos_flag                         false
% 2.32/1.01  --inst_sos_phase                        true
% 2.32/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel_side                     none
% 2.32/1.01  --inst_solver_per_active                1400
% 2.32/1.01  --inst_solver_calls_frac                1.
% 2.32/1.01  --inst_passive_queue_type               priority_queues
% 2.32/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.01  --inst_passive_queues_freq              [25;2]
% 2.32/1.01  --inst_dismatching                      true
% 2.32/1.01  --inst_eager_unprocessed_to_passive     true
% 2.32/1.01  --inst_prop_sim_given                   true
% 2.32/1.01  --inst_prop_sim_new                     false
% 2.32/1.01  --inst_subs_new                         false
% 2.32/1.01  --inst_eq_res_simp                      false
% 2.32/1.01  --inst_subs_given                       false
% 2.32/1.01  --inst_orphan_elimination               true
% 2.32/1.01  --inst_learning_loop_flag               true
% 2.32/1.01  --inst_learning_start                   3000
% 2.32/1.01  --inst_learning_factor                  2
% 2.32/1.01  --inst_start_prop_sim_after_learn       3
% 2.32/1.01  --inst_sel_renew                        solver
% 2.32/1.01  --inst_lit_activity_flag                true
% 2.32/1.01  --inst_restr_to_given                   false
% 2.32/1.01  --inst_activity_threshold               500
% 2.32/1.01  --inst_out_proof                        true
% 2.32/1.01  
% 2.32/1.01  ------ Resolution Options
% 2.32/1.01  
% 2.32/1.01  --resolution_flag                       false
% 2.32/1.01  --res_lit_sel                           adaptive
% 2.32/1.01  --res_lit_sel_side                      none
% 2.32/1.01  --res_ordering                          kbo
% 2.32/1.01  --res_to_prop_solver                    active
% 2.32/1.01  --res_prop_simpl_new                    false
% 2.32/1.01  --res_prop_simpl_given                  true
% 2.32/1.01  --res_passive_queue_type                priority_queues
% 2.32/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.01  --res_passive_queues_freq               [15;5]
% 2.32/1.01  --res_forward_subs                      full
% 2.32/1.01  --res_backward_subs                     full
% 2.32/1.01  --res_forward_subs_resolution           true
% 2.32/1.01  --res_backward_subs_resolution          true
% 2.32/1.01  --res_orphan_elimination                true
% 2.32/1.01  --res_time_limit                        2.
% 2.32/1.01  --res_out_proof                         true
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Options
% 2.32/1.01  
% 2.32/1.01  --superposition_flag                    true
% 2.32/1.01  --sup_passive_queue_type                priority_queues
% 2.32/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.01  --demod_completeness_check              fast
% 2.32/1.01  --demod_use_ground                      true
% 2.32/1.01  --sup_to_prop_solver                    passive
% 2.32/1.01  --sup_prop_simpl_new                    true
% 2.32/1.01  --sup_prop_simpl_given                  true
% 2.32/1.01  --sup_fun_splitting                     false
% 2.32/1.01  --sup_smt_interval                      50000
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Simplification Setup
% 2.32/1.01  
% 2.32/1.01  --sup_indices_passive                   []
% 2.32/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_full_bw                           [BwDemod]
% 2.32/1.01  --sup_immed_triv                        [TrivRules]
% 2.32/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_immed_bw_main                     []
% 2.32/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  
% 2.32/1.01  ------ Combination Options
% 2.32/1.01  
% 2.32/1.01  --comb_res_mult                         3
% 2.32/1.01  --comb_sup_mult                         2
% 2.32/1.01  --comb_inst_mult                        10
% 2.32/1.01  
% 2.32/1.01  ------ Debug Options
% 2.32/1.01  
% 2.32/1.01  --dbg_backtrace                         false
% 2.32/1.01  --dbg_dump_prop_clauses                 false
% 2.32/1.01  --dbg_dump_prop_clauses_file            -
% 2.32/1.01  --dbg_out_stat                          false
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  ------ Proving...
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  % SZS status Theorem for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01   Resolution empty clause
% 2.32/1.01  
% 2.32/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  fof(f14,conjecture,(
% 2.32/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f15,negated_conjecture,(
% 2.32/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.32/1.01    inference(negated_conjecture,[],[f14])).
% 2.32/1.01  
% 2.32/1.01  fof(f25,plain,(
% 2.32/1.01    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.32/1.01    inference(ennf_transformation,[],[f15])).
% 2.32/1.01  
% 2.32/1.01  fof(f26,plain,(
% 2.32/1.01    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.32/1.01    inference(flattening,[],[f25])).
% 2.32/1.01  
% 2.32/1.01  fof(f44,plain,(
% 2.32/1.01    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7))),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f45,plain,(
% 2.32/1.01    ~r2_hidden(k1_funct_1(sK7,sK5),sK6) & k1_xboole_0 != sK6 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_2(sK7,k1_tarski(sK5),sK6) & v1_funct_1(sK7)),
% 2.32/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f26,f44])).
% 2.32/1.01  
% 2.32/1.01  fof(f79,plain,(
% 2.32/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))),
% 2.32/1.01    inference(cnf_transformation,[],[f45])).
% 2.32/1.01  
% 2.32/1.01  fof(f3,axiom,(
% 2.32/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f55,plain,(
% 2.32/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f3])).
% 2.32/1.01  
% 2.32/1.01  fof(f4,axiom,(
% 2.32/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f56,plain,(
% 2.32/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f4])).
% 2.32/1.01  
% 2.32/1.01  fof(f5,axiom,(
% 2.32/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f57,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f5])).
% 2.32/1.01  
% 2.32/1.01  fof(f82,plain,(
% 2.32/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.32/1.01    inference(definition_unfolding,[],[f56,f57])).
% 2.32/1.01  
% 2.32/1.01  fof(f83,plain,(
% 2.32/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.32/1.01    inference(definition_unfolding,[],[f55,f82])).
% 2.32/1.01  
% 2.32/1.01  fof(f90,plain,(
% 2.32/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))),
% 2.32/1.01    inference(definition_unfolding,[],[f79,f83])).
% 2.32/1.01  
% 2.32/1.01  fof(f11,axiom,(
% 2.32/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f21,plain,(
% 2.32/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.01    inference(ennf_transformation,[],[f11])).
% 2.32/1.01  
% 2.32/1.01  fof(f69,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.01    inference(cnf_transformation,[],[f21])).
% 2.32/1.01  
% 2.32/1.01  fof(f13,axiom,(
% 2.32/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f23,plain,(
% 2.32/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.01    inference(ennf_transformation,[],[f13])).
% 2.32/1.01  
% 2.32/1.01  fof(f24,plain,(
% 2.32/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.01    inference(flattening,[],[f23])).
% 2.32/1.01  
% 2.32/1.01  fof(f43,plain,(
% 2.32/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.01    inference(nnf_transformation,[],[f24])).
% 2.32/1.01  
% 2.32/1.01  fof(f71,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.01    inference(cnf_transformation,[],[f43])).
% 2.32/1.01  
% 2.32/1.01  fof(f78,plain,(
% 2.32/1.01    v1_funct_2(sK7,k1_tarski(sK5),sK6)),
% 2.32/1.01    inference(cnf_transformation,[],[f45])).
% 2.32/1.01  
% 2.32/1.01  fof(f91,plain,(
% 2.32/1.01    v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6)),
% 2.32/1.01    inference(definition_unfolding,[],[f78,f83])).
% 2.32/1.01  
% 2.32/1.01  fof(f80,plain,(
% 2.32/1.01    k1_xboole_0 != sK6),
% 2.32/1.01    inference(cnf_transformation,[],[f45])).
% 2.32/1.01  
% 2.32/1.01  fof(f6,axiom,(
% 2.32/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f36,plain,(
% 2.32/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.32/1.01    inference(nnf_transformation,[],[f6])).
% 2.32/1.01  
% 2.32/1.01  fof(f58,plain,(
% 2.32/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.32/1.01    inference(cnf_transformation,[],[f36])).
% 2.32/1.01  
% 2.32/1.01  fof(f7,axiom,(
% 2.32/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f17,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.32/1.01    inference(ennf_transformation,[],[f7])).
% 2.32/1.01  
% 2.32/1.01  fof(f60,plain,(
% 2.32/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f17])).
% 2.32/1.01  
% 2.32/1.01  fof(f59,plain,(
% 2.32/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f36])).
% 2.32/1.01  
% 2.32/1.01  fof(f9,axiom,(
% 2.32/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f18,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f9])).
% 2.32/1.01  
% 2.32/1.01  fof(f19,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/1.01    inference(flattening,[],[f18])).
% 2.32/1.01  
% 2.32/1.01  fof(f37,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/1.01    inference(nnf_transformation,[],[f19])).
% 2.32/1.01  
% 2.32/1.01  fof(f38,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/1.01    inference(rectify,[],[f37])).
% 2.32/1.01  
% 2.32/1.01  fof(f41,plain,(
% 2.32/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f40,plain,(
% 2.32/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f39,plain,(
% 2.32/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f42,plain,(
% 2.32/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.32/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f38,f41,f40,f39])).
% 2.32/1.01  
% 2.32/1.01  fof(f64,plain,(
% 2.32/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f42])).
% 2.32/1.01  
% 2.32/1.01  fof(f97,plain,(
% 2.32/1.01    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/1.01    inference(equality_resolution,[],[f64])).
% 2.32/1.01  
% 2.32/1.01  fof(f98,plain,(
% 2.32/1.01    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.32/1.01    inference(equality_resolution,[],[f97])).
% 2.32/1.01  
% 2.32/1.01  fof(f77,plain,(
% 2.32/1.01    v1_funct_1(sK7)),
% 2.32/1.01    inference(cnf_transformation,[],[f45])).
% 2.32/1.01  
% 2.32/1.01  fof(f1,axiom,(
% 2.32/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f16,plain,(
% 2.32/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.32/1.01    inference(ennf_transformation,[],[f1])).
% 2.32/1.01  
% 2.32/1.01  fof(f27,plain,(
% 2.32/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.01    inference(nnf_transformation,[],[f16])).
% 2.32/1.01  
% 2.32/1.01  fof(f28,plain,(
% 2.32/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.01    inference(rectify,[],[f27])).
% 2.32/1.01  
% 2.32/1.01  fof(f29,plain,(
% 2.32/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f30,plain,(
% 2.32/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.32/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.32/1.01  
% 2.32/1.01  fof(f46,plain,(
% 2.32/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f30])).
% 2.32/1.01  
% 2.32/1.01  fof(f81,plain,(
% 2.32/1.01    ~r2_hidden(k1_funct_1(sK7,sK5),sK6)),
% 2.32/1.01    inference(cnf_transformation,[],[f45])).
% 2.32/1.01  
% 2.32/1.01  fof(f2,axiom,(
% 2.32/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f31,plain,(
% 2.32/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.32/1.01    inference(nnf_transformation,[],[f2])).
% 2.32/1.01  
% 2.32/1.01  fof(f32,plain,(
% 2.32/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.32/1.01    inference(flattening,[],[f31])).
% 2.32/1.01  
% 2.32/1.01  fof(f33,plain,(
% 2.32/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.32/1.01    inference(rectify,[],[f32])).
% 2.32/1.01  
% 2.32/1.01  fof(f34,plain,(
% 2.32/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f35,plain,(
% 2.32/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.32/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 2.32/1.01  
% 2.32/1.01  fof(f50,plain,(
% 2.32/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.32/1.01    inference(cnf_transformation,[],[f35])).
% 2.32/1.01  
% 2.32/1.01  fof(f88,plain,(
% 2.32/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.32/1.01    inference(definition_unfolding,[],[f50,f82])).
% 2.32/1.01  
% 2.32/1.01  fof(f94,plain,(
% 2.32/1.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 2.32/1.02    inference(equality_resolution,[],[f88])).
% 2.32/1.02  
% 2.32/1.02  fof(f95,plain,(
% 2.32/1.02    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 2.32/1.02    inference(equality_resolution,[],[f94])).
% 2.32/1.02  
% 2.32/1.02  fof(f12,axiom,(
% 2.32/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.02  
% 2.32/1.02  fof(f22,plain,(
% 2.32/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.02    inference(ennf_transformation,[],[f12])).
% 2.32/1.02  
% 2.32/1.02  fof(f70,plain,(
% 2.32/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.02    inference(cnf_transformation,[],[f22])).
% 2.32/1.02  
% 2.32/1.02  fof(f10,axiom,(
% 2.32/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.02  
% 2.32/1.02  fof(f20,plain,(
% 2.32/1.02    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.32/1.02    inference(ennf_transformation,[],[f10])).
% 2.32/1.02  
% 2.32/1.02  fof(f68,plain,(
% 2.32/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.32/1.02    inference(cnf_transformation,[],[f20])).
% 2.32/1.02  
% 2.32/1.02  fof(f8,axiom,(
% 2.32/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.32/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.02  
% 2.32/1.02  fof(f61,plain,(
% 2.32/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.32/1.02    inference(cnf_transformation,[],[f8])).
% 2.32/1.02  
% 2.32/1.02  cnf(c_30,negated_conjecture,
% 2.32/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
% 2.32/1.02      inference(cnf_transformation,[],[f90]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1718,plain,
% 2.32/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_20,plain,
% 2.32/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.32/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1721,plain,
% 2.32/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.32/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3064,plain,
% 2.32/1.02      ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k1_relat_1(sK7) ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_1718,c_1721]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_27,plain,
% 2.32/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.32/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.32/1.02      | k1_xboole_0 = X2 ),
% 2.32/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_31,negated_conjecture,
% 2.32/1.02      ( v1_funct_2(sK7,k2_enumset1(sK5,sK5,sK5,sK5),sK6) ),
% 2.32/1.02      inference(cnf_transformation,[],[f91]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_723,plain,
% 2.32/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.02      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 2.32/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.32/1.02      | sK6 != X2
% 2.32/1.02      | sK7 != X0
% 2.32/1.02      | k1_xboole_0 = X2 ),
% 2.32/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_724,plain,
% 2.32/1.02      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))
% 2.32/1.02      | k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5)
% 2.32/1.02      | k1_xboole_0 = sK6 ),
% 2.32/1.02      inference(unflattening,[status(thm)],[c_723]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_29,negated_conjecture,
% 2.32/1.02      ( k1_xboole_0 != sK6 ),
% 2.32/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_726,plain,
% 2.32/1.02      ( k1_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_724,c_30,c_29]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3245,plain,
% 2.32/1.02      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK7) ),
% 2.32/1.02      inference(demodulation,[status(thm)],[c_3064,c_726]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_10,plain,
% 2.32/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1724,plain,
% 2.32/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.32/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2219,plain,
% 2.32/1.02      ( r1_tarski(sK7,k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_1718,c_1724]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3332,plain,
% 2.32/1.02      ( r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),sK6)) = iProver_top ),
% 2.32/1.02      inference(demodulation,[status(thm)],[c_3245,c_2219]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_11,plain,
% 2.32/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.32/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_9,plain,
% 2.32/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_250,plain,
% 2.32/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.32/1.02      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_251,plain,
% 2.32/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.32/1.02      inference(renaming,[status(thm)],[c_250]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_318,plain,
% 2.32/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.32/1.02      inference(bin_hyper_res,[status(thm)],[c_11,c_251]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1717,plain,
% 2.32/1.02      ( r1_tarski(X0,X1) != iProver_top
% 2.32/1.02      | v1_relat_1(X1) != iProver_top
% 2.32/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_6652,plain,
% 2.32/1.02      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK7),sK6)) != iProver_top
% 2.32/1.02      | v1_relat_1(sK7) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_3332,c_1717]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_16,plain,
% 2.32/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.32/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.32/1.02      | ~ v1_funct_1(X1)
% 2.32/1.02      | ~ v1_relat_1(X1) ),
% 2.32/1.02      inference(cnf_transformation,[],[f98]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_32,negated_conjecture,
% 2.32/1.02      ( v1_funct_1(sK7) ),
% 2.32/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_494,plain,
% 2.32/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.32/1.02      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.32/1.02      | ~ v1_relat_1(X1)
% 2.32/1.02      | sK7 != X1 ),
% 2.32/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_495,plain,
% 2.32/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 2.32/1.02      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 2.32/1.02      | ~ v1_relat_1(sK7) ),
% 2.32/1.02      inference(unflattening,[status(thm)],[c_494]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1712,plain,
% 2.32/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.32/1.02      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 2.32/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2,plain,
% 2.32/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.32/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1732,plain,
% 2.32/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.32/1.02      | r2_hidden(X0,X2) = iProver_top
% 2.32/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4289,plain,
% 2.32/1.02      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 2.32/1.02      | r2_hidden(k1_funct_1(sK7,X0),X1) = iProver_top
% 2.32/1.02      | r1_tarski(k2_relat_1(sK7),X1) != iProver_top
% 2.32/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_1712,c_1732]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_28,negated_conjecture,
% 2.32/1.02      ( ~ r2_hidden(k1_funct_1(sK7,sK5),sK6) ),
% 2.32/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1719,plain,
% 2.32/1.02      ( r2_hidden(k1_funct_1(sK7,sK5),sK6) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5604,plain,
% 2.32/1.02      ( r2_hidden(sK5,k1_relat_1(sK7)) != iProver_top
% 2.32/1.02      | r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 2.32/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_4289,c_1719]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_7,plain,
% 2.32/1.02      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 2.32/1.02      inference(cnf_transformation,[],[f95]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1727,plain,
% 2.32/1.02      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3352,plain,
% 2.32/1.02      ( r2_hidden(sK5,k1_relat_1(sK7)) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_3245,c_1727]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_5737,plain,
% 2.32/1.02      ( r1_tarski(k2_relat_1(sK7),sK6) != iProver_top
% 2.32/1.02      | v1_relat_1(sK7) != iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5604,c_3352]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_21,plain,
% 2.32/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.32/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1720,plain,
% 2.32/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.32/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_2696,plain,
% 2.32/1.02      ( k2_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK7) = k2_relat_1(sK7) ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_1718,c_1720]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3331,plain,
% 2.32/1.02      ( k2_relset_1(k1_relat_1(sK7),sK6,sK7) = k2_relat_1(sK7) ),
% 2.32/1.02      inference(demodulation,[status(thm)],[c_3245,c_2696]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_19,plain,
% 2.32/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.32/1.02      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.32/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1722,plain,
% 2.32/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.32/1.02      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_4174,plain,
% 2.32/1.02      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK6)) = iProver_top
% 2.32/1.02      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) != iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_3331,c_1722]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_3334,plain,
% 2.32/1.02      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK6))) = iProver_top ),
% 2.32/1.02      inference(demodulation,[status(thm)],[c_3245,c_1718]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_7874,plain,
% 2.32/1.02      ( m1_subset_1(k2_relat_1(sK7),k1_zfmisc_1(sK6)) = iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,[status(thm)],[c_4174,c_3334]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_7879,plain,
% 2.32/1.02      ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
% 2.32/1.02      inference(superposition,[status(thm)],[c_7874,c_1724]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_9460,plain,
% 2.32/1.02      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK7),sK6)) != iProver_top ),
% 2.32/1.02      inference(global_propositional_subsumption,
% 2.32/1.02                [status(thm)],
% 2.32/1.02                [c_6652,c_3352,c_5604,c_7879]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_12,plain,
% 2.32/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.32/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_1723,plain,
% 2.32/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.32/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.32/1.02  
% 2.32/1.02  cnf(c_9465,plain,
% 2.32/1.02      ( $false ),
% 2.32/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_9460,c_1723]) ).
% 2.32/1.02  
% 2.32/1.02  
% 2.32/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.02  
% 2.32/1.02  ------                               Statistics
% 2.32/1.02  
% 2.32/1.02  ------ General
% 2.32/1.02  
% 2.32/1.02  abstr_ref_over_cycles:                  0
% 2.32/1.02  abstr_ref_under_cycles:                 0
% 2.32/1.02  gc_basic_clause_elim:                   0
% 2.32/1.02  forced_gc_time:                         0
% 2.32/1.02  parsing_time:                           0.011
% 2.32/1.02  unif_index_cands_time:                  0.
% 2.32/1.02  unif_index_add_time:                    0.
% 2.32/1.02  orderings_time:                         0.
% 2.32/1.02  out_proof_time:                         0.008
% 2.32/1.02  total_time:                             0.284
% 2.32/1.02  num_of_symbols:                         54
% 2.32/1.02  num_of_terms:                           8311
% 2.32/1.02  
% 2.32/1.02  ------ Preprocessing
% 2.32/1.02  
% 2.32/1.02  num_of_splits:                          0
% 2.32/1.02  num_of_split_atoms:                     0
% 2.32/1.02  num_of_reused_defs:                     0
% 2.32/1.02  num_eq_ax_congr_red:                    46
% 2.32/1.02  num_of_sem_filtered_clauses:            1
% 2.32/1.02  num_of_subtypes:                        0
% 2.32/1.02  monotx_restored_types:                  0
% 2.32/1.02  sat_num_of_epr_types:                   0
% 2.32/1.02  sat_num_of_non_cyclic_types:            0
% 2.32/1.02  sat_guarded_non_collapsed_types:        0
% 2.32/1.02  num_pure_diseq_elim:                    0
% 2.32/1.02  simp_replaced_by:                       0
% 2.32/1.02  res_preprocessed:                       148
% 2.32/1.02  prep_upred:                             0
% 2.32/1.02  prep_unflattend:                        45
% 2.32/1.02  smt_new_axioms:                         0
% 2.32/1.02  pred_elim_cands:                        4
% 2.32/1.02  pred_elim:                              2
% 2.32/1.02  pred_elim_cl:                           5
% 2.32/1.02  pred_elim_cycles:                       5
% 2.32/1.02  merged_defs:                            8
% 2.32/1.02  merged_defs_ncl:                        0
% 2.32/1.02  bin_hyper_res:                          9
% 2.32/1.02  prep_cycles:                            4
% 2.32/1.02  pred_elim_time:                         0.01
% 2.32/1.02  splitting_time:                         0.
% 2.32/1.02  sem_filter_time:                        0.
% 2.32/1.02  monotx_time:                            0.
% 2.32/1.02  subtype_inf_time:                       0.
% 2.32/1.02  
% 2.32/1.02  ------ Problem properties
% 2.32/1.02  
% 2.32/1.02  clauses:                                28
% 2.32/1.02  conjectures:                            3
% 2.32/1.02  epr:                                    3
% 2.32/1.02  horn:                                   22
% 2.32/1.02  ground:                                 6
% 2.32/1.02  unary:                                  7
% 2.32/1.02  binary:                                 7
% 2.32/1.02  lits:                                   69
% 2.32/1.02  lits_eq:                                24
% 2.32/1.02  fd_pure:                                0
% 2.32/1.02  fd_pseudo:                              0
% 2.32/1.02  fd_cond:                                3
% 2.32/1.02  fd_pseudo_cond:                         3
% 2.32/1.02  ac_symbols:                             0
% 2.32/1.02  
% 2.32/1.02  ------ Propositional Solver
% 2.32/1.02  
% 2.32/1.02  prop_solver_calls:                      27
% 2.32/1.02  prop_fast_solver_calls:                 1346
% 2.32/1.02  smt_solver_calls:                       0
% 2.32/1.02  smt_fast_solver_calls:                  0
% 2.32/1.02  prop_num_of_clauses:                    2933
% 2.32/1.02  prop_preprocess_simplified:             8160
% 2.32/1.02  prop_fo_subsumed:                       173
% 2.32/1.02  prop_solver_time:                       0.
% 2.32/1.02  smt_solver_time:                        0.
% 2.32/1.02  smt_fast_solver_time:                   0.
% 2.32/1.02  prop_fast_solver_time:                  0.
% 2.32/1.02  prop_unsat_core_time:                   0.
% 2.32/1.02  
% 2.32/1.02  ------ QBF
% 2.32/1.02  
% 2.32/1.02  qbf_q_res:                              0
% 2.32/1.02  qbf_num_tautologies:                    0
% 2.32/1.02  qbf_prep_cycles:                        0
% 2.32/1.02  
% 2.32/1.02  ------ BMC1
% 2.32/1.02  
% 2.32/1.02  bmc1_current_bound:                     -1
% 2.32/1.02  bmc1_last_solved_bound:                 -1
% 2.32/1.02  bmc1_unsat_core_size:                   -1
% 2.32/1.02  bmc1_unsat_core_parents_size:           -1
% 2.32/1.02  bmc1_merge_next_fun:                    0
% 2.32/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.02  
% 2.32/1.02  ------ Instantiation
% 2.32/1.02  
% 2.32/1.02  inst_num_of_clauses:                    691
% 2.32/1.02  inst_num_in_passive:                    307
% 2.32/1.02  inst_num_in_active:                     383
% 2.32/1.02  inst_num_in_unprocessed:                1
% 2.32/1.02  inst_num_of_loops:                      440
% 2.32/1.02  inst_num_of_learning_restarts:          0
% 2.32/1.02  inst_num_moves_active_passive:          54
% 2.32/1.02  inst_lit_activity:                      0
% 2.32/1.02  inst_lit_activity_moves:                0
% 2.32/1.02  inst_num_tautologies:                   0
% 2.32/1.02  inst_num_prop_implied:                  0
% 2.32/1.02  inst_num_existing_simplified:           0
% 2.32/1.02  inst_num_eq_res_simplified:             0
% 2.32/1.02  inst_num_child_elim:                    0
% 2.32/1.02  inst_num_of_dismatching_blockings:      507
% 2.32/1.02  inst_num_of_non_proper_insts:           699
% 2.32/1.02  inst_num_of_duplicates:                 0
% 2.32/1.02  inst_inst_num_from_inst_to_res:         0
% 2.32/1.02  inst_dismatching_checking_time:         0.
% 2.32/1.02  
% 2.32/1.02  ------ Resolution
% 2.32/1.02  
% 2.32/1.02  res_num_of_clauses:                     0
% 2.32/1.02  res_num_in_passive:                     0
% 2.32/1.02  res_num_in_active:                      0
% 2.32/1.02  res_num_of_loops:                       152
% 2.32/1.02  res_forward_subset_subsumed:            84
% 2.32/1.02  res_backward_subset_subsumed:           0
% 2.32/1.02  res_forward_subsumed:                   0
% 2.32/1.02  res_backward_subsumed:                  0
% 2.32/1.02  res_forward_subsumption_resolution:     0
% 2.32/1.02  res_backward_subsumption_resolution:    0
% 2.32/1.02  res_clause_to_clause_subsumption:       1086
% 2.32/1.02  res_orphan_elimination:                 0
% 2.32/1.02  res_tautology_del:                      33
% 2.32/1.02  res_num_eq_res_simplified:              0
% 2.32/1.02  res_num_sel_changes:                    0
% 2.32/1.02  res_moves_from_active_to_pass:          0
% 2.32/1.02  
% 2.32/1.02  ------ Superposition
% 2.32/1.02  
% 2.32/1.02  sup_time_total:                         0.
% 2.32/1.02  sup_time_generating:                    0.
% 2.32/1.02  sup_time_sim_full:                      0.
% 2.32/1.02  sup_time_sim_immed:                     0.
% 2.32/1.02  
% 2.32/1.02  sup_num_of_clauses:                     195
% 2.32/1.02  sup_num_in_active:                      81
% 2.32/1.02  sup_num_in_passive:                     114
% 2.32/1.02  sup_num_of_loops:                       87
% 2.32/1.02  sup_fw_superposition:                   205
% 2.32/1.02  sup_bw_superposition:                   139
% 2.32/1.02  sup_immediate_simplified:               70
% 2.32/1.02  sup_given_eliminated:                   0
% 2.32/1.02  comparisons_done:                       0
% 2.32/1.02  comparisons_avoided:                    15
% 2.32/1.02  
% 2.32/1.02  ------ Simplifications
% 2.32/1.02  
% 2.32/1.02  
% 2.32/1.02  sim_fw_subset_subsumed:                 46
% 2.32/1.02  sim_bw_subset_subsumed:                 0
% 2.32/1.02  sim_fw_subsumed:                        9
% 2.32/1.02  sim_bw_subsumed:                        13
% 2.32/1.02  sim_fw_subsumption_res:                 1
% 2.32/1.02  sim_bw_subsumption_res:                 0
% 2.32/1.02  sim_tautology_del:                      3
% 2.32/1.02  sim_eq_tautology_del:                   26
% 2.32/1.02  sim_eq_res_simp:                        0
% 2.32/1.02  sim_fw_demodulated:                     0
% 2.32/1.02  sim_bw_demodulated:                     6
% 2.32/1.02  sim_light_normalised:                   2
% 2.32/1.02  sim_joinable_taut:                      0
% 2.32/1.02  sim_joinable_simp:                      0
% 2.32/1.02  sim_ac_normalised:                      0
% 2.32/1.02  sim_smt_subsumption:                    0
% 2.32/1.02  
%------------------------------------------------------------------------------
