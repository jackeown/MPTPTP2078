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
% DateTime   : Thu Dec  3 12:07:47 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 937 expanded)
%              Number of clauses        :   97 ( 313 expanded)
%              Number of leaves         :   21 ( 200 expanded)
%              Depth                    :   23
%              Number of atoms          :  530 (4284 expanded)
%              Number of equality atoms :  173 ( 924 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ r2_hidden(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f31,f48,f47])).

fof(f73,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f45])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f68])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1626,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1629,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2749,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1626,c_1629])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1627,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3166,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2749,c_1627])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1632,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_407,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_408,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1622,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_27,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_409,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1863,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1864,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1863])).

cnf(c_1879,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | k1_funct_1(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1622,c_27,c_409,c_1864])).

cnf(c_1880,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1879])).

cnf(c_4161,plain,
    ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1880])).

cnf(c_4207,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4161,c_27,c_1864])).

cnf(c_4208,plain,
    ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4207])).

cnf(c_4219,plain,
    ( k1_funct_1(sK6,sK2(sK7,sK5,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_3166,c_4208])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_392,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_1623,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_394,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_1922,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1623,c_27,c_394,c_1864])).

cnf(c_1923,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_1922])).

cnf(c_4365,plain,
    ( r2_hidden(sK2(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_4219,c_1923])).

cnf(c_28,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1038,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2047,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1960,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2496,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k7_relset_1(sK3,sK4,sK6,sK5) = k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1960])).

cnf(c_1039,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2206,plain,
    ( X0 != X1
    | X0 = k7_relset_1(sK3,sK4,sK6,sK5)
    | k7_relset_1(sK3,sK4,sK6,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_2495,plain,
    ( X0 = k7_relset_1(sK3,sK4,sK6,sK5)
    | X0 != k9_relat_1(sK6,sK5)
    | k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_2206])).

cnf(c_2535,plain,
    ( k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5)
    | k9_relat_1(sK6,sK5) = k7_relset_1(sK3,sK4,sK6,sK5)
    | k9_relat_1(sK6,sK5) != k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_2495])).

cnf(c_2536,plain,
    ( k9_relat_1(sK6,sK5) = k9_relat_1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1040,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1902,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | X1 != k7_relset_1(sK3,sK4,sK6,sK5)
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_2046,plain,
    ( r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | X0 != k7_relset_1(sK3,sK4,sK6,sK5)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_2697,plain,
    ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | r2_hidden(sK7,k9_relat_1(sK6,sK5))
    | k9_relat_1(sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_2698,plain,
    ( k9_relat_1(sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
    | sK7 != sK7
    | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2697])).

cnf(c_4350,plain,
    ( r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6)
    | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4357,plain,
    ( r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4350])).

cnf(c_4483,plain,
    ( r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4365,c_24,c_27,c_28,c_1864,c_2047,c_2496,c_2535,c_2536,c_2698,c_4357])).

cnf(c_18,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_377,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_378,plain,
    ( r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_1624,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_379,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_1913,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1624,c_27,c_379,c_1864])).

cnf(c_1914,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_1913])).

cnf(c_4490,plain,
    ( r2_hidden(sK2(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_1914])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1640,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1637,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2302,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_1637])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1635,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3006,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_1635])).

cnf(c_7765,plain,
    ( m1_subset_1(sK2(sK7,sK5,sK6),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4490,c_3006])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1636,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8461,plain,
    ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
    | r2_hidden(sK2(sK7,sK5,sK6),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7765,c_1636])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1628,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4366,plain,
    ( r2_hidden(sK2(sK7,sK5,sK6),sK3) != iProver_top
    | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4219,c_1628])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4352,plain,
    ( r2_hidden(sK2(sK7,sK5,sK6),sK5)
    | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4353,plain,
    ( r2_hidden(sK2(sK7,sK5,sK6),sK5) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4352])).

cnf(c_4383,plain,
    ( r2_hidden(sK2(sK7,sK5,sK6),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4366,c_24,c_27,c_28,c_1864,c_2047,c_2496,c_2535,c_2536,c_2698,c_4353])).

cnf(c_14454,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8461,c_4383])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_11])).

cnf(c_360,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_19])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_1625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_2071,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1626,c_1625])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2988,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2302,c_1638])).

cnf(c_5983,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2071,c_2988])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1643,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4503,plain,
    ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4490,c_1643])).

cnf(c_1866,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | r1_tarski(k1_relat_1(sK6),sK3) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_1867,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1866])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14454,c_5983,c_4503,c_1867,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.26/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.50  
% 7.26/1.50  ------  iProver source info
% 7.26/1.50  
% 7.26/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.50  git: non_committed_changes: false
% 7.26/1.50  git: last_make_outside_of_git: false
% 7.26/1.50  
% 7.26/1.50  ------ 
% 7.26/1.50  ------ Parsing...
% 7.26/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.50  ------ Proving...
% 7.26/1.50  ------ Problem Properties 
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  clauses                                 23
% 7.26/1.50  conjectures                             3
% 7.26/1.50  EPR                                     3
% 7.26/1.50  Horn                                    20
% 7.26/1.50  unary                                   2
% 7.26/1.50  binary                                  8
% 7.26/1.50  lits                                    59
% 7.26/1.50  lits eq                                 5
% 7.26/1.50  fd_pure                                 0
% 7.26/1.50  fd_pseudo                               0
% 7.26/1.50  fd_cond                                 0
% 7.26/1.50  fd_pseudo_cond                          3
% 7.26/1.50  AC symbols                              0
% 7.26/1.50  
% 7.26/1.50  ------ Input Options Time Limit: Unbounded
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  ------ 
% 7.26/1.50  Current options:
% 7.26/1.50  ------ 
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  ------ Proving...
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  % SZS status Theorem for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  fof(f13,conjecture,(
% 7.26/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f14,negated_conjecture,(
% 7.26/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.26/1.50    inference(negated_conjecture,[],[f13])).
% 7.26/1.50  
% 7.26/1.50  fof(f15,plain,(
% 7.26/1.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.26/1.50    inference(pure_predicate_removal,[],[f14])).
% 7.26/1.50  
% 7.26/1.50  fof(f30,plain,(
% 7.26/1.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 7.26/1.50    inference(ennf_transformation,[],[f15])).
% 7.26/1.50  
% 7.26/1.50  fof(f31,plain,(
% 7.26/1.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 7.26/1.50    inference(flattening,[],[f30])).
% 7.26/1.50  
% 7.26/1.50  fof(f48,plain,(
% 7.26/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.26/1.50    introduced(choice_axiom,[])).
% 7.26/1.50  
% 7.26/1.50  fof(f47,plain,(
% 7.26/1.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6))),
% 7.26/1.50    introduced(choice_axiom,[])).
% 7.26/1.50  
% 7.26/1.50  fof(f49,plain,(
% 7.26/1.50    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)),
% 7.26/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f31,f48,f47])).
% 7.26/1.50  
% 7.26/1.50  fof(f73,plain,(
% 7.26/1.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 7.26/1.50    inference(cnf_transformation,[],[f49])).
% 7.26/1.50  
% 7.26/1.50  fof(f12,axiom,(
% 7.26/1.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f29,plain,(
% 7.26/1.50    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.50    inference(ennf_transformation,[],[f12])).
% 7.26/1.50  
% 7.26/1.50  fof(f71,plain,(
% 7.26/1.50    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f29])).
% 7.26/1.50  
% 7.26/1.50  fof(f74,plain,(
% 7.26/1.50    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 7.26/1.50    inference(cnf_transformation,[],[f49])).
% 7.26/1.50  
% 7.26/1.50  fof(f8,axiom,(
% 7.26/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f24,plain,(
% 7.26/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.26/1.50    inference(ennf_transformation,[],[f8])).
% 7.26/1.50  
% 7.26/1.50  fof(f41,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.26/1.50    inference(nnf_transformation,[],[f24])).
% 7.26/1.50  
% 7.26/1.50  fof(f42,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.26/1.50    inference(rectify,[],[f41])).
% 7.26/1.50  
% 7.26/1.50  fof(f43,plain,(
% 7.26/1.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 7.26/1.50    introduced(choice_axiom,[])).
% 7.26/1.50  
% 7.26/1.50  fof(f44,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.26/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 7.26/1.50  
% 7.26/1.50  fof(f63,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f44])).
% 7.26/1.50  
% 7.26/1.50  fof(f9,axiom,(
% 7.26/1.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f25,plain,(
% 7.26/1.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.26/1.50    inference(ennf_transformation,[],[f9])).
% 7.26/1.50  
% 7.26/1.50  fof(f26,plain,(
% 7.26/1.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.26/1.50    inference(flattening,[],[f25])).
% 7.26/1.50  
% 7.26/1.50  fof(f45,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.26/1.50    inference(nnf_transformation,[],[f26])).
% 7.26/1.50  
% 7.26/1.50  fof(f46,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.26/1.50    inference(flattening,[],[f45])).
% 7.26/1.50  
% 7.26/1.50  fof(f67,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f46])).
% 7.26/1.50  
% 7.26/1.50  fof(f72,plain,(
% 7.26/1.50    v1_funct_1(sK6)),
% 7.26/1.50    inference(cnf_transformation,[],[f49])).
% 7.26/1.50  
% 7.26/1.50  fof(f10,axiom,(
% 7.26/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f27,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.50    inference(ennf_transformation,[],[f10])).
% 7.26/1.50  
% 7.26/1.50  fof(f69,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f27])).
% 7.26/1.50  
% 7.26/1.50  fof(f68,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f46])).
% 7.26/1.50  
% 7.26/1.50  fof(f78,plain,(
% 7.26/1.50    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.26/1.50    inference(equality_resolution,[],[f68])).
% 7.26/1.50  
% 7.26/1.50  fof(f66,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f46])).
% 7.26/1.50  
% 7.26/1.50  fof(f2,axiom,(
% 7.26/1.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f36,plain,(
% 7.26/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.26/1.50    inference(nnf_transformation,[],[f2])).
% 7.26/1.50  
% 7.26/1.50  fof(f37,plain,(
% 7.26/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.26/1.50    inference(rectify,[],[f36])).
% 7.26/1.50  
% 7.26/1.50  fof(f38,plain,(
% 7.26/1.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.26/1.50    introduced(choice_axiom,[])).
% 7.26/1.50  
% 7.26/1.50  fof(f39,plain,(
% 7.26/1.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.26/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.26/1.50  
% 7.26/1.50  fof(f53,plain,(
% 7.26/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.26/1.50    inference(cnf_transformation,[],[f39])).
% 7.26/1.50  
% 7.26/1.50  fof(f76,plain,(
% 7.26/1.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.26/1.50    inference(equality_resolution,[],[f53])).
% 7.26/1.50  
% 7.26/1.50  fof(f4,axiom,(
% 7.26/1.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f18,plain,(
% 7.26/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.26/1.50    inference(ennf_transformation,[],[f4])).
% 7.26/1.50  
% 7.26/1.50  fof(f57,plain,(
% 7.26/1.50    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f18])).
% 7.26/1.50  
% 7.26/1.50  fof(f6,axiom,(
% 7.26/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f21,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.26/1.50    inference(ennf_transformation,[],[f6])).
% 7.26/1.50  
% 7.26/1.50  fof(f22,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.26/1.50    inference(flattening,[],[f21])).
% 7.26/1.50  
% 7.26/1.50  fof(f59,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f22])).
% 7.26/1.50  
% 7.26/1.50  fof(f5,axiom,(
% 7.26/1.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f19,plain,(
% 7.26/1.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.26/1.50    inference(ennf_transformation,[],[f5])).
% 7.26/1.50  
% 7.26/1.50  fof(f20,plain,(
% 7.26/1.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.26/1.50    inference(flattening,[],[f19])).
% 7.26/1.50  
% 7.26/1.50  fof(f58,plain,(
% 7.26/1.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f20])).
% 7.26/1.50  
% 7.26/1.50  fof(f75,plain,(
% 7.26/1.50    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f49])).
% 7.26/1.50  
% 7.26/1.50  fof(f64,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f44])).
% 7.26/1.50  
% 7.26/1.50  fof(f11,axiom,(
% 7.26/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f16,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.26/1.50    inference(pure_predicate_removal,[],[f11])).
% 7.26/1.50  
% 7.26/1.50  fof(f28,plain,(
% 7.26/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.50    inference(ennf_transformation,[],[f16])).
% 7.26/1.50  
% 7.26/1.50  fof(f70,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f28])).
% 7.26/1.50  
% 7.26/1.50  fof(f7,axiom,(
% 7.26/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f23,plain,(
% 7.26/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.26/1.50    inference(ennf_transformation,[],[f7])).
% 7.26/1.50  
% 7.26/1.50  fof(f40,plain,(
% 7.26/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.26/1.50    inference(nnf_transformation,[],[f23])).
% 7.26/1.50  
% 7.26/1.50  fof(f60,plain,(
% 7.26/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f40])).
% 7.26/1.50  
% 7.26/1.50  fof(f3,axiom,(
% 7.26/1.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f17,plain,(
% 7.26/1.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.26/1.50    inference(ennf_transformation,[],[f3])).
% 7.26/1.50  
% 7.26/1.50  fof(f56,plain,(
% 7.26/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f17])).
% 7.26/1.50  
% 7.26/1.50  fof(f1,axiom,(
% 7.26/1.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.26/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f32,plain,(
% 7.26/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.50    inference(nnf_transformation,[],[f1])).
% 7.26/1.50  
% 7.26/1.50  fof(f33,plain,(
% 7.26/1.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.50    inference(rectify,[],[f32])).
% 7.26/1.50  
% 7.26/1.50  fof(f34,plain,(
% 7.26/1.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.26/1.50    introduced(choice_axiom,[])).
% 7.26/1.50  
% 7.26/1.50  fof(f35,plain,(
% 7.26/1.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 7.26/1.50  
% 7.26/1.50  fof(f50,plain,(
% 7.26/1.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f35])).
% 7.26/1.50  
% 7.26/1.50  cnf(c_24,negated_conjecture,
% 7.26/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 7.26/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1626,plain,
% 7.26/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_21,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.26/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1629,plain,
% 7.26/1.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.26/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2749,plain,
% 7.26/1.50      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_1626,c_1629]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_23,negated_conjecture,
% 7.26/1.50      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 7.26/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1627,plain,
% 7.26/1.50      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3166,plain,
% 7.26/1.50      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_2749,c_1627]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_14,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.26/1.50      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1)
% 7.26/1.50      | ~ v1_relat_1(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1632,plain,
% 7.26/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(sK2(X0,X2,X1),X0),X1) = iProver_top
% 7.26/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_17,plain,
% 7.26/1.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.26/1.50      | ~ v1_funct_1(X2)
% 7.26/1.50      | ~ v1_relat_1(X2)
% 7.26/1.50      | k1_funct_1(X2,X0) = X1 ),
% 7.26/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_25,negated_conjecture,
% 7.26/1.50      ( v1_funct_1(sK6) ),
% 7.26/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_407,plain,
% 7.26/1.50      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 7.26/1.50      | ~ v1_relat_1(X2)
% 7.26/1.50      | k1_funct_1(X2,X0) = X1
% 7.26/1.50      | sK6 != X2 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_408,plain,
% 7.26/1.50      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 7.26/1.50      | ~ v1_relat_1(sK6)
% 7.26/1.50      | k1_funct_1(sK6,X0) = X1 ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_407]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1622,plain,
% 7.26/1.50      ( k1_funct_1(sK6,X0) = X1
% 7.26/1.50      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_27,plain,
% 7.26/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_409,plain,
% 7.26/1.50      ( k1_funct_1(sK6,X0) = X1
% 7.26/1.50      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_19,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | v1_relat_1(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1863,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.26/1.50      | v1_relat_1(sK6) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_19]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1864,plain,
% 7.26/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_1863]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1879,plain,
% 7.26/1.50      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 7.26/1.50      | k1_funct_1(sK6,X0) = X1 ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_1622,c_27,c_409,c_1864]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1880,plain,
% 7.26/1.50      ( k1_funct_1(sK6,X0) = X1
% 7.26/1.50      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 7.26/1.50      inference(renaming,[status(thm)],[c_1879]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4161,plain,
% 7.26/1.50      ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
% 7.26/1.50      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_1632,c_1880]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4207,plain,
% 7.26/1.50      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 7.26/1.50      | k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0 ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_4161,c_27,c_1864]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4208,plain,
% 7.26/1.50      ( k1_funct_1(sK6,sK2(X0,X1,sK6)) = X0
% 7.26/1.50      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 7.26/1.50      inference(renaming,[status(thm)],[c_4207]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4219,plain,
% 7.26/1.50      ( k1_funct_1(sK6,sK2(sK7,sK5,sK6)) = sK7 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_3166,c_4208]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_16,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.26/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.26/1.50      | ~ v1_funct_1(X1)
% 7.26/1.50      | ~ v1_relat_1(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_392,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.26/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 7.26/1.50      | ~ v1_relat_1(X1)
% 7.26/1.50      | sK6 != X1 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_393,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 7.26/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 7.26/1.50      | ~ v1_relat_1(sK6) ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_392]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1623,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_394,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1922,plain,
% 7.26/1.50      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 7.26/1.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_1623,c_27,c_394,c_1864]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1923,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top ),
% 7.26/1.50      inference(renaming,[status(thm)],[c_1922]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4365,plain,
% 7.26/1.50      ( r2_hidden(sK2(sK7,sK5,sK6),k1_relat_1(sK6)) != iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4219,c_1923]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_28,plain,
% 7.26/1.50      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1038,plain,( X0 = X0 ),theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2047,plain,
% 7.26/1.50      ( sK7 = sK7 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_1038]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1960,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.26/1.50      | k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_21]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2496,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.26/1.50      | k7_relset_1(sK3,sK4,sK6,sK5) = k9_relat_1(sK6,sK5) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_1960]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1039,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2206,plain,
% 7.26/1.50      ( X0 != X1
% 7.26/1.50      | X0 = k7_relset_1(sK3,sK4,sK6,sK5)
% 7.26/1.50      | k7_relset_1(sK3,sK4,sK6,sK5) != X1 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_1039]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2495,plain,
% 7.26/1.50      ( X0 = k7_relset_1(sK3,sK4,sK6,sK5)
% 7.26/1.50      | X0 != k9_relat_1(sK6,sK5)
% 7.26/1.50      | k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_2206]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2535,plain,
% 7.26/1.50      ( k7_relset_1(sK3,sK4,sK6,sK5) != k9_relat_1(sK6,sK5)
% 7.26/1.50      | k9_relat_1(sK6,sK5) = k7_relset_1(sK3,sK4,sK6,sK5)
% 7.26/1.50      | k9_relat_1(sK6,sK5) != k9_relat_1(sK6,sK5) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_2495]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2536,plain,
% 7.26/1.50      ( k9_relat_1(sK6,sK5) = k9_relat_1(sK6,sK5) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_1038]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1040,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.26/1.50      theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1902,plain,
% 7.26/1.50      ( r2_hidden(X0,X1)
% 7.26/1.50      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 7.26/1.50      | X1 != k7_relset_1(sK3,sK4,sK6,sK5)
% 7.26/1.50      | X0 != sK7 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_1040]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2046,plain,
% 7.26/1.50      ( r2_hidden(sK7,X0)
% 7.26/1.50      | ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 7.26/1.50      | X0 != k7_relset_1(sK3,sK4,sK6,sK5)
% 7.26/1.50      | sK7 != sK7 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_1902]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2697,plain,
% 7.26/1.50      ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 7.26/1.50      | r2_hidden(sK7,k9_relat_1(sK6,sK5))
% 7.26/1.50      | k9_relat_1(sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
% 7.26/1.50      | sK7 != sK7 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_2046]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2698,plain,
% 7.26/1.50      ( k9_relat_1(sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
% 7.26/1.50      | sK7 != sK7
% 7.26/1.50      | r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) != iProver_top
% 7.26/1.50      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_2697]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4350,plain,
% 7.26/1.50      ( r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6)
% 7.26/1.50      | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
% 7.26/1.50      | ~ v1_relat_1(sK6) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4357,plain,
% 7.26/1.50      ( r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6) = iProver_top
% 7.26/1.50      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_4350]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4483,plain,
% 7.26/1.50      ( r2_hidden(k4_tarski(sK2(sK7,sK5,sK6),sK7),sK6) = iProver_top ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_4365,c_24,c_27,c_28,c_1864,c_2047,c_2496,c_2535,
% 7.26/1.50                 c_2536,c_2698,c_4357]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(X1))
% 7.26/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.26/1.50      | ~ v1_funct_1(X1)
% 7.26/1.50      | ~ v1_relat_1(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_377,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(X1))
% 7.26/1.50      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 7.26/1.50      | ~ v1_relat_1(X1)
% 7.26/1.50      | sK6 != X1 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_378,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(sK6))
% 7.26/1.50      | ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 7.26/1.50      | ~ v1_relat_1(sK6) ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_377]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1624,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_379,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1913,plain,
% 7.26/1.50      ( r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 7.26/1.50      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_1624,c_27,c_379,c_1864]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1914,plain,
% 7.26/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) = iProver_top
% 7.26/1.50      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top ),
% 7.26/1.50      inference(renaming,[status(thm)],[c_1913]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4490,plain,
% 7.26/1.50      ( r2_hidden(sK2(sK7,sK5,sK6),k1_relat_1(sK6)) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4483,c_1914]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4,plain,
% 7.26/1.50      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.26/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1640,plain,
% 7.26/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.50      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_7,plain,
% 7.26/1.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1637,plain,
% 7.26/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.26/1.50      | r2_hidden(X0,X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2302,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.26/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_1640,c_1637]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_9,plain,
% 7.26/1.50      ( m1_subset_1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.26/1.50      | ~ r2_hidden(X0,X2) ),
% 7.26/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1635,plain,
% 7.26/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.26/1.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.50      | r2_hidden(X0,X2) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3006,plain,
% 7.26/1.50      ( m1_subset_1(X0,X1) = iProver_top
% 7.26/1.50      | r1_tarski(X2,X1) != iProver_top
% 7.26/1.50      | r2_hidden(X0,X2) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_2302,c_1635]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_7765,plain,
% 7.26/1.50      ( m1_subset_1(sK2(sK7,sK5,sK6),X0) = iProver_top
% 7.26/1.50      | r1_tarski(k1_relat_1(sK6),X0) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4490,c_3006]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_8,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1636,plain,
% 7.26/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.26/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.26/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_8461,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(sK6),X0) != iProver_top
% 7.26/1.50      | r2_hidden(sK2(sK7,sK5,sK6),X0) = iProver_top
% 7.26/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_7765,c_1636]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_22,negated_conjecture,
% 7.26/1.50      ( ~ r2_hidden(X0,sK3)
% 7.26/1.50      | ~ r2_hidden(X0,sK5)
% 7.26/1.50      | k1_funct_1(sK6,X0) != sK7 ),
% 7.26/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1628,plain,
% 7.26/1.50      ( k1_funct_1(sK6,X0) != sK7
% 7.26/1.50      | r2_hidden(X0,sK3) != iProver_top
% 7.26/1.50      | r2_hidden(X0,sK5) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4366,plain,
% 7.26/1.50      ( r2_hidden(sK2(sK7,sK5,sK6),sK3) != iProver_top
% 7.26/1.50      | r2_hidden(sK2(sK7,sK5,sK6),sK5) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4219,c_1628]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_13,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.26/1.50      | r2_hidden(sK2(X0,X2,X1),X2)
% 7.26/1.50      | ~ v1_relat_1(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4352,plain,
% 7.26/1.50      ( r2_hidden(sK2(sK7,sK5,sK6),sK5)
% 7.26/1.50      | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
% 7.26/1.50      | ~ v1_relat_1(sK6) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4353,plain,
% 7.26/1.50      ( r2_hidden(sK2(sK7,sK5,sK6),sK5) = iProver_top
% 7.26/1.50      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_4352]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4383,plain,
% 7.26/1.50      ( r2_hidden(sK2(sK7,sK5,sK6),sK3) != iProver_top ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_4366,c_24,c_27,c_28,c_1864,c_2047,c_2496,c_2535,
% 7.26/1.50                 c_2536,c_2698,c_4353]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_14454,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(sK6),sK3) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_8461,c_4383]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_20,plain,
% 7.26/1.50      ( v4_relat_1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.26/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_11,plain,
% 7.26/1.50      ( ~ v4_relat_1(X0,X1)
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.26/1.50      | ~ v1_relat_1(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_356,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.26/1.50      | ~ v1_relat_1(X0) ),
% 7.26/1.50      inference(resolution,[status(thm)],[c_20,c_11]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_360,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(X0),X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_356,c_19]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_361,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.26/1.50      inference(renaming,[status(thm)],[c_360]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1625,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2071,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_1626,c_1625]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.50      | ~ v1_xboole_0(X1)
% 7.26/1.50      | v1_xboole_0(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1638,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.26/1.50      | v1_xboole_0(X1) != iProver_top
% 7.26/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2988,plain,
% 7.26/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.50      | v1_xboole_0(X1) != iProver_top
% 7.26/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_2302,c_1638]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5983,plain,
% 7.26/1.50      ( v1_xboole_0(k1_relat_1(sK6)) = iProver_top
% 7.26/1.50      | v1_xboole_0(sK3) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_2071,c_2988]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1643,plain,
% 7.26/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.26/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4503,plain,
% 7.26/1.50      ( v1_xboole_0(k1_relat_1(sK6)) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4490,c_1643]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1866,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 7.26/1.50      | r1_tarski(k1_relat_1(sK6),sK3) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_361]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1867,plain,
% 7.26/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 7.26/1.50      | r1_tarski(k1_relat_1(sK6),sK3) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_1866]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(contradiction,plain,
% 7.26/1.50      ( $false ),
% 7.26/1.50      inference(minisat,[status(thm)],[c_14454,c_5983,c_4503,c_1867,c_27]) ).
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  ------                               Statistics
% 7.26/1.50  
% 7.26/1.50  ------ Selected
% 7.26/1.50  
% 7.26/1.50  total_time:                             0.584
% 7.26/1.50  
%------------------------------------------------------------------------------
