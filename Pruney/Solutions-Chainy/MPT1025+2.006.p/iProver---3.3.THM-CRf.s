%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:01 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  186 (1434 expanded)
%              Number of clauses        :  114 ( 461 expanded)
%              Number of leaves         :   19 ( 304 expanded)
%              Depth                    :   22
%              Number of atoms          :  678 (6689 expanded)
%              Number of equality atoms :  246 (1384 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK9
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK8,X5) != X4
              | ~ r2_hidden(X5,sK7)
              | ~ m1_subset_1(X5,sK5) )
          & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ m1_subset_1(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f28,f49,f48])).

fof(f74,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f46,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK4(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK4(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK4(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK4(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f50])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ m1_subset_1(X5,sK5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK3(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1229,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1239,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2178,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1229,c_1239])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1250,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1233,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2288,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
    | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1250,c_1233])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1248,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2395,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1241,c_1248])).

cnf(c_8294,plain,
    ( r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2288,c_2395])).

cnf(c_8295,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
    | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8294])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_325,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_326,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_1226,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_27,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_327,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1523,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1524,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1523])).

cnf(c_1539,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | k1_funct_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1226,c_27,c_327,c_1524])).

cnf(c_1540,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_1539])).

cnf(c_8318,plain,
    ( k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
    | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8295,c_1540])).

cnf(c_9372,plain,
    ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0)))) = sK0(k7_relset_1(sK5,sK6,sK8,X0))
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2178,c_8318])).

cnf(c_9379,plain,
    ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0)))) = sK0(k9_relat_1(sK8,X0))
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9372,c_2178])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1492,plain,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | ~ v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1493,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_1638,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1800,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1638])).

cnf(c_1802,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1800])).

cnf(c_1568,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1801,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_1804,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1703,plain,
    ( m1_subset_1(X0,sK6)
    | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
    | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1915,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | m1_subset_1(sK9,sK6)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_1916,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_1230,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK4(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1232,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1742,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1232])).

cnf(c_2083,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_27,c_28,c_1493,c_1802,c_1804,c_1916])).

cnf(c_2269,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2178,c_1230])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2711,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2712,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2711])).

cnf(c_2289,plain,
    ( m1_subset_1(X0,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X1,sK5,sK8,X0),X0),sK8) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2178,c_1233])).

cnf(c_2394,plain,
    ( m1_subset_1(k9_relat_1(sK8,X0),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2178,c_1241])).

cnf(c_2850,plain,
    ( m1_subset_1(k9_relat_1(sK8,X0),k1_zfmisc_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2394,c_27])).

cnf(c_1247,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2858,plain,
    ( m1_subset_1(X0,sK6) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_1247])).

cnf(c_3059,plain,
    ( v1_xboole_0(X1) = iProver_top
    | r2_hidden(k4_tarski(sK4(X1,sK5,sK8,X0),X0),sK8) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2289,c_27,c_28,c_1493,c_1802,c_1804,c_2858])).

cnf(c_3060,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X1,sK5,sK8,X0),X0),sK8) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(renaming,[status(thm)],[c_3059])).

cnf(c_3071,plain,
    ( k1_funct_1(sK8,sK4(X0,sK5,sK8,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3060,c_1540])).

cnf(c_3110,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_3071])).

cnf(c_3433,plain,
    ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3434,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3433])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK4(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_5040,plain,
    ( ~ m1_subset_1(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5041,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5040])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_9642,plain,
    ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
    | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_9643,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
    | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9642])).

cnf(c_9674,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9379,c_27,c_28,c_1493,c_1524,c_1802,c_1804,c_1916,c_2083,c_2269,c_2712,c_3110,c_3434,c_5041,c_9643])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1236,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2605,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1236])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1240,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1814,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1229,c_1240])).

cnf(c_2608,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2605,c_1814])).

cnf(c_1249,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2963,plain,
    ( k1_relat_1(sK8) = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2608,c_1249])).

cnf(c_9679,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_9674,c_2963])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1244,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3514,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1540])).

cnf(c_3798,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3514,c_27,c_1524])).

cnf(c_3799,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3798])).

cnf(c_3809,plain,
    ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_2269,c_3799])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_310,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_1227,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1556,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_24,c_1523])).

cnf(c_1557,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
    inference(renaming,[status(thm)],[c_1556])).

cnf(c_1558,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1557])).

cnf(c_1601,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1227,c_1558])).

cnf(c_1602,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_1601])).

cnf(c_3910,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_3809,c_1602])).

cnf(c_2709,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2716,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2709])).

cnf(c_4011,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3910,c_27,c_1524,c_2269,c_2716])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_295,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_296,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_1228,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_297,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_1592,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1228,c_27,c_297,c_1524])).

cnf(c_1593,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_1592])).

cnf(c_4017,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4011,c_1593])).

cnf(c_4027,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4017,c_1249])).

cnf(c_9863,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9679,c_4027])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9863,c_9674])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.30/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.30/1.00  
% 3.30/1.00  ------  iProver source info
% 3.30/1.00  
% 3.30/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.30/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.30/1.00  git: non_committed_changes: false
% 3.30/1.00  git: last_make_outside_of_git: false
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  ------ Parsing...
% 3.30/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.30/1.00  
% 3.30/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.30/1.00  ------ Proving...
% 3.30/1.00  ------ Problem Properties 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  clauses                                 25
% 3.30/1.00  conjectures                             3
% 3.30/1.00  EPR                                     1
% 3.30/1.00  Horn                                    19
% 3.30/1.00  unary                                   2
% 3.30/1.00  binary                                  6
% 3.30/1.00  lits                                    86
% 3.30/1.00  lits eq                                 7
% 3.30/1.00  fd_pure                                 0
% 3.30/1.00  fd_pseudo                               0
% 3.30/1.00  fd_cond                                 0
% 3.30/1.00  fd_pseudo_cond                          1
% 3.30/1.00  AC symbols                              0
% 3.30/1.00  
% 3.30/1.00  ------ Input Options Time Limit: Unbounded
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ 
% 3.30/1.00  Current options:
% 3.30/1.00  ------ 
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  ------ Proving...
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS status Theorem for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  fof(f12,conjecture,(
% 3.30/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f13,negated_conjecture,(
% 3.30/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.30/1.00    inference(negated_conjecture,[],[f12])).
% 3.30/1.00  
% 3.30/1.00  fof(f14,plain,(
% 3.30/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.30/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.30/1.00  
% 3.30/1.00  fof(f27,plain,(
% 3.30/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.30/1.00    inference(ennf_transformation,[],[f14])).
% 3.30/1.00  
% 3.30/1.00  fof(f28,plain,(
% 3.30/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.30/1.00    inference(flattening,[],[f27])).
% 3.30/1.00  
% 3.30/1.00  fof(f49,plain,(
% 3.30/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f48,plain,(
% 3.30/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f50,plain,(
% 3.30/1.00    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8)),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f28,f49,f48])).
% 3.30/1.00  
% 3.30/1.00  fof(f74,plain,(
% 3.30/1.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.30/1.00    inference(cnf_transformation,[],[f50])).
% 3.30/1.00  
% 3.30/1.00  fof(f9,axiom,(
% 3.30/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f24,plain,(
% 3.30/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/1.00    inference(ennf_transformation,[],[f9])).
% 3.30/1.00  
% 3.30/1.00  fof(f65,plain,(
% 3.30/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f24])).
% 3.30/1.00  
% 3.30/1.00  fof(f1,axiom,(
% 3.30/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f29,plain,(
% 3.30/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.30/1.00    inference(nnf_transformation,[],[f1])).
% 3.30/1.00  
% 3.30/1.00  fof(f30,plain,(
% 3.30/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.30/1.00    inference(rectify,[],[f29])).
% 3.30/1.00  
% 3.30/1.00  fof(f31,plain,(
% 3.30/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f32,plain,(
% 3.30/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.30/1.00  
% 3.30/1.00  fof(f52,plain,(
% 3.30/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f32])).
% 3.30/1.00  
% 3.30/1.00  fof(f11,axiom,(
% 3.30/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f26,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f11])).
% 3.30/1.00  
% 3.30/1.00  fof(f44,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.30/1.00    inference(nnf_transformation,[],[f26])).
% 3.30/1.00  
% 3.30/1.00  fof(f45,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.30/1.00    inference(rectify,[],[f44])).
% 3.30/1.00  
% 3.30/1.00  fof(f46,plain,(
% 3.30/1.00    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f47,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 3.30/1.00  
% 3.30/1.00  fof(f70,plain,(
% 3.30/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f47])).
% 3.30/1.00  
% 3.30/1.00  fof(f7,axiom,(
% 3.30/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f22,plain,(
% 3.30/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/1.00    inference(ennf_transformation,[],[f7])).
% 3.30/1.00  
% 3.30/1.00  fof(f63,plain,(
% 3.30/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f22])).
% 3.30/1.00  
% 3.30/1.00  fof(f2,axiom,(
% 3.30/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f15,plain,(
% 3.30/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.30/1.00    inference(ennf_transformation,[],[f2])).
% 3.30/1.00  
% 3.30/1.00  fof(f53,plain,(
% 3.30/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f15])).
% 3.30/1.00  
% 3.30/1.00  fof(f5,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f19,plain,(
% 3.30/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.30/1.00    inference(ennf_transformation,[],[f5])).
% 3.30/1.00  
% 3.30/1.00  fof(f20,plain,(
% 3.30/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(flattening,[],[f19])).
% 3.30/1.00  
% 3.30/1.00  fof(f37,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(nnf_transformation,[],[f20])).
% 3.30/1.00  
% 3.30/1.00  fof(f38,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(flattening,[],[f37])).
% 3.30/1.00  
% 3.30/1.00  fof(f60,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f38])).
% 3.30/1.00  
% 3.30/1.00  fof(f73,plain,(
% 3.30/1.00    v1_funct_1(sK8)),
% 3.30/1.00    inference(cnf_transformation,[],[f50])).
% 3.30/1.00  
% 3.30/1.00  fof(f6,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f21,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/1.00    inference(ennf_transformation,[],[f6])).
% 3.30/1.00  
% 3.30/1.00  fof(f62,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f21])).
% 3.30/1.00  
% 3.30/1.00  fof(f75,plain,(
% 3.30/1.00    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.30/1.00    inference(cnf_transformation,[],[f50])).
% 3.30/1.00  
% 3.30/1.00  fof(f51,plain,(
% 3.30/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f32])).
% 3.30/1.00  
% 3.30/1.00  fof(f3,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f16,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.30/1.00    inference(ennf_transformation,[],[f3])).
% 3.30/1.00  
% 3.30/1.00  fof(f17,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.30/1.00    inference(flattening,[],[f16])).
% 3.30/1.00  
% 3.30/1.00  fof(f54,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f17])).
% 3.30/1.00  
% 3.30/1.00  fof(f69,plain,(
% 3.30/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f47])).
% 3.30/1.00  
% 3.30/1.00  fof(f4,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f18,plain,(
% 3.30/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(ennf_transformation,[],[f4])).
% 3.30/1.00  
% 3.30/1.00  fof(f33,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(nnf_transformation,[],[f18])).
% 3.30/1.00  
% 3.30/1.00  fof(f34,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(rectify,[],[f33])).
% 3.30/1.00  
% 3.30/1.00  fof(f35,plain,(
% 3.30/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f36,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 3.30/1.00  
% 3.30/1.00  fof(f57,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f36])).
% 3.30/1.00  
% 3.30/1.00  fof(f71,plain,(
% 3.30/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f47])).
% 3.30/1.00  
% 3.30/1.00  fof(f76,plain,(
% 3.30/1.00    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f50])).
% 3.30/1.00  
% 3.30/1.00  fof(f10,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f25,plain,(
% 3.30/1.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.30/1.00    inference(ennf_transformation,[],[f10])).
% 3.30/1.00  
% 3.30/1.00  fof(f39,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.30/1.00    inference(nnf_transformation,[],[f25])).
% 3.30/1.00  
% 3.30/1.00  fof(f40,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.30/1.00    inference(rectify,[],[f39])).
% 3.30/1.00  
% 3.30/1.00  fof(f42,plain,(
% 3.30/1.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f41,plain,(
% 3.30/1.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 3.30/1.00    introduced(choice_axiom,[])).
% 3.30/1.00  
% 3.30/1.00  fof(f43,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.30/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 3.30/1.00  
% 3.30/1.00  fof(f66,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK3(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f43])).
% 3.30/1.00  
% 3.30/1.00  fof(f8,axiom,(
% 3.30/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.30/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.30/1.00  
% 3.30/1.00  fof(f23,plain,(
% 3.30/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.30/1.00    inference(ennf_transformation,[],[f8])).
% 3.30/1.00  
% 3.30/1.00  fof(f64,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.30/1.00    inference(cnf_transformation,[],[f23])).
% 3.30/1.00  
% 3.30/1.00  fof(f56,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f36])).
% 3.30/1.00  
% 3.30/1.00  fof(f61,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f38])).
% 3.30/1.00  
% 3.30/1.00  fof(f77,plain,(
% 3.30/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.30/1.00    inference(equality_resolution,[],[f61])).
% 3.30/1.00  
% 3.30/1.00  fof(f59,plain,(
% 3.30/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.30/1.00    inference(cnf_transformation,[],[f38])).
% 3.30/1.00  
% 3.30/1.00  cnf(c_24,negated_conjecture,
% 3.30/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.30/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1229,plain,
% 3.30/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_14,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.30/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1239,plain,
% 3.30/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2178,plain,
% 3.30/1.00      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1229,c_1239]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_0,plain,
% 3.30/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1250,plain,
% 3.30/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.30/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_20,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.30/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.30/1.00      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
% 3.30/1.00      | v1_xboole_0(X1)
% 3.30/1.00      | v1_xboole_0(X3)
% 3.30/1.00      | v1_xboole_0(X4) ),
% 3.30/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1233,plain,
% 3.30/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.30/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(X3) = iProver_top
% 3.30/1.00      | v1_xboole_0(X4) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2288,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
% 3.30/1.00      | v1_xboole_0(X2) = iProver_top
% 3.30/1.00      | v1_xboole_0(X3) = iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1250,c_1233]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_12,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1241,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.30/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.30/1.00      | ~ v1_xboole_0(X1)
% 3.30/1.00      | v1_xboole_0(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1248,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.30/1.00      | v1_xboole_0(X1) != iProver_top
% 3.30/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2395,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.30/1.00      | v1_xboole_0(X2) != iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1241,c_1248]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8294,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
% 3.30/1.00      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.30/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.30/1.00      | v1_xboole_0(X3) = iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2288,c_2395]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8295,plain,
% 3.30/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(X3) = iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_8294]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9,plain,
% 3.30/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.30/1.00      | ~ v1_funct_1(X2)
% 3.30/1.00      | ~ v1_relat_1(X2)
% 3.30/1.00      | k1_funct_1(X2,X0) = X1 ),
% 3.30/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_25,negated_conjecture,
% 3.30/1.00      ( v1_funct_1(sK8) ),
% 3.30/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_325,plain,
% 3.30/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.30/1.00      | ~ v1_relat_1(X2)
% 3.30/1.00      | k1_funct_1(X2,X0) = X1
% 3.30/1.00      | sK8 != X2 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_326,plain,
% 3.30/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.30/1.00      | ~ v1_relat_1(sK8)
% 3.30/1.00      | k1_funct_1(sK8,X0) = X1 ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_325]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1226,plain,
% 3.30/1.00      ( k1_funct_1(sK8,X0) = X1
% 3.30/1.00      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_27,plain,
% 3.30/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_327,plain,
% 3.30/1.00      ( k1_funct_1(sK8,X0) = X1
% 3.30/1.00      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_11,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/1.00      | v1_relat_1(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1523,plain,
% 3.30/1.00      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.30/1.00      | v1_relat_1(sK8) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1524,plain,
% 3.30/1.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1523]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1539,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.30/1.00      | k1_funct_1(sK8,X0) = X1 ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1226,c_27,c_327,c_1524]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1540,plain,
% 3.30/1.00      ( k1_funct_1(sK8,X0) = X1
% 3.30/1.00      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_1539]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8318,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
% 3.30/1.00      | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(X0) = iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_8295,c_1540]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9372,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0)))) = sK0(k7_relset_1(sK5,sK6,sK8,X0))
% 3.30/1.00      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.30/1.00      | v1_xboole_0(X0) = iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2178,c_8318]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9379,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0)))) = sK0(k9_relat_1(sK8,X0))
% 3.30/1.00      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.30/1.00      | v1_xboole_0(X0) = iProver_top
% 3.30/1.00      | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.30/1.00      inference(light_normalisation,[status(thm)],[c_9372,c_2178]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_23,negated_conjecture,
% 3.30/1.00      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.30/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_28,plain,
% 3.30/1.00      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1,plain,
% 3.30/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1492,plain,
% 3.30/1.00      ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.30/1.00      | ~ v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1493,plain,
% 3.30/1.00      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1638,plain,
% 3.30/1.00      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(X0))
% 3.30/1.00      | ~ v1_xboole_0(X0)
% 3.30/1.00      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1800,plain,
% 3.30/1.00      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.30/1.00      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
% 3.30/1.00      | ~ v1_xboole_0(sK6) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1638]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1802,plain,
% 3.30/1.00      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 3.30/1.00      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1800]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1568,plain,
% 3.30/1.00      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
% 3.30/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1801,plain,
% 3.30/1.00      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.30/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1568]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1804,plain,
% 3.30/1.00      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3,plain,
% 3.30/1.00      ( m1_subset_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.30/1.00      | ~ r2_hidden(X0,X2) ),
% 3.30/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1703,plain,
% 3.30/1.00      ( m1_subset_1(X0,sK6)
% 3.30/1.00      | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
% 3.30/1.00      | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1915,plain,
% 3.30/1.00      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.30/1.00      | m1_subset_1(sK9,sK6)
% 3.30/1.00      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1703]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1916,plain,
% 3.30/1.00      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 3.30/1.00      | m1_subset_1(sK9,sK6) = iProver_top
% 3.30/1.00      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1230,plain,
% 3.30/1.00      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_21,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.30/1.00      | m1_subset_1(sK4(X4,X3,X2,X0),X3)
% 3.30/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.30/1.00      | v1_xboole_0(X1)
% 3.30/1.00      | v1_xboole_0(X3)
% 3.30/1.00      | v1_xboole_0(X4) ),
% 3.30/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1232,plain,
% 3.30/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.30/1.00      | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
% 3.30/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(X3) = iProver_top
% 3.30/1.00      | v1_xboole_0(X4) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1742,plain,
% 3.30/1.00      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.30/1.00      | m1_subset_1(sK9,sK6) != iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.30/1.00      | v1_xboole_0(sK6) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK7) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1230,c_1232]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2083,plain,
% 3.30/1.00      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK7) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1742,c_27,c_28,c_1493,c_1802,c_1804,c_1916]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2269,plain,
% 3.30/1.00      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_2178,c_1230]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_5,plain,
% 3.30/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.30/1.00      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.30/1.00      | ~ v1_relat_1(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2711,plain,
% 3.30/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
% 3.30/1.00      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.30/1.00      | ~ v1_relat_1(sK8) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2712,plain,
% 3.30/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
% 3.30/1.00      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2711]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2289,plain,
% 3.30/1.00      ( m1_subset_1(X0,sK6) != iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.30/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK4(X1,sK5,sK8,X0),X0),sK8) = iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK6) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2178,c_1233]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2394,plain,
% 3.30/1.00      ( m1_subset_1(k9_relat_1(sK8,X0),k1_zfmisc_1(sK6)) = iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2178,c_1241]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2850,plain,
% 3.30/1.00      ( m1_subset_1(k9_relat_1(sK8,X0),k1_zfmisc_1(sK6)) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2394,c_27]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1247,plain,
% 3.30/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.30/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2858,plain,
% 3.30/1.00      ( m1_subset_1(X0,sK6) = iProver_top
% 3.30/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2850,c_1247]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3059,plain,
% 3.30/1.00      ( v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK4(X1,sK5,sK8,X0),X0),sK8) = iProver_top
% 3.30/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_2289,c_27,c_28,c_1493,c_1802,c_1804,c_2858]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3060,plain,
% 3.30/1.00      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK4(X1,sK5,sK8,X0),X0),sK8) = iProver_top
% 3.30/1.00      | v1_xboole_0(X1) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_3059]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3071,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK4(X0,sK5,sK8,X1)) = X1
% 3.30/1.00      | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top
% 3.30/1.00      | v1_xboole_0(X0) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_3060,c_1540]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3110,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK7) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2269,c_3071]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3433,plain,
% 3.30/1.00      ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7) | ~ v1_xboole_0(sK7) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3434,plain,
% 3.30/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
% 3.30/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_3433]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_19,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,X1)
% 3.30/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.30/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.30/1.00      | r2_hidden(sK4(X4,X3,X2,X0),X4)
% 3.30/1.00      | v1_xboole_0(X1)
% 3.30/1.00      | v1_xboole_0(X3)
% 3.30/1.00      | v1_xboole_0(X4) ),
% 3.30/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_5040,plain,
% 3.30/1.00      ( ~ m1_subset_1(sK9,sK6)
% 3.30/1.00      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.30/1.00      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.30/1.00      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.30/1.00      | v1_xboole_0(sK6)
% 3.30/1.00      | v1_xboole_0(sK5)
% 3.30/1.00      | v1_xboole_0(sK7) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_5041,plain,
% 3.30/1.00      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.30/1.00      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.30/1.00      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
% 3.30/1.00      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.30/1.00      | v1_xboole_0(sK6) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.30/1.00      | v1_xboole_0(sK7) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_5040]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_22,negated_conjecture,
% 3.30/1.00      ( ~ m1_subset_1(X0,sK5)
% 3.30/1.00      | ~ r2_hidden(X0,sK7)
% 3.30/1.00      | k1_funct_1(sK8,X0) != sK9 ),
% 3.30/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9642,plain,
% 3.30/1.00      ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
% 3.30/1.00      | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.30/1.00      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9643,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
% 3.30/1.00      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
% 3.30/1.00      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_9642]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9674,plain,
% 3.30/1.00      ( v1_xboole_0(sK5) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_9379,c_27,c_28,c_1493,c_1524,c_1802,c_1804,c_1916,
% 3.30/1.00                 c_2083,c_2269,c_2712,c_3110,c_3434,c_5041,c_9643]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_17,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/1.00      | r2_hidden(sK3(X1,X0),X1)
% 3.30/1.00      | k1_relset_1(X1,X2,X0) = X1 ),
% 3.30/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1236,plain,
% 3.30/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.30/1.00      | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2605,plain,
% 3.30/1.00      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.30/1.00      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1229,c_1236]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_13,plain,
% 3.30/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.30/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.30/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1240,plain,
% 3.30/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.30/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1814,plain,
% 3.30/1.00      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1229,c_1240]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2608,plain,
% 3.30/1.00      ( k1_relat_1(sK8) = sK5
% 3.30/1.00      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_2605,c_1814]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1249,plain,
% 3.30/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.30/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2963,plain,
% 3.30/1.00      ( k1_relat_1(sK8) = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2608,c_1249]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9679,plain,
% 3.30/1.00      ( k1_relat_1(sK8) = sK5 ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_9674,c_2963]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_6,plain,
% 3.30/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.30/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.30/1.00      | ~ v1_relat_1(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1244,plain,
% 3.30/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.30/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3514,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.30/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_1244,c_1540]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3798,plain,
% 3.30/1.00      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.30/1.00      | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_3514,c_27,c_1524]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3799,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.30/1.00      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_3798]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3809,plain,
% 3.30/1.00      ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_2269,c_3799]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_8,plain,
% 3.30/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.30/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.30/1.00      | ~ v1_funct_1(X1)
% 3.30/1.00      | ~ v1_relat_1(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_310,plain,
% 3.30/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.30/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.30/1.00      | ~ v1_relat_1(X1)
% 3.30/1.00      | sK8 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_311,plain,
% 3.30/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.30/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 3.30/1.00      | ~ v1_relat_1(sK8) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_310]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1227,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1556,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 3.30/1.00      | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_311,c_24,c_1523]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1557,plain,
% 3.30/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.30/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_1556]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1558,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_1557]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1601,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 3.30/1.00      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1227,c_1558]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1602,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_1601]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_3910,plain,
% 3.30/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_3809,c_1602]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2709,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.30/1.00      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.30/1.00      | ~ v1_relat_1(sK8) ),
% 3.30/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_2716,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.30/1.00      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_2709]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4011,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_3910,c_27,c_1524,c_2269,c_2716]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_10,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.30/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.30/1.00      | ~ v1_funct_1(X1)
% 3.30/1.00      | ~ v1_relat_1(X1) ),
% 3.30/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_295,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(X1))
% 3.30/1.00      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.30/1.00      | ~ v1_relat_1(X1)
% 3.30/1.00      | sK8 != X1 ),
% 3.30/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_296,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.30/1.00      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.30/1.00      | ~ v1_relat_1(sK8) ),
% 3.30/1.00      inference(unflattening,[status(thm)],[c_295]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1228,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_297,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.30/1.00      | v1_relat_1(sK8) != iProver_top ),
% 3.30/1.00      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1592,plain,
% 3.30/1.00      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.30/1.00      | r2_hidden(X0,k1_relat_1(sK8)) = iProver_top ),
% 3.30/1.00      inference(global_propositional_subsumption,
% 3.30/1.00                [status(thm)],
% 3.30/1.00                [c_1228,c_27,c_297,c_1524]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_1593,plain,
% 3.30/1.00      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.30/1.00      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.30/1.00      inference(renaming,[status(thm)],[c_1592]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4017,plain,
% 3.30/1.00      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_4011,c_1593]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_4027,plain,
% 3.30/1.00      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.30/1.00      inference(superposition,[status(thm)],[c_4017,c_1249]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(c_9863,plain,
% 3.30/1.00      ( v1_xboole_0(sK5) != iProver_top ),
% 3.30/1.00      inference(demodulation,[status(thm)],[c_9679,c_4027]) ).
% 3.30/1.00  
% 3.30/1.00  cnf(contradiction,plain,
% 3.30/1.00      ( $false ),
% 3.30/1.00      inference(minisat,[status(thm)],[c_9863,c_9674]) ).
% 3.30/1.00  
% 3.30/1.00  
% 3.30/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.30/1.00  
% 3.30/1.00  ------                               Statistics
% 3.30/1.00  
% 3.30/1.00  ------ Selected
% 3.30/1.00  
% 3.30/1.00  total_time:                             0.384
% 3.30/1.00  
%------------------------------------------------------------------------------
