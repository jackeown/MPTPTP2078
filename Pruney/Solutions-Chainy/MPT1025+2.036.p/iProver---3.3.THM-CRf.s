%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:07 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  194 (1178 expanded)
%              Number of clauses        :  119 ( 413 expanded)
%              Number of leaves         :   23 ( 260 expanded)
%              Depth                    :   21
%              Number of atoms          :  711 (5409 expanded)
%              Number of equality atoms :  256 (1124 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ m1_subset_1(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f29,f50,f49])).

fof(f76,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f27])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK4(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK4(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f77,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f51])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ m1_subset_1(X5,sK5) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK3(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1002,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1012,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2031,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1002,c_1012])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1024,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1006,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
    | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_1006])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1022,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_1022])).

cnf(c_7999,plain,
    ( r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2041,c_2119])).

cnf(c_8000,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
    | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7999])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_334,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_335,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_999,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_8023,plain,
    ( k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
    | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8000,c_999])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1452,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_4,c_25])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1457,plain,
    ( v1_relat_1(sK8) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1452,c_5])).

cnf(c_1458,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_9580,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
    | k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8023,c_1458])).

cnf(c_9581,plain,
    ( k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
    | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9580])).

cnf(c_9593,plain,
    ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0)))) = sK0(k7_relset_1(sK5,sK6,sK8,X0))
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_9581])).

cnf(c_9600,plain,
    ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0)))) = sK0(k9_relat_1(sK8,X0))
    | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9593,c_2031])).

cnf(c_28,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_29,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1272,plain,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | ~ v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1273,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_535,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1488,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_1402,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_1594,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1592])).

cnf(c_1341,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1593,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_1596,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1593])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1477,plain,
    ( m1_subset_1(X0,sK6)
    | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
    | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1704,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | m1_subset_1(sK9,sK6)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1705,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1704])).

cnf(c_1356,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1794,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_536,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1599,plain,
    ( X0 != X1
    | X0 = k7_relset_1(sK5,sK6,sK8,sK7)
    | k7_relset_1(sK5,sK6,sK8,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1793,plain,
    ( X0 = k7_relset_1(sK5,sK6,sK8,sK7)
    | X0 != k9_relat_1(sK8,sK7)
    | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_1847,plain,
    ( k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7)
    | k9_relat_1(sK8,sK7) = k7_relset_1(sK5,sK6,sK8,sK7)
    | k9_relat_1(sK8,sK7) != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1793])).

cnf(c_1848,plain,
    ( k9_relat_1(sK8,sK7) = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_1003,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK4(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1005,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1525,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_1005])).

cnf(c_1866,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1525,c_28,c_29,c_1273,c_1594,c_1596,c_1705])).

cnf(c_537,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1346,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | X1 != k7_relset_1(sK5,sK6,sK8,sK7)
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1487,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | X0 != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_2276,plain,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_2277,plain,
    ( k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2276])).

cnf(c_2042,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_1006])).

cnf(c_2615,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2042,c_28,c_29,c_1273,c_1594,c_1596,c_1705])).

cnf(c_2624,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2615,c_999])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK4(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3042,plain,
    ( ~ m1_subset_1(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3043,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3042])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3443,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3444,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3443])).

cnf(c_5148,plain,
    ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5149,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5148])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_9680,plain,
    ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
    | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_9681,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
    | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9680])).

cnf(c_10035,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9600,c_25,c_28,c_29,c_1273,c_1458,c_1488,c_1594,c_1596,c_1705,c_1794,c_1847,c_1848,c_1866,c_2277,c_2624,c_3043,c_3444,c_5149,c_9681])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1009,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2354,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1002,c_1009])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1013,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1617,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1002,c_1013])).

cnf(c_2357,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2354,c_1617])).

cnf(c_1023,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2989,plain,
    ( k1_relat_1(sK8) = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_1023])).

cnf(c_10040,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_10035,c_2989])).

cnf(c_2471,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2031,c_1003])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1016,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3240,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_999])).

cnf(c_3460,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3240,c_1458])).

cnf(c_3461,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3460])).

cnf(c_3471,plain,
    ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_2471,c_3461])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_1000,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_3615,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3471,c_1000])).

cnf(c_3441,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3448,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3441])).

cnf(c_3705,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3615,c_25,c_29,c_1458,c_1488,c_1794,c_1847,c_1848,c_2277,c_3448])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_304,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_305,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_1001,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_3711,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3705,c_1001])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3442,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8))
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3446,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3442])).

cnf(c_3722,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3711,c_25,c_29,c_1458,c_1488,c_1794,c_1847,c_1848,c_2277,c_3446])).

cnf(c_3727,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3722,c_1023])).

cnf(c_10253,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10040,c_3727])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10253,c_10035])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:27:00 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.33  % Running in FOF mode
% 3.61/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.98  
% 3.61/0.98  ------  iProver source info
% 3.61/0.98  
% 3.61/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.98  git: non_committed_changes: false
% 3.61/0.98  git: last_make_outside_of_git: false
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  ------ Parsing...
% 3.61/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.98  
% 3.61/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.98  ------ Proving...
% 3.61/0.98  ------ Problem Properties 
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  clauses                                 26
% 3.61/0.98  conjectures                             3
% 3.61/0.98  EPR                                     1
% 3.61/0.98  Horn                                    20
% 3.61/0.98  unary                                   3
% 3.61/0.98  binary                                  5
% 3.61/0.98  lits                                    88
% 3.61/0.98  lits eq                                 7
% 3.61/0.98  fd_pure                                 0
% 3.61/0.98  fd_pseudo                               0
% 3.61/0.98  fd_cond                                 0
% 3.61/0.98  fd_pseudo_cond                          1
% 3.61/0.98  AC symbols                              0
% 3.61/0.98  
% 3.61/0.98  ------ Input Options Time Limit: Unbounded
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ 
% 3.61/0.98  Current options:
% 3.61/0.98  ------ 
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  ------ Proving...
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  % SZS status Theorem for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  fof(f13,conjecture,(
% 3.61/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f14,negated_conjecture,(
% 3.61/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.61/0.98    inference(negated_conjecture,[],[f13])).
% 3.61/0.98  
% 3.61/0.98  fof(f15,plain,(
% 3.61/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.61/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.61/0.98  
% 3.61/0.98  fof(f28,plain,(
% 3.61/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.61/0.98    inference(ennf_transformation,[],[f15])).
% 3.61/0.98  
% 3.61/0.98  fof(f29,plain,(
% 3.61/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.61/0.98    inference(flattening,[],[f28])).
% 3.61/0.98  
% 3.61/0.98  fof(f50,plain,(
% 3.61/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f49,plain,(
% 3.61/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f51,plain,(
% 3.61/0.98    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8)),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f29,f50,f49])).
% 3.61/0.98  
% 3.61/0.98  fof(f76,plain,(
% 3.61/0.98    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.61/0.98    inference(cnf_transformation,[],[f51])).
% 3.61/0.98  
% 3.61/0.98  fof(f10,axiom,(
% 3.61/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f25,plain,(
% 3.61/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f10])).
% 3.61/0.98  
% 3.61/0.98  fof(f67,plain,(
% 3.61/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f25])).
% 3.61/0.98  
% 3.61/0.98  fof(f1,axiom,(
% 3.61/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f30,plain,(
% 3.61/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.61/0.98    inference(nnf_transformation,[],[f1])).
% 3.61/0.98  
% 3.61/0.98  fof(f31,plain,(
% 3.61/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.61/0.98    inference(rectify,[],[f30])).
% 3.61/0.98  
% 3.61/0.98  fof(f32,plain,(
% 3.61/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f33,plain,(
% 3.61/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 3.61/0.98  
% 3.61/0.98  fof(f53,plain,(
% 3.61/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f33])).
% 3.61/0.98  
% 3.61/0.98  fof(f12,axiom,(
% 3.61/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f27,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f12])).
% 3.61/0.98  
% 3.61/0.98  fof(f45,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.61/0.98    inference(nnf_transformation,[],[f27])).
% 3.61/0.98  
% 3.61/0.98  fof(f46,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.61/0.98    inference(rectify,[],[f45])).
% 3.61/0.98  
% 3.61/0.98  fof(f47,plain,(
% 3.61/0.98    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f48,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f46,f47])).
% 3.61/0.98  
% 3.61/0.98  fof(f72,plain,(
% 3.61/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f48])).
% 3.61/0.98  
% 3.61/0.98  fof(f8,axiom,(
% 3.61/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f23,plain,(
% 3.61/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f8])).
% 3.61/0.98  
% 3.61/0.98  fof(f65,plain,(
% 3.61/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f23])).
% 3.61/0.98  
% 3.61/0.98  fof(f2,axiom,(
% 3.61/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f16,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f2])).
% 3.61/0.98  
% 3.61/0.98  fof(f54,plain,(
% 3.61/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f16])).
% 3.61/0.98  
% 3.61/0.98  fof(f7,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f21,plain,(
% 3.61/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.61/0.98    inference(ennf_transformation,[],[f7])).
% 3.61/0.98  
% 3.61/0.98  fof(f22,plain,(
% 3.61/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(flattening,[],[f21])).
% 3.61/0.98  
% 3.61/0.98  fof(f38,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(nnf_transformation,[],[f22])).
% 3.61/0.98  
% 3.61/0.98  fof(f39,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(flattening,[],[f38])).
% 3.61/0.98  
% 3.61/0.98  fof(f63,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f75,plain,(
% 3.61/0.98    v1_funct_1(sK8)),
% 3.61/0.98    inference(cnf_transformation,[],[f51])).
% 3.61/0.98  
% 3.61/0.98  fof(f4,axiom,(
% 3.61/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f19,plain,(
% 3.61/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.61/0.98    inference(ennf_transformation,[],[f4])).
% 3.61/0.98  
% 3.61/0.98  fof(f56,plain,(
% 3.61/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f19])).
% 3.61/0.98  
% 3.61/0.98  fof(f5,axiom,(
% 3.61/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f57,plain,(
% 3.61/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f5])).
% 3.61/0.98  
% 3.61/0.98  fof(f77,plain,(
% 3.61/0.98    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.61/0.98    inference(cnf_transformation,[],[f51])).
% 3.61/0.98  
% 3.61/0.98  fof(f52,plain,(
% 3.61/0.98    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f33])).
% 3.61/0.98  
% 3.61/0.98  fof(f3,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f17,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.61/0.98    inference(ennf_transformation,[],[f3])).
% 3.61/0.98  
% 3.61/0.98  fof(f18,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.61/0.98    inference(flattening,[],[f17])).
% 3.61/0.98  
% 3.61/0.98  fof(f55,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f18])).
% 3.61/0.98  
% 3.61/0.98  fof(f71,plain,(
% 3.61/0.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f48])).
% 3.61/0.98  
% 3.61/0.98  fof(f73,plain,(
% 3.61/0.98    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f48])).
% 3.61/0.98  
% 3.61/0.98  fof(f6,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f20,plain,(
% 3.61/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(ennf_transformation,[],[f6])).
% 3.61/0.98  
% 3.61/0.98  fof(f34,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(nnf_transformation,[],[f20])).
% 3.61/0.98  
% 3.61/0.98  fof(f35,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(rectify,[],[f34])).
% 3.61/0.98  
% 3.61/0.98  fof(f36,plain,(
% 3.61/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f37,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.61/0.98  
% 3.61/0.98  fof(f60,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f37])).
% 3.61/0.98  
% 3.61/0.98  fof(f78,plain,(
% 3.61/0.98    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f51])).
% 3.61/0.98  
% 3.61/0.98  fof(f11,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f26,plain,(
% 3.61/0.98    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.61/0.98    inference(ennf_transformation,[],[f11])).
% 3.61/0.98  
% 3.61/0.98  fof(f40,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.61/0.98    inference(nnf_transformation,[],[f26])).
% 3.61/0.98  
% 3.61/0.98  fof(f41,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.61/0.98    inference(rectify,[],[f40])).
% 3.61/0.98  
% 3.61/0.98  fof(f43,plain,(
% 3.61/0.98    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f42,plain,(
% 3.61/0.98    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 3.61/0.98    introduced(choice_axiom,[])).
% 3.61/0.98  
% 3.61/0.98  fof(f44,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.61/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f41,f43,f42])).
% 3.61/0.98  
% 3.61/0.98  fof(f68,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK3(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f44])).
% 3.61/0.98  
% 3.61/0.98  fof(f9,axiom,(
% 3.61/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.61/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.98  
% 3.61/0.98  fof(f24,plain,(
% 3.61/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.98    inference(ennf_transformation,[],[f9])).
% 3.61/0.98  
% 3.61/0.98  fof(f66,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.98    inference(cnf_transformation,[],[f24])).
% 3.61/0.98  
% 3.61/0.98  fof(f59,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f37])).
% 3.61/0.98  
% 3.61/0.98  fof(f64,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f79,plain,(
% 3.61/0.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(equality_resolution,[],[f64])).
% 3.61/0.98  
% 3.61/0.98  fof(f62,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f39])).
% 3.61/0.98  
% 3.61/0.98  fof(f58,plain,(
% 3.61/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.61/0.98    inference(cnf_transformation,[],[f37])).
% 3.61/0.98  
% 3.61/0.98  cnf(c_25,negated_conjecture,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.61/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1002,plain,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_15,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.61/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1012,plain,
% 3.61/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2031,plain,
% 3.61/0.98      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1002,c_1012]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_0,plain,
% 3.61/0.98      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1024,plain,
% 3.61/0.98      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_21,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,X1)
% 3.61/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.61/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.61/0.98      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
% 3.61/0.98      | v1_xboole_0(X1)
% 3.61/0.98      | v1_xboole_0(X3)
% 3.61/0.98      | v1_xboole_0(X4) ),
% 3.61/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1006,plain,
% 3.61/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.61/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(X3) = iProver_top
% 3.61/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2041,plain,
% 3.61/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(X2) = iProver_top
% 3.61/0.98      | v1_xboole_0(X3) = iProver_top
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1024,c_1006]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_13,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.61/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1014,plain,
% 3.61/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.98      | ~ v1_xboole_0(X1)
% 3.61/0.98      | v1_xboole_0(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1022,plain,
% 3.61/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.61/0.98      | v1_xboole_0(X1) != iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2119,plain,
% 3.61/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | v1_xboole_0(X2) != iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1014,c_1022]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_7999,plain,
% 3.61/0.98      ( r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
% 3.61/0.98      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.61/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | v1_xboole_0(X3) = iProver_top
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_2041,c_2119]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_8000,plain,
% 3.61/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | m1_subset_1(sK0(k7_relset_1(X1,X2,X0,X3)),X2) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(sK4(X3,X1,X0,sK0(k7_relset_1(X1,X2,X0,X3))),sK0(k7_relset_1(X1,X2,X0,X3))),X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(X3) = iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(X1,X2,X0,X3)) = iProver_top ),
% 3.61/0.98      inference(renaming,[status(thm)],[c_7999]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_11,plain,
% 3.61/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.61/0.98      | ~ v1_funct_1(X2)
% 3.61/0.98      | ~ v1_relat_1(X2)
% 3.61/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.61/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_26,negated_conjecture,
% 3.61/0.98      ( v1_funct_1(sK8) ),
% 3.61/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_334,plain,
% 3.61/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.61/0.98      | ~ v1_relat_1(X2)
% 3.61/0.98      | k1_funct_1(X2,X0) = X1
% 3.61/0.98      | sK8 != X2 ),
% 3.61/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_335,plain,
% 3.61/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.61/0.98      | ~ v1_relat_1(sK8)
% 3.61/0.98      | k1_funct_1(sK8,X0) = X1 ),
% 3.61/0.98      inference(unflattening,[status(thm)],[c_334]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_999,plain,
% 3.61/0.98      ( k1_funct_1(sK8,X0) = X1
% 3.61/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_8023,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
% 3.61/0.98      | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_8000,c_999]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_4,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.98      | ~ v1_relat_1(X1)
% 3.61/0.98      | v1_relat_1(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1452,plain,
% 3.61/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6)) | v1_relat_1(sK8) ),
% 3.61/0.98      inference(resolution,[status(thm)],[c_4,c_25]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5,plain,
% 3.61/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.61/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1457,plain,
% 3.61/0.98      ( v1_relat_1(sK8) ),
% 3.61/0.98      inference(forward_subsumption_resolution,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_1452,c_5]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1458,plain,
% 3.61/0.98      ( v1_relat_1(sK8) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9580,plain,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
% 3.61/0.98      | k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_8023,c_1458]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9581,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(X0,X1,sK8,sK0(k7_relset_1(X1,X2,sK8,X0)))) = sK0(k7_relset_1(X1,X2,sK8,X0))
% 3.61/0.98      | m1_subset_1(sK0(k7_relset_1(X1,X2,sK8,X0)),X2) != iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(X1,X2,sK8,X0)) = iProver_top ),
% 3.61/0.98      inference(renaming,[status(thm)],[c_9580]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9593,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k7_relset_1(sK5,sK6,sK8,X0)))) = sK0(k7_relset_1(sK5,sK6,sK8,X0))
% 3.61/0.98      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,X0)) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_2031,c_9581]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9600,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(X0,sK5,sK8,sK0(k9_relat_1(sK8,X0)))) = sK0(k9_relat_1(sK8,X0))
% 3.61/0.98      | m1_subset_1(sK0(k9_relat_1(sK8,X0)),sK6) != iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.61/0.98      | v1_xboole_0(X0) = iProver_top
% 3.61/0.98      | v1_xboole_0(k9_relat_1(sK8,X0)) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.61/0.98      inference(light_normalisation,[status(thm)],[c_9593,c_2031]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_28,plain,
% 3.61/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_24,negated_conjecture,
% 3.61/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.61/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_29,plain,
% 3.61/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1272,plain,
% 3.61/0.98      ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.61/0.98      | ~ v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1273,plain,
% 3.61/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_535,plain,( X0 = X0 ),theory(equality) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1488,plain,
% 3.61/0.98      ( sK9 = sK9 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_535]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1402,plain,
% 3.61/0.98      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(X0))
% 3.61/0.98      | ~ v1_xboole_0(X0)
% 3.61/0.98      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1592,plain,
% 3.61/0.98      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.61/0.98      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7))
% 3.61/0.98      | ~ v1_xboole_0(sK6) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1402]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1594,plain,
% 3.61/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 3.61/0.98      | v1_xboole_0(k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK6) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1592]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1341,plain,
% 3.61/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
% 3.61/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1593,plain,
% 3.61/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.61/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1341]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1596,plain,
% 3.61/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1593]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3,plain,
% 3.61/0.98      ( m1_subset_1(X0,X1)
% 3.61/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.61/0.98      | ~ r2_hidden(X0,X2) ),
% 3.61/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1477,plain,
% 3.61/0.98      ( m1_subset_1(X0,sK6)
% 3.61/0.98      | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
% 3.61/0.98      | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1704,plain,
% 3.61/0.98      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.61/0.98      | m1_subset_1(sK9,sK6)
% 3.61/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1477]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1705,plain,
% 3.61/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 3.61/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 3.61/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1704]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1356,plain,
% 3.61/0.98      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.61/0.98      | k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1794,plain,
% 3.61/0.98      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.61/0.98      | k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1356]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_536,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1599,plain,
% 3.61/0.98      ( X0 != X1
% 3.61/0.98      | X0 = k7_relset_1(sK5,sK6,sK8,sK7)
% 3.61/0.98      | k7_relset_1(sK5,sK6,sK8,sK7) != X1 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_536]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1793,plain,
% 3.61/0.98      ( X0 = k7_relset_1(sK5,sK6,sK8,sK7)
% 3.61/0.98      | X0 != k9_relat_1(sK8,sK7)
% 3.61/0.98      | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1599]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1847,plain,
% 3.61/0.98      ( k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7)
% 3.61/0.98      | k9_relat_1(sK8,sK7) = k7_relset_1(sK5,sK6,sK8,sK7)
% 3.61/0.98      | k9_relat_1(sK8,sK7) != k9_relat_1(sK8,sK7) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1793]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1848,plain,
% 3.61/0.98      ( k9_relat_1(sK8,sK7) = k9_relat_1(sK8,sK7) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_535]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1003,plain,
% 3.61/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_22,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,X1)
% 3.61/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.61/0.98      | m1_subset_1(sK4(X4,X3,X2,X0),X3)
% 3.61/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.61/0.98      | v1_xboole_0(X1)
% 3.61/0.98      | v1_xboole_0(X3)
% 3.61/0.98      | v1_xboole_0(X4) ),
% 3.61/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1005,plain,
% 3.61/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.61/0.98      | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
% 3.61/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.61/0.98      | v1_xboole_0(X1) = iProver_top
% 3.61/0.98      | v1_xboole_0(X3) = iProver_top
% 3.61/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1525,plain,
% 3.61/0.98      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.61/0.98      | m1_subset_1(sK9,sK6) != iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.61/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1003,c_1005]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1866,plain,
% 3.61/0.98      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_1525,c_28,c_29,c_1273,c_1594,c_1596,c_1705]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_537,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.61/0.98      theory(equality) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1346,plain,
% 3.61/0.98      ( r2_hidden(X0,X1)
% 3.61/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.61/0.98      | X1 != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.61/0.98      | X0 != sK9 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_537]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1487,plain,
% 3.61/0.98      ( r2_hidden(sK9,X0)
% 3.61/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.61/0.98      | X0 != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.61/0.98      | sK9 != sK9 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1346]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2276,plain,
% 3.61/0.98      ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.61/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.61/0.98      | k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.61/0.98      | sK9 != sK9 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1487]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2277,plain,
% 3.61/0.98      ( k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.61/0.98      | sK9 != sK9
% 3.61/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.61/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_2276]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2042,plain,
% 3.61/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1003,c_1006]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2615,plain,
% 3.61/0.98      ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_2042,c_28,c_29,c_1273,c_1594,c_1596,c_1705]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2624,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_2615,c_999]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_20,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,X1)
% 3.61/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.61/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.61/0.98      | r2_hidden(sK4(X4,X3,X2,X0),X4)
% 3.61/0.98      | v1_xboole_0(X1)
% 3.61/0.98      | v1_xboole_0(X3)
% 3.61/0.98      | v1_xboole_0(X4) ),
% 3.61/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3042,plain,
% 3.61/0.98      ( ~ m1_subset_1(sK9,sK6)
% 3.61/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.61/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.61/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.61/0.98      | v1_xboole_0(sK6)
% 3.61/0.98      | v1_xboole_0(sK5)
% 3.61/0.98      | v1_xboole_0(sK7) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3043,plain,
% 3.61/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.61/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.61/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
% 3.61/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.61/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.61/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_3042]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_7,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.61/0.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3443,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
% 3.61/0.98      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.61/0.98      | ~ v1_relat_1(sK8) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3444,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
% 3.61/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_3443]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5148,plain,
% 3.61/0.98      ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7) | ~ v1_xboole_0(sK7) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_5149,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
% 3.61/0.98      | v1_xboole_0(sK7) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_5148]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_23,negated_conjecture,
% 3.61/0.98      ( ~ m1_subset_1(X0,sK5)
% 3.61/0.98      | ~ r2_hidden(X0,sK7)
% 3.61/0.98      | k1_funct_1(sK8,X0) != sK9 ),
% 3.61/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9680,plain,
% 3.61/0.98      ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
% 3.61/0.98      | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.61/0.98      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9681,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
% 3.61/0.98      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
% 3.61/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_9680]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_10035,plain,
% 3.61/0.98      ( v1_xboole_0(sK5) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_9600,c_25,c_28,c_29,c_1273,c_1458,c_1488,c_1594,
% 3.61/0.98                 c_1596,c_1705,c_1794,c_1847,c_1848,c_1866,c_2277,c_2624,
% 3.61/0.98                 c_3043,c_3444,c_5149,c_9681]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_18,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | r2_hidden(sK3(X1,X0),X1)
% 3.61/0.98      | k1_relset_1(X1,X2,X0) = X1 ),
% 3.61/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1009,plain,
% 3.61/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.61/0.98      | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2354,plain,
% 3.61/0.98      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.61/0.98      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1002,c_1009]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_14,plain,
% 3.61/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.61/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1013,plain,
% 3.61/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.61/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1617,plain,
% 3.61/0.98      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1002,c_1013]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2357,plain,
% 3.61/0.98      ( k1_relat_1(sK8) = sK5
% 3.61/0.98      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_2354,c_1617]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1023,plain,
% 3.61/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.61/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2989,plain,
% 3.61/0.98      ( k1_relat_1(sK8) = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_2357,c_1023]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_10040,plain,
% 3.61/0.98      ( k1_relat_1(sK8) = sK5 ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_10035,c_2989]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_2471,plain,
% 3.61/0.98      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_2031,c_1003]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_8,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.61/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1016,plain,
% 3.61/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.61/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3240,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.61/0.98      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_1016,c_999]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3460,plain,
% 3.61/0.98      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.61/0.98      | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_3240,c_1458]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3461,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.61/0.98      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.61/0.98      inference(renaming,[status(thm)],[c_3460]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3471,plain,
% 3.61/0.98      ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_2471,c_3461]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_10,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.61/0.98      | ~ v1_funct_1(X1)
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_319,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.61/0.98      | ~ v1_relat_1(X1)
% 3.61/0.98      | sK8 != X1 ),
% 3.61/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_320,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.61/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 3.61/0.98      | ~ v1_relat_1(sK8) ),
% 3.61/0.98      inference(unflattening,[status(thm)],[c_319]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1000,plain,
% 3.61/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3615,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_3471,c_1000]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3441,plain,
% 3.61/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.61/0.98      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.61/0.98      | ~ v1_relat_1(sK8) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3448,plain,
% 3.61/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.61/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_3441]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3705,plain,
% 3.61/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_3615,c_25,c_29,c_1458,c_1488,c_1794,c_1847,c_1848,
% 3.61/0.98                 c_2277,c_3448]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_12,plain,
% 3.61/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.61/0.98      | ~ v1_funct_1(X1)
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_304,plain,
% 3.61/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.61/0.98      | ~ v1_relat_1(X1)
% 3.61/0.98      | sK8 != X1 ),
% 3.61/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_305,plain,
% 3.61/0.98      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.61/0.98      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.61/0.98      | ~ v1_relat_1(sK8) ),
% 3.61/0.98      inference(unflattening,[status(thm)],[c_304]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_1001,plain,
% 3.61/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.61/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3711,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_3705,c_1001]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_9,plain,
% 3.61/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.61/0.98      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.61/0.98      | ~ v1_relat_1(X1) ),
% 3.61/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3442,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8))
% 3.61/0.98      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.61/0.98      | ~ v1_relat_1(sK8) ),
% 3.61/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3446,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top
% 3.61/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.61/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.61/0.98      inference(predicate_to_equality,[status(thm)],[c_3442]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3722,plain,
% 3.61/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
% 3.61/0.98      inference(global_propositional_subsumption,
% 3.61/0.98                [status(thm)],
% 3.61/0.98                [c_3711,c_25,c_29,c_1458,c_1488,c_1794,c_1847,c_1848,
% 3.61/0.98                 c_2277,c_3446]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_3727,plain,
% 3.61/0.98      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.61/0.98      inference(superposition,[status(thm)],[c_3722,c_1023]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(c_10253,plain,
% 3.61/0.98      ( v1_xboole_0(sK5) != iProver_top ),
% 3.61/0.98      inference(demodulation,[status(thm)],[c_10040,c_3727]) ).
% 3.61/0.98  
% 3.61/0.98  cnf(contradiction,plain,
% 3.61/0.98      ( $false ),
% 3.61/0.98      inference(minisat,[status(thm)],[c_10253,c_10035]) ).
% 3.61/0.98  
% 3.61/0.98  
% 3.61/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.98  
% 3.61/0.98  ------                               Statistics
% 3.61/0.98  
% 3.61/0.98  ------ Selected
% 3.61/0.98  
% 3.61/0.98  total_time:                             0.395
% 3.61/0.98  
%------------------------------------------------------------------------------
