%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:04 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  189 (1075 expanded)
%              Number of clauses        :  117 ( 349 expanded)
%              Number of leaves         :   22 ( 236 expanded)
%              Depth                    :   22
%              Number of atoms          :  671 (5209 expanded)
%              Number of equality atoms :  231 (1055 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
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

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f53,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ m1_subset_1(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f31,f52,f51])).

fof(f78,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
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

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f77,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
        & r2_hidden(sK3(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
     => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2)
              | ~ r2_hidden(X3,X1) )
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
            & r2_hidden(sK3(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f45,f44])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r2_hidden(k4_tarski(sK3(X1,X2),X6),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK4(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK4(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK3(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ m1_subset_1(X5,sK5) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1261,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_321,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_1259,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1536,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1563,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
    | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_25,c_1536])).

cnf(c_1564,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
    inference(renaming,[status(thm)],[c_1563])).

cnf(c_1565,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_1650,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1259,c_1565])).

cnf(c_1651,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_1650])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(sK3(X1,X0),X3),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1269,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X2),X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4434,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,sK8),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1651,c_1269])).

cnf(c_4758,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_4434])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1272,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1847,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1261,c_1272])).

cnf(c_4759,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4758,c_1847])).

cnf(c_28,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1537,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_792,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1751,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1745,plain,
    ( m1_subset_1(X0,sK6)
    | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
    | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1942,plain,
    ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | m1_subset_1(sK9,sK6)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(instantiation,[status(thm)],[c_1745])).

cnf(c_1943,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
    | m1_subset_1(sK9,sK6) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1634,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2087,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_1262,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_1264,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1766,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1264])).

cnf(c_2106,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1766,c_28])).

cnf(c_2107,plain,
    ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
    | m1_subset_1(sK9,sK6) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_2106])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1619,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2151,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_2152,plain,
    ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2151])).

cnf(c_793,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1881,plain,
    ( X0 != X1
    | X0 = k7_relset_1(sK5,sK6,sK8,sK7)
    | k7_relset_1(sK5,sK6,sK8,sK7) != X1 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_2086,plain,
    ( X0 = k7_relset_1(sK5,sK6,sK8,sK7)
    | X0 != k9_relat_1(sK8,sK7)
    | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_2157,plain,
    ( k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7)
    | k9_relat_1(sK8,sK7) = k7_relset_1(sK5,sK6,sK8,sK7)
    | k9_relat_1(sK8,sK7) != k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_2158,plain,
    ( k9_relat_1(sK8,sK7) = k9_relat_1(sK8,sK7) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2423,plain,
    ( v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1274])).

cnf(c_794,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1624,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | X1 != k7_relset_1(sK5,sK6,sK8,sK7)
    | X0 != sK9 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1750,plain,
    ( r2_hidden(sK9,X0)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | X0 != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_2520,plain,
    ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_2521,plain,
    ( k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
    | sK9 != sK9
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2520])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1265,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2271,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1265])).

cnf(c_2806,plain,
    ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2271,c_28,c_29,c_1943,c_2152])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_336,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_337,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8)
    | k1_funct_1(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_1258,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_338,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1588,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | k1_funct_1(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1258,c_28,c_338,c_1537])).

cnf(c_1589,plain,
    ( k1_funct_1(sK8,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_1588])).

cnf(c_2816,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2806,c_1589])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2900,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2901,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2900])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2898,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2905,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2898])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3782,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3783,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3782])).

cnf(c_3910,plain,
    ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7)
    | ~ v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3911,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3910])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK4(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4103,plain,
    ( ~ m1_subset_1(sK9,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK7) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4104,plain,
    ( m1_subset_1(sK9,sK6) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4103])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK3(X1,X0),X1)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1268,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3330,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1268])).

cnf(c_3333,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3330,c_1847])).

cnf(c_1282,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4120,plain,
    ( k1_relat_1(sK8) = sK5
    | v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3333,c_1282])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4707,plain,
    ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
    | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
    | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4708,plain,
    ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
    | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4707])).

cnf(c_4943,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4759,c_25,c_28,c_29,c_1537,c_1751,c_1943,c_2087,c_2107,c_2152,c_2157,c_2158,c_2423,c_2521,c_2816,c_2901,c_2905,c_3783,c_3911,c_4104,c_4120,c_4708])).

cnf(c_1271,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2305,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1261,c_1271])).

cnf(c_2548,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2305,c_1262])).

cnf(c_1277,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3477,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1589])).

cnf(c_3823,plain,
    ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3477,c_28,c_1537])).

cnf(c_3824,plain,
    ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3823])).

cnf(c_3834,plain,
    ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
    inference(superposition,[status(thm)],[c_2548,c_3824])).

cnf(c_3863,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_3834,c_1651])).

cnf(c_3969,plain,
    ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3863,c_25,c_28,c_29,c_1537,c_1751,c_2087,c_2157,c_2158,c_2521,c_2905])).

cnf(c_10,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_306,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v1_relat_1(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_307,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_1260,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1544,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
    | r2_hidden(X0,k1_relat_1(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_25,c_1536])).

cnf(c_1545,plain,
    ( r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(k4_tarski(X0,X1),sK8) ),
    inference(renaming,[status(thm)],[c_1544])).

cnf(c_1546,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_1643,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1260,c_1546])).

cnf(c_1644,plain,
    ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_1643])).

cnf(c_3975,plain,
    ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3969,c_1644])).

cnf(c_4112,plain,
    ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_1282])).

cnf(c_4947,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4943,c_4112])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4947,c_4708,c_4104,c_3911,c_3783,c_2905,c_2901,c_2816,c_2521,c_2423,c_2158,c_2157,c_2152,c_2107,c_2087,c_1943,c_1751,c_1537,c_29,c_28,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:07:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.57/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.57/0.97  
% 3.57/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/0.97  
% 3.57/0.97  ------  iProver source info
% 3.57/0.97  
% 3.57/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.57/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/0.97  git: non_committed_changes: false
% 3.57/0.97  git: last_make_outside_of_git: false
% 3.57/0.97  
% 3.57/0.97  ------ 
% 3.57/0.97  ------ Parsing...
% 3.57/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/0.97  
% 3.57/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/0.97  ------ Proving...
% 3.57/0.97  ------ Problem Properties 
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  clauses                                 26
% 3.57/0.97  conjectures                             3
% 3.57/0.97  EPR                                     2
% 3.57/0.97  Horn                                    19
% 3.57/0.97  unary                                   2
% 3.57/0.97  binary                                  6
% 3.57/0.97  lits                                    89
% 3.57/0.97  lits eq                                 7
% 3.57/0.97  fd_pure                                 0
% 3.57/0.97  fd_pseudo                               0
% 3.57/0.97  fd_cond                                 0
% 3.57/0.97  fd_pseudo_cond                          1
% 3.57/0.97  AC symbols                              0
% 3.57/0.97  
% 3.57/0.97  ------ Input Options Time Limit: Unbounded
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  ------ 
% 3.57/0.97  Current options:
% 3.57/0.97  ------ 
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  ------ Proving...
% 3.57/0.97  
% 3.57/0.97  
% 3.57/0.97  % SZS status Theorem for theBenchmark.p
% 3.57/0.97  
% 3.57/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/0.97  
% 3.57/0.97  fof(f13,conjecture,(
% 3.57/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f14,negated_conjecture,(
% 3.57/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.57/0.97    inference(negated_conjecture,[],[f13])).
% 3.57/0.97  
% 3.57/0.97  fof(f15,plain,(
% 3.57/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.57/0.97    inference(pure_predicate_removal,[],[f14])).
% 3.57/0.97  
% 3.57/0.97  fof(f30,plain,(
% 3.57/0.97    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.57/0.97    inference(ennf_transformation,[],[f15])).
% 3.57/0.97  
% 3.57/0.97  fof(f31,plain,(
% 3.57/0.97    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.57/0.97    inference(flattening,[],[f30])).
% 3.57/0.97  
% 3.57/0.97  fof(f52,plain,(
% 3.57/0.97    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f51,plain,(
% 3.57/0.97    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f53,plain,(
% 3.57/0.97    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK8)),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f31,f52,f51])).
% 3.57/0.97  
% 3.57/0.97  fof(f78,plain,(
% 3.57/0.97    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.57/0.97    inference(cnf_transformation,[],[f53])).
% 3.57/0.97  
% 3.57/0.97  fof(f5,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f21,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.57/0.97    inference(ennf_transformation,[],[f5])).
% 3.57/0.97  
% 3.57/0.97  fof(f22,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.57/0.97    inference(flattening,[],[f21])).
% 3.57/0.97  
% 3.57/0.97  fof(f40,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.57/0.97    inference(nnf_transformation,[],[f22])).
% 3.57/0.97  
% 3.57/0.97  fof(f41,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.57/0.97    inference(flattening,[],[f40])).
% 3.57/0.97  
% 3.57/0.97  fof(f64,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f41])).
% 3.57/0.97  
% 3.57/0.97  fof(f81,plain,(
% 3.57/0.97    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.97    inference(equality_resolution,[],[f64])).
% 3.57/0.97  
% 3.57/0.97  fof(f77,plain,(
% 3.57/0.97    v1_funct_1(sK8)),
% 3.57/0.97    inference(cnf_transformation,[],[f53])).
% 3.57/0.97  
% 3.57/0.97  fof(f6,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f23,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.97    inference(ennf_transformation,[],[f6])).
% 3.57/0.97  
% 3.57/0.97  fof(f65,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.97    inference(cnf_transformation,[],[f23])).
% 3.57/0.97  
% 3.57/0.97  fof(f11,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f28,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.57/0.97    inference(ennf_transformation,[],[f11])).
% 3.57/0.97  
% 3.57/0.97  fof(f42,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.57/0.97    inference(nnf_transformation,[],[f28])).
% 3.57/0.97  
% 3.57/0.97  fof(f43,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.57/0.97    inference(rectify,[],[f42])).
% 3.57/0.97  
% 3.57/0.97  fof(f45,plain,(
% 3.57/0.97    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X5,X6),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f44,plain,(
% 3.57/0.97    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) => r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f46,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(X3,sK2(X2,X3)),X2) | ~r2_hidden(X3,X1)) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) & r2_hidden(sK3(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f45,f44])).
% 3.57/0.97  
% 3.57/0.97  fof(f71,plain,(
% 3.57/0.97    ( ! [X6,X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r2_hidden(k4_tarski(sK3(X1,X2),X6),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.57/0.97    inference(cnf_transformation,[],[f46])).
% 3.57/0.97  
% 3.57/0.97  fof(f9,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f26,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.97    inference(ennf_transformation,[],[f9])).
% 3.57/0.97  
% 3.57/0.97  fof(f68,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.97    inference(cnf_transformation,[],[f26])).
% 3.57/0.97  
% 3.57/0.97  fof(f79,plain,(
% 3.57/0.97    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.57/0.97    inference(cnf_transformation,[],[f53])).
% 3.57/0.97  
% 3.57/0.97  fof(f3,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f18,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.57/0.97    inference(ennf_transformation,[],[f3])).
% 3.57/0.97  
% 3.57/0.97  fof(f19,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.57/0.97    inference(flattening,[],[f18])).
% 3.57/0.97  
% 3.57/0.97  fof(f57,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f19])).
% 3.57/0.97  
% 3.57/0.97  fof(f10,axiom,(
% 3.57/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f27,plain,(
% 3.57/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.97    inference(ennf_transformation,[],[f10])).
% 3.57/0.97  
% 3.57/0.97  fof(f69,plain,(
% 3.57/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.97    inference(cnf_transformation,[],[f27])).
% 3.57/0.97  
% 3.57/0.97  fof(f12,axiom,(
% 3.57/0.97    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f29,plain,(
% 3.57/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.57/0.97    inference(ennf_transformation,[],[f12])).
% 3.57/0.97  
% 3.57/0.97  fof(f47,plain,(
% 3.57/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.57/0.97    inference(nnf_transformation,[],[f29])).
% 3.57/0.97  
% 3.57/0.97  fof(f48,plain,(
% 3.57/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.57/0.97    inference(rectify,[],[f47])).
% 3.57/0.97  
% 3.57/0.97  fof(f49,plain,(
% 3.57/0.97    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f50,plain,(
% 3.57/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 3.57/0.97  
% 3.57/0.97  fof(f73,plain,(
% 3.57/0.97    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK4(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f50])).
% 3.57/0.97  
% 3.57/0.97  fof(f8,axiom,(
% 3.57/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f25,plain,(
% 3.57/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.57/0.97    inference(ennf_transformation,[],[f8])).
% 3.57/0.97  
% 3.57/0.97  fof(f67,plain,(
% 3.57/0.97    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.57/0.97    inference(cnf_transformation,[],[f25])).
% 3.57/0.97  
% 3.57/0.97  fof(f7,axiom,(
% 3.57/0.97    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f24,plain,(
% 3.57/0.97    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.57/0.97    inference(ennf_transformation,[],[f7])).
% 3.57/0.97  
% 3.57/0.97  fof(f66,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f24])).
% 3.57/0.97  
% 3.57/0.97  fof(f74,plain,(
% 3.57/0.97    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f50])).
% 3.57/0.97  
% 3.57/0.97  fof(f63,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f41])).
% 3.57/0.97  
% 3.57/0.97  fof(f4,axiom,(
% 3.57/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f20,plain,(
% 3.57/0.97    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.57/0.97    inference(ennf_transformation,[],[f4])).
% 3.57/0.97  
% 3.57/0.97  fof(f36,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.57/0.97    inference(nnf_transformation,[],[f20])).
% 3.57/0.97  
% 3.57/0.97  fof(f37,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.57/0.97    inference(rectify,[],[f36])).
% 3.57/0.97  
% 3.57/0.97  fof(f38,plain,(
% 3.57/0.97    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f39,plain,(
% 3.57/0.97    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 3.57/0.97  
% 3.57/0.97  fof(f60,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f39])).
% 3.57/0.97  
% 3.57/0.97  fof(f59,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f39])).
% 3.57/0.97  
% 3.57/0.97  fof(f1,axiom,(
% 3.57/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.57/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.57/0.97  
% 3.57/0.97  fof(f32,plain,(
% 3.57/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.97    inference(nnf_transformation,[],[f1])).
% 3.57/0.97  
% 3.57/0.97  fof(f33,plain,(
% 3.57/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.97    inference(rectify,[],[f32])).
% 3.57/0.97  
% 3.57/0.97  fof(f34,plain,(
% 3.57/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.57/0.97    introduced(choice_axiom,[])).
% 3.57/0.97  
% 3.57/0.97  fof(f35,plain,(
% 3.57/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.57/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.57/0.97  
% 3.57/0.97  fof(f54,plain,(
% 3.57/0.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f35])).
% 3.57/0.97  
% 3.57/0.97  fof(f75,plain,(
% 3.57/0.97    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f50])).
% 3.57/0.97  
% 3.57/0.97  fof(f70,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK3(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.57/0.97    inference(cnf_transformation,[],[f46])).
% 3.57/0.97  
% 3.57/0.97  fof(f80,plain,(
% 3.57/0.97    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f53])).
% 3.57/0.97  
% 3.57/0.97  fof(f62,plain,(
% 3.57/0.97    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.57/0.97    inference(cnf_transformation,[],[f41])).
% 3.57/0.97  
% 3.57/0.97  cnf(c_25,negated_conjecture,
% 3.57/0.97      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.57/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_1261,plain,
% 3.57/0.97      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.57/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_8,plain,
% 3.57/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.97      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.57/0.97      | ~ v1_funct_1(X1)
% 3.57/0.97      | ~ v1_relat_1(X1) ),
% 3.57/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.57/0.97  
% 3.57/0.97  cnf(c_26,negated_conjecture,
% 3.57/0.98      ( v1_funct_1(sK8) ),
% 3.57/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_321,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.57/0.98      | ~ v1_relat_1(X1)
% 3.57/0.98      | sK8 != X1 ),
% 3.57/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_322,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 3.57/0.98      | ~ v1_relat_1(sK8) ),
% 3.57/0.98      inference(unflattening,[status(thm)],[c_321]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1259,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 3.57/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_11,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | v1_relat_1(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1536,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.57/0.98      | v1_relat_1(sK8) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1563,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8)
% 3.57/0.98      | ~ r2_hidden(X0,k1_relat_1(sK8)) ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_322,c_25,c_1536]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1564,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_1563]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1565,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1650,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top
% 3.57/0.98      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1259,c_1565]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1651,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK8,X0)),sK8) = iProver_top ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_1650]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_17,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | ~ r2_hidden(k4_tarski(sK3(X1,X0),X3),X0)
% 3.57/0.98      | k1_relset_1(X1,X2,X0) = X1 ),
% 3.57/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1269,plain,
% 3.57/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(sK3(X0,X2),X3),X2) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4434,plain,
% 3.57/0.98      ( k1_relset_1(X0,X1,sK8) = X0
% 3.57/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.57/0.98      | r2_hidden(sK3(X0,sK8),k1_relat_1(sK8)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1651,c_1269]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4758,plain,
% 3.57/0.98      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.57/0.98      | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1261,c_4434]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_14,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1272,plain,
% 3.57/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1847,plain,
% 3.57/0.98      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1261,c_1272]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4759,plain,
% 3.57/0.98      ( k1_relat_1(sK8) = sK5
% 3.57/0.98      | r2_hidden(sK3(sK5,sK8),k1_relat_1(sK8)) != iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_4758,c_1847]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_28,plain,
% 3.57/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_24,negated_conjecture,
% 3.57/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_29,plain,
% 3.57/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1537,plain,
% 3.57/0.98      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.57/0.98      | v1_relat_1(sK8) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_792,plain,( X0 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1751,plain,
% 3.57/0.98      ( sK9 = sK9 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_792]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3,plain,
% 3.57/0.98      ( m1_subset_1(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.57/0.98      | ~ r2_hidden(X0,X2) ),
% 3.57/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1745,plain,
% 3.57/0.98      ( m1_subset_1(X0,sK6)
% 3.57/0.98      | ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,X1),k1_zfmisc_1(sK6))
% 3.57/0.98      | ~ r2_hidden(X0,k7_relset_1(sK5,sK6,sK8,X1)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1942,plain,
% 3.57/0.98      ( ~ m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.57/0.98      | m1_subset_1(sK9,sK6)
% 3.57/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1745]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1943,plain,
% 3.57/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) != iProver_top
% 3.57/0.98      | m1_subset_1(sK9,sK6) = iProver_top
% 3.57/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1942]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_15,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.57/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1634,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.57/0.98      | k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2087,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.57/0.98      | k7_relset_1(sK5,sK6,sK8,sK7) = k9_relat_1(sK8,sK7) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1634]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1262,plain,
% 3.57/0.98      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_22,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.57/0.98      | m1_subset_1(sK4(X4,X3,X2,X0),X3)
% 3.57/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.57/0.98      | v1_xboole_0(X1)
% 3.57/0.98      | v1_xboole_0(X3)
% 3.57/0.98      | v1_xboole_0(X4) ),
% 3.57/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1264,plain,
% 3.57/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.57/0.98      | m1_subset_1(sK4(X4,X3,X2,X0),X3) = iProver_top
% 3.57/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.57/0.98      | v1_xboole_0(X1) = iProver_top
% 3.57/0.98      | v1_xboole_0(X3) = iProver_top
% 3.57/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1766,plain,
% 3.57/0.98      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.57/0.98      | m1_subset_1(sK9,sK6) != iProver_top
% 3.57/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1262,c_1264]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2106,plain,
% 3.57/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.57/0.98      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1766,c_28]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2107,plain,
% 3.57/0.98      ( m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) = iProver_top
% 3.57/0.98      | m1_subset_1(sK9,sK6) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_2106]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_13,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.57/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1619,plain,
% 3.57/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,X0),k1_zfmisc_1(sK6))
% 3.57/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2151,plain,
% 3.57/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6))
% 3.57/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1619]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2152,plain,
% 3.57/0.98      ( m1_subset_1(k7_relset_1(sK5,sK6,sK8,sK7),k1_zfmisc_1(sK6)) = iProver_top
% 3.57/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2151]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_793,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1881,plain,
% 3.57/0.98      ( X0 != X1
% 3.57/0.98      | X0 = k7_relset_1(sK5,sK6,sK8,sK7)
% 3.57/0.98      | k7_relset_1(sK5,sK6,sK8,sK7) != X1 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_793]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2086,plain,
% 3.57/0.98      ( X0 = k7_relset_1(sK5,sK6,sK8,sK7)
% 3.57/0.98      | X0 != k9_relat_1(sK8,sK7)
% 3.57/0.98      | k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1881]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2157,plain,
% 3.57/0.98      ( k7_relset_1(sK5,sK6,sK8,sK7) != k9_relat_1(sK8,sK7)
% 3.57/0.98      | k9_relat_1(sK8,sK7) = k7_relset_1(sK5,sK6,sK8,sK7)
% 3.57/0.98      | k9_relat_1(sK8,sK7) != k9_relat_1(sK8,sK7) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_2086]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2158,plain,
% 3.57/0.98      ( k9_relat_1(sK8,sK7) = k9_relat_1(sK8,sK7) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_792]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_12,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | ~ v1_xboole_0(X2)
% 3.57/0.98      | v1_xboole_0(X0) ),
% 3.57/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1274,plain,
% 3.57/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.57/0.98      | v1_xboole_0(X2) != iProver_top
% 3.57/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2423,plain,
% 3.57/0.98      ( v1_xboole_0(sK6) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK8) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1261,c_1274]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_794,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.57/0.98      theory(equality) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1624,plain,
% 3.57/0.98      ( r2_hidden(X0,X1)
% 3.57/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.57/0.98      | X1 != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.57/0.98      | X0 != sK9 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_794]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1750,plain,
% 3.57/0.98      ( r2_hidden(sK9,X0)
% 3.57/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.57/0.98      | X0 != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.57/0.98      | sK9 != sK9 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1624]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2520,plain,
% 3.57/0.98      ( ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.57/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.57/0.98      | k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.57/0.98      | sK9 != sK9 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1750]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2521,plain,
% 3.57/0.98      ( k9_relat_1(sK8,sK7) != k7_relset_1(sK5,sK6,sK8,sK7)
% 3.57/0.98      | sK9 != sK9
% 3.57/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.57/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2520]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_21,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.57/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.57/0.98      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
% 3.57/0.98      | v1_xboole_0(X1)
% 3.57/0.98      | v1_xboole_0(X3)
% 3.57/0.98      | v1_xboole_0(X4) ),
% 3.57/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1265,plain,
% 3.57/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.57/0.98      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.57/0.98      | v1_xboole_0(X1) = iProver_top
% 3.57/0.98      | v1_xboole_0(X3) = iProver_top
% 3.57/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2271,plain,
% 3.57/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.57/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1262,c_1265]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2806,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK4(sK7,sK5,sK8,sK9),sK9),sK8) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_2271,c_28,c_29,c_1943,c_2152]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_9,plain,
% 3.57/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.57/0.98      | ~ v1_funct_1(X2)
% 3.57/0.98      | ~ v1_relat_1(X2)
% 3.57/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.57/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_336,plain,
% 3.57/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.57/0.98      | ~ v1_relat_1(X2)
% 3.57/0.98      | k1_funct_1(X2,X0) = X1
% 3.57/0.98      | sK8 != X2 ),
% 3.57/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_337,plain,
% 3.57/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.57/0.98      | ~ v1_relat_1(sK8)
% 3.57/0.98      | k1_funct_1(sK8,X0) = X1 ),
% 3.57/0.98      inference(unflattening,[status(thm)],[c_336]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1258,plain,
% 3.57/0.98      ( k1_funct_1(sK8,X0) = X1
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.57/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_338,plain,
% 3.57/0.98      ( k1_funct_1(sK8,X0) = X1
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.57/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1588,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.57/0.98      | k1_funct_1(sK8,X0) = X1 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1258,c_28,c_338,c_1537]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1589,plain,
% 3.57/0.98      ( k1_funct_1(sK8,X0) = X1
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_1588]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2816,plain,
% 3.57/0.98      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) = sK9
% 3.57/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2806,c_1589]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_5,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2900,plain,
% 3.57/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7)
% 3.57/0.98      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.57/0.98      | ~ v1_relat_1(sK8) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2901,plain,
% 3.57/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) = iProver_top
% 3.57/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.57/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2900]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_6,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.57/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2898,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.57/0.98      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 3.57/0.98      | ~ v1_relat_1(sK8) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2905,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top
% 3.57/0.98      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.57/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_2898]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1,plain,
% 3.57/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3782,plain,
% 3.57/0.98      ( ~ r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8)
% 3.57/0.98      | ~ v1_xboole_0(sK8) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3783,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_3782]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3910,plain,
% 3.57/0.98      ( ~ r2_hidden(sK1(sK9,sK7,sK8),sK7) | ~ v1_xboole_0(sK7) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3911,plain,
% 3.57/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),sK7) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_3910]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_20,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,X1)
% 3.57/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.57/0.98      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.57/0.98      | r2_hidden(sK4(X4,X3,X2,X0),X4)
% 3.57/0.98      | v1_xboole_0(X1)
% 3.57/0.98      | v1_xboole_0(X3)
% 3.57/0.98      | v1_xboole_0(X4) ),
% 3.57/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4103,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK9,sK6)
% 3.57/0.98      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.57/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.57/0.98      | ~ r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
% 3.57/0.98      | v1_xboole_0(sK6)
% 3.57/0.98      | v1_xboole_0(sK5)
% 3.57/0.98      | v1_xboole_0(sK7) ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4104,plain,
% 3.57/0.98      ( m1_subset_1(sK9,sK6) != iProver_top
% 3.57/0.98      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.57/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) = iProver_top
% 3.57/0.98      | r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) != iProver_top
% 3.57/0.98      | v1_xboole_0(sK6) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.57/0.98      | v1_xboole_0(sK7) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_4103]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_18,plain,
% 3.57/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.57/0.98      | r2_hidden(sK3(X1,X0),X1)
% 3.57/0.98      | k1_relset_1(X1,X2,X0) = X1 ),
% 3.57/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1268,plain,
% 3.57/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.57/0.98      | r2_hidden(sK3(X0,X2),X0) = iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3330,plain,
% 3.57/0.98      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.57/0.98      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1261,c_1268]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3333,plain,
% 3.57/0.98      ( k1_relat_1(sK8) = sK5
% 3.57/0.98      | r2_hidden(sK3(sK5,sK8),sK5) = iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_3330,c_1847]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1282,plain,
% 3.57/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.57/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4120,plain,
% 3.57/0.98      ( k1_relat_1(sK8) = sK5 | v1_xboole_0(sK5) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3333,c_1282]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_23,negated_conjecture,
% 3.57/0.98      ( ~ m1_subset_1(X0,sK5)
% 3.57/0.98      | ~ r2_hidden(X0,sK7)
% 3.57/0.98      | k1_funct_1(sK8,X0) != sK9 ),
% 3.57/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4707,plain,
% 3.57/0.98      ( ~ m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5)
% 3.57/0.98      | ~ r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7)
% 3.57/0.98      | k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9 ),
% 3.57/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4708,plain,
% 3.57/0.98      ( k1_funct_1(sK8,sK4(sK7,sK5,sK8,sK9)) != sK9
% 3.57/0.98      | m1_subset_1(sK4(sK7,sK5,sK8,sK9),sK5) != iProver_top
% 3.57/0.98      | r2_hidden(sK4(sK7,sK5,sK8,sK9),sK7) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_4707]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4943,plain,
% 3.57/0.98      ( k1_relat_1(sK8) = sK5 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_4759,c_25,c_28,c_29,c_1537,c_1751,c_1943,c_2087,
% 3.57/0.98                 c_2107,c_2152,c_2157,c_2158,c_2423,c_2521,c_2816,c_2901,
% 3.57/0.98                 c_2905,c_3783,c_3911,c_4104,c_4120,c_4708]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1271,plain,
% 3.57/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.57/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2305,plain,
% 3.57/0.98      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1261,c_1271]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_2548,plain,
% 3.57/0.98      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_2305,c_1262]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1277,plain,
% 3.57/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.57/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3477,plain,
% 3.57/0.98      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.57/0.98      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.57/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_1277,c_1589]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3823,plain,
% 3.57/0.98      ( r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.57/0.98      | k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0 ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3477,c_28,c_1537]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3824,plain,
% 3.57/0.98      ( k1_funct_1(sK8,sK1(X0,X1,sK8)) = X0
% 3.57/0.98      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_3823]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3834,plain,
% 3.57/0.98      ( k1_funct_1(sK8,sK1(sK9,sK7,sK8)) = sK9 ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_2548,c_3824]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3863,plain,
% 3.57/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) != iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3834,c_1651]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3969,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(sK1(sK9,sK7,sK8),sK9),sK8) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_3863,c_25,c_28,c_29,c_1537,c_1751,c_2087,c_2157,
% 3.57/0.98                 c_2158,c_2521,c_2905]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_10,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.57/0.98      | ~ v1_funct_1(X1)
% 3.57/0.98      | ~ v1_relat_1(X1) ),
% 3.57/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_306,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(X1))
% 3.57/0.98      | ~ r2_hidden(k4_tarski(X0,X2),X1)
% 3.57/0.98      | ~ v1_relat_1(X1)
% 3.57/0.98      | sK8 != X1 ),
% 3.57/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_307,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.57/0.98      | ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.57/0.98      | ~ v1_relat_1(sK8) ),
% 3.57/0.98      inference(unflattening,[status(thm)],[c_306]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1260,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.57/0.98      | v1_relat_1(sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1544,plain,
% 3.57/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK8)
% 3.57/0.98      | r2_hidden(X0,k1_relat_1(sK8)) ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_307,c_25,c_1536]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1545,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8))
% 3.57/0.98      | ~ r2_hidden(k4_tarski(X0,X1),sK8) ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_1544]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1546,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.57/0.98      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1643,plain,
% 3.57/0.98      ( r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top
% 3.57/0.98      | r2_hidden(X0,k1_relat_1(sK8)) = iProver_top ),
% 3.57/0.98      inference(global_propositional_subsumption,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_1260,c_1546]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_1644,plain,
% 3.57/0.98      ( r2_hidden(X0,k1_relat_1(sK8)) = iProver_top
% 3.57/0.98      | r2_hidden(k4_tarski(X0,X1),sK8) != iProver_top ),
% 3.57/0.98      inference(renaming,[status(thm)],[c_1643]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_3975,plain,
% 3.57/0.98      ( r2_hidden(sK1(sK9,sK7,sK8),k1_relat_1(sK8)) = iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3969,c_1644]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4112,plain,
% 3.57/0.98      ( v1_xboole_0(k1_relat_1(sK8)) != iProver_top ),
% 3.57/0.98      inference(superposition,[status(thm)],[c_3975,c_1282]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(c_4947,plain,
% 3.57/0.98      ( v1_xboole_0(sK5) != iProver_top ),
% 3.57/0.98      inference(demodulation,[status(thm)],[c_4943,c_4112]) ).
% 3.57/0.98  
% 3.57/0.98  cnf(contradiction,plain,
% 3.57/0.98      ( $false ),
% 3.57/0.98      inference(minisat,
% 3.57/0.98                [status(thm)],
% 3.57/0.98                [c_4947,c_4708,c_4104,c_3911,c_3783,c_2905,c_2901,c_2816,
% 3.57/0.98                 c_2521,c_2423,c_2158,c_2157,c_2152,c_2107,c_2087,c_1943,
% 3.57/0.98                 c_1751,c_1537,c_29,c_28,c_25]) ).
% 3.57/0.98  
% 3.57/0.98  
% 3.57/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/0.98  
% 3.57/0.98  ------                               Statistics
% 3.57/0.98  
% 3.57/0.98  ------ Selected
% 3.57/0.98  
% 3.57/0.98  total_time:                             0.175
% 3.57/0.98  
%------------------------------------------------------------------------------
