%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:54 EST 2020

% Result     : Theorem 7.36s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 791 expanded)
%              Number of clauses        :   91 ( 217 expanded)
%              Number of leaves         :   22 ( 184 expanded)
%              Depth                    :   22
%              Number of atoms          :  507 (2769 expanded)
%              Number of equality atoms :  221 ( 944 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f46,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4)))
      & k1_xboole_0 != sK5
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4)))
    & k1_xboole_0 != sK5
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f32,f46])).

fof(f75,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f79])).

fof(f86,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5))) ),
    inference(definition_unfolding,[],[f76,f80])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f90,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f55,f80,f80])).

fof(f78,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4))) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) ),
    inference(definition_unfolding,[],[f78,f80,f80])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f71,f80,f80])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_15,plain,
    ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_387,plain,
    ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1,X2),X2)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_27])).

cnf(c_388,plain,
    ( r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7))
    | r2_hidden(sK1(sK7,X0,X1),X1)
    | ~ v1_relat_1(sK7)
    | k9_relat_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_1726,plain,
    ( k9_relat_1(sK7,X0) = X1
    | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_389,plain,
    ( k9_relat_1(sK7,X0) = X1
    | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_307,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_308,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_1729,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_1997,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1729])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2000,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2001,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2000])).

cnf(c_2387,plain,
    ( r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
    | k9_relat_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1726,c_389,c_1997,c_2001])).

cnf(c_2388,plain,
    ( k9_relat_1(sK7,X0) = X1
    | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2387])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_441,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1723,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_443,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_2188,plain,
    ( r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_443,c_1997,c_2001])).

cnf(c_2189,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2188])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1737,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_498,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_499,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1720,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1731,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2120,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r1_tarski(X1,sK3(sK7,X1,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_1731])).

cnf(c_2519,plain,
    ( r1_tarski(X1,sK3(sK7,X1,X0)) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2120,c_1997,c_2001])).

cnf(c_2520,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r1_tarski(X1,sK3(sK7,X1,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2519])).

cnf(c_2525,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1737,c_2520])).

cnf(c_3445,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2189,c_2525])).

cnf(c_719,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_21])).

cnf(c_720,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_719])).

cnf(c_721,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_3586,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_721])).

cnf(c_3592,plain,
    ( k9_relat_1(sK7,X0) = k1_xboole_0
    | r2_hidden(sK2(sK7,X0,k1_xboole_0),k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2388,c_3586])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_331,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_332,plain,
    ( v4_relat_1(sK7,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_353,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_332])).

cnf(c_354,plain,
    ( r1_tarski(k1_relat_1(sK7),X0)
    | ~ v1_relat_1(sK7)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_1728,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK7),X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_355,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK7),X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_2627,plain,
    ( r1_tarski(k1_relat_1(sK7),X0) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_355,c_1997,c_2001])).

cnf(c_2628,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK7),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2627])).

cnf(c_2633,plain,
    ( r1_tarski(k1_relat_1(sK7),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2628])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1734,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9967,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_relat_1(sK7)
    | k1_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2633,c_1734])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_322,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_323,plain,
    ( k7_relset_1(X0,X1,sK7,X2) = k9_relat_1(sK7,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_1794,plain,
    ( k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,X0) = k9_relat_1(sK7,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1849,plain,
    ( k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) = k9_relat_1(sK7,sK6)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_1351,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1798,plain,
    ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_zfmisc_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_1883,plain,
    ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_1998,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
    | v1_relat_1(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1997])).

cnf(c_1345,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2003,plain,
    ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_372,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_373,plain,
    ( ~ v1_relat_1(sK7)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7)
    | k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_1727,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7)
    | k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7)
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_2281,plain,
    ( k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1727,c_373,c_1998,c_2000])).

cnf(c_2282,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7)
    | k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7) ),
    inference(renaming,[status(thm)],[c_2281])).

cnf(c_2283,plain,
    ( k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7)
    | k2_enumset1(sK4,sK4,sK4,sK4) != k1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(c_11,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4721,plain,
    ( r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1347,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1780,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))
    | k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) != X0
    | k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_1850,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))
    | ~ r1_tarski(k9_relat_1(sK7,sK6),X0)
    | k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
    | k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_5537,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))
    | ~ r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7))
    | k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
    | k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_9971,plain,
    ( k1_relat_1(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9967,c_24,c_1849,c_1883,c_1998,c_2000,c_2003,c_2283,c_4721,c_5537])).

cnf(c_14126,plain,
    ( k9_relat_1(sK7,X0) = k1_xboole_0
    | r2_hidden(sK2(sK7,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3592,c_9971])).

cnf(c_14132,plain,
    ( k9_relat_1(sK7,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14126,c_3586])).

cnf(c_1730,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1800,plain,
    ( k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(equality_resolution,[status(thm)],[c_323])).

cnf(c_1845,plain,
    ( r1_tarski(k9_relat_1(sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1730,c_1800])).

cnf(c_21975,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14132,c_1845])).

cnf(c_1974,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1975,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21975,c_1975])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:43:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.36/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.36/1.49  
% 7.36/1.49  ------  iProver source info
% 7.36/1.49  
% 7.36/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.36/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.36/1.49  git: non_committed_changes: false
% 7.36/1.49  git: last_make_outside_of_git: false
% 7.36/1.49  
% 7.36/1.49  ------ 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options
% 7.36/1.49  
% 7.36/1.49  --out_options                           all
% 7.36/1.49  --tptp_safe_out                         true
% 7.36/1.49  --problem_path                          ""
% 7.36/1.49  --include_path                          ""
% 7.36/1.49  --clausifier                            res/vclausify_rel
% 7.36/1.49  --clausifier_options                    ""
% 7.36/1.49  --stdin                                 false
% 7.36/1.49  --stats_out                             all
% 7.36/1.49  
% 7.36/1.49  ------ General Options
% 7.36/1.49  
% 7.36/1.49  --fof                                   false
% 7.36/1.49  --time_out_real                         305.
% 7.36/1.49  --time_out_virtual                      -1.
% 7.36/1.49  --symbol_type_check                     false
% 7.36/1.49  --clausify_out                          false
% 7.36/1.49  --sig_cnt_out                           false
% 7.36/1.49  --trig_cnt_out                          false
% 7.36/1.49  --trig_cnt_out_tolerance                1.
% 7.36/1.49  --trig_cnt_out_sk_spl                   false
% 7.36/1.49  --abstr_cl_out                          false
% 7.36/1.49  
% 7.36/1.49  ------ Global Options
% 7.36/1.49  
% 7.36/1.49  --schedule                              default
% 7.36/1.49  --add_important_lit                     false
% 7.36/1.49  --prop_solver_per_cl                    1000
% 7.36/1.49  --min_unsat_core                        false
% 7.36/1.49  --soft_assumptions                      false
% 7.36/1.49  --soft_lemma_size                       3
% 7.36/1.49  --prop_impl_unit_size                   0
% 7.36/1.49  --prop_impl_unit                        []
% 7.36/1.49  --share_sel_clauses                     true
% 7.36/1.49  --reset_solvers                         false
% 7.36/1.49  --bc_imp_inh                            [conj_cone]
% 7.36/1.49  --conj_cone_tolerance                   3.
% 7.36/1.49  --extra_neg_conj                        none
% 7.36/1.49  --large_theory_mode                     true
% 7.36/1.49  --prolific_symb_bound                   200
% 7.36/1.49  --lt_threshold                          2000
% 7.36/1.49  --clause_weak_htbl                      true
% 7.36/1.49  --gc_record_bc_elim                     false
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing Options
% 7.36/1.49  
% 7.36/1.49  --preprocessing_flag                    true
% 7.36/1.49  --time_out_prep_mult                    0.1
% 7.36/1.49  --splitting_mode                        input
% 7.36/1.49  --splitting_grd                         true
% 7.36/1.49  --splitting_cvd                         false
% 7.36/1.49  --splitting_cvd_svl                     false
% 7.36/1.49  --splitting_nvd                         32
% 7.36/1.49  --sub_typing                            true
% 7.36/1.49  --prep_gs_sim                           true
% 7.36/1.49  --prep_unflatten                        true
% 7.36/1.49  --prep_res_sim                          true
% 7.36/1.49  --prep_upred                            true
% 7.36/1.49  --prep_sem_filter                       exhaustive
% 7.36/1.49  --prep_sem_filter_out                   false
% 7.36/1.49  --pred_elim                             true
% 7.36/1.49  --res_sim_input                         true
% 7.36/1.49  --eq_ax_congr_red                       true
% 7.36/1.49  --pure_diseq_elim                       true
% 7.36/1.49  --brand_transform                       false
% 7.36/1.49  --non_eq_to_eq                          false
% 7.36/1.49  --prep_def_merge                        true
% 7.36/1.49  --prep_def_merge_prop_impl              false
% 7.36/1.49  --prep_def_merge_mbd                    true
% 7.36/1.49  --prep_def_merge_tr_red                 false
% 7.36/1.49  --prep_def_merge_tr_cl                  false
% 7.36/1.49  --smt_preprocessing                     true
% 7.36/1.49  --smt_ac_axioms                         fast
% 7.36/1.49  --preprocessed_out                      false
% 7.36/1.49  --preprocessed_stats                    false
% 7.36/1.49  
% 7.36/1.49  ------ Abstraction refinement Options
% 7.36/1.49  
% 7.36/1.49  --abstr_ref                             []
% 7.36/1.49  --abstr_ref_prep                        false
% 7.36/1.49  --abstr_ref_until_sat                   false
% 7.36/1.49  --abstr_ref_sig_restrict                funpre
% 7.36/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.49  --abstr_ref_under                       []
% 7.36/1.49  
% 7.36/1.49  ------ SAT Options
% 7.36/1.49  
% 7.36/1.49  --sat_mode                              false
% 7.36/1.49  --sat_fm_restart_options                ""
% 7.36/1.49  --sat_gr_def                            false
% 7.36/1.49  --sat_epr_types                         true
% 7.36/1.49  --sat_non_cyclic_types                  false
% 7.36/1.49  --sat_finite_models                     false
% 7.36/1.49  --sat_fm_lemmas                         false
% 7.36/1.49  --sat_fm_prep                           false
% 7.36/1.49  --sat_fm_uc_incr                        true
% 7.36/1.49  --sat_out_model                         small
% 7.36/1.49  --sat_out_clauses                       false
% 7.36/1.49  
% 7.36/1.49  ------ QBF Options
% 7.36/1.49  
% 7.36/1.49  --qbf_mode                              false
% 7.36/1.49  --qbf_elim_univ                         false
% 7.36/1.49  --qbf_dom_inst                          none
% 7.36/1.49  --qbf_dom_pre_inst                      false
% 7.36/1.49  --qbf_sk_in                             false
% 7.36/1.49  --qbf_pred_elim                         true
% 7.36/1.49  --qbf_split                             512
% 7.36/1.49  
% 7.36/1.49  ------ BMC1 Options
% 7.36/1.49  
% 7.36/1.49  --bmc1_incremental                      false
% 7.36/1.49  --bmc1_axioms                           reachable_all
% 7.36/1.49  --bmc1_min_bound                        0
% 7.36/1.49  --bmc1_max_bound                        -1
% 7.36/1.49  --bmc1_max_bound_default                -1
% 7.36/1.49  --bmc1_symbol_reachability              true
% 7.36/1.49  --bmc1_property_lemmas                  false
% 7.36/1.49  --bmc1_k_induction                      false
% 7.36/1.49  --bmc1_non_equiv_states                 false
% 7.36/1.49  --bmc1_deadlock                         false
% 7.36/1.49  --bmc1_ucm                              false
% 7.36/1.49  --bmc1_add_unsat_core                   none
% 7.36/1.49  --bmc1_unsat_core_children              false
% 7.36/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.49  --bmc1_out_stat                         full
% 7.36/1.49  --bmc1_ground_init                      false
% 7.36/1.49  --bmc1_pre_inst_next_state              false
% 7.36/1.49  --bmc1_pre_inst_state                   false
% 7.36/1.49  --bmc1_pre_inst_reach_state             false
% 7.36/1.49  --bmc1_out_unsat_core                   false
% 7.36/1.49  --bmc1_aig_witness_out                  false
% 7.36/1.49  --bmc1_verbose                          false
% 7.36/1.49  --bmc1_dump_clauses_tptp                false
% 7.36/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.49  --bmc1_dump_file                        -
% 7.36/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.49  --bmc1_ucm_extend_mode                  1
% 7.36/1.49  --bmc1_ucm_init_mode                    2
% 7.36/1.49  --bmc1_ucm_cone_mode                    none
% 7.36/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.49  --bmc1_ucm_relax_model                  4
% 7.36/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.49  --bmc1_ucm_layered_model                none
% 7.36/1.49  --bmc1_ucm_max_lemma_size               10
% 7.36/1.49  
% 7.36/1.49  ------ AIG Options
% 7.36/1.49  
% 7.36/1.49  --aig_mode                              false
% 7.36/1.49  
% 7.36/1.49  ------ Instantiation Options
% 7.36/1.49  
% 7.36/1.49  --instantiation_flag                    true
% 7.36/1.49  --inst_sos_flag                         true
% 7.36/1.49  --inst_sos_phase                        true
% 7.36/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel_side                     num_symb
% 7.36/1.49  --inst_solver_per_active                1400
% 7.36/1.49  --inst_solver_calls_frac                1.
% 7.36/1.49  --inst_passive_queue_type               priority_queues
% 7.36/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.49  --inst_passive_queues_freq              [25;2]
% 7.36/1.49  --inst_dismatching                      true
% 7.36/1.49  --inst_eager_unprocessed_to_passive     true
% 7.36/1.49  --inst_prop_sim_given                   true
% 7.36/1.49  --inst_prop_sim_new                     false
% 7.36/1.49  --inst_subs_new                         false
% 7.36/1.49  --inst_eq_res_simp                      false
% 7.36/1.49  --inst_subs_given                       false
% 7.36/1.49  --inst_orphan_elimination               true
% 7.36/1.49  --inst_learning_loop_flag               true
% 7.36/1.49  --inst_learning_start                   3000
% 7.36/1.49  --inst_learning_factor                  2
% 7.36/1.49  --inst_start_prop_sim_after_learn       3
% 7.36/1.49  --inst_sel_renew                        solver
% 7.36/1.49  --inst_lit_activity_flag                true
% 7.36/1.49  --inst_restr_to_given                   false
% 7.36/1.49  --inst_activity_threshold               500
% 7.36/1.49  --inst_out_proof                        true
% 7.36/1.49  
% 7.36/1.49  ------ Resolution Options
% 7.36/1.49  
% 7.36/1.49  --resolution_flag                       true
% 7.36/1.49  --res_lit_sel                           adaptive
% 7.36/1.49  --res_lit_sel_side                      none
% 7.36/1.49  --res_ordering                          kbo
% 7.36/1.49  --res_to_prop_solver                    active
% 7.36/1.49  --res_prop_simpl_new                    false
% 7.36/1.49  --res_prop_simpl_given                  true
% 7.36/1.49  --res_passive_queue_type                priority_queues
% 7.36/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.49  --res_passive_queues_freq               [15;5]
% 7.36/1.49  --res_forward_subs                      full
% 7.36/1.49  --res_backward_subs                     full
% 7.36/1.49  --res_forward_subs_resolution           true
% 7.36/1.49  --res_backward_subs_resolution          true
% 7.36/1.49  --res_orphan_elimination                true
% 7.36/1.49  --res_time_limit                        2.
% 7.36/1.49  --res_out_proof                         true
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Options
% 7.36/1.49  
% 7.36/1.49  --superposition_flag                    true
% 7.36/1.49  --sup_passive_queue_type                priority_queues
% 7.36/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.49  --demod_completeness_check              fast
% 7.36/1.49  --demod_use_ground                      true
% 7.36/1.49  --sup_to_prop_solver                    passive
% 7.36/1.49  --sup_prop_simpl_new                    true
% 7.36/1.49  --sup_prop_simpl_given                  true
% 7.36/1.49  --sup_fun_splitting                     true
% 7.36/1.49  --sup_smt_interval                      50000
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Simplification Setup
% 7.36/1.49  
% 7.36/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_immed_triv                        [TrivRules]
% 7.36/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_bw_main                     []
% 7.36/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_input_bw                          []
% 7.36/1.49  
% 7.36/1.49  ------ Combination Options
% 7.36/1.49  
% 7.36/1.49  --comb_res_mult                         3
% 7.36/1.49  --comb_sup_mult                         2
% 7.36/1.49  --comb_inst_mult                        10
% 7.36/1.49  
% 7.36/1.49  ------ Debug Options
% 7.36/1.49  
% 7.36/1.49  --dbg_backtrace                         false
% 7.36/1.49  --dbg_dump_prop_clauses                 false
% 7.36/1.49  --dbg_dump_prop_clauses_file            -
% 7.36/1.49  --dbg_out_stat                          false
% 7.36/1.49  ------ Parsing...
% 7.36/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.36/1.49  ------ Proving...
% 7.36/1.49  ------ Problem Properties 
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  clauses                                 24
% 7.36/1.49  conjectures                             2
% 7.36/1.49  EPR                                     4
% 7.36/1.49  Horn                                    19
% 7.36/1.49  unary                                   6
% 7.36/1.49  binary                                  5
% 7.36/1.49  lits                                    62
% 7.36/1.49  lits eq                                 16
% 7.36/1.49  fd_pure                                 0
% 7.36/1.49  fd_pseudo                               0
% 7.36/1.49  fd_cond                                 0
% 7.36/1.49  fd_pseudo_cond                          5
% 7.36/1.49  AC symbols                              0
% 7.36/1.49  
% 7.36/1.49  ------ Schedule dynamic 5 is on 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  ------ 
% 7.36/1.49  Current options:
% 7.36/1.49  ------ 
% 7.36/1.49  
% 7.36/1.49  ------ Input Options
% 7.36/1.49  
% 7.36/1.49  --out_options                           all
% 7.36/1.49  --tptp_safe_out                         true
% 7.36/1.49  --problem_path                          ""
% 7.36/1.49  --include_path                          ""
% 7.36/1.49  --clausifier                            res/vclausify_rel
% 7.36/1.49  --clausifier_options                    ""
% 7.36/1.49  --stdin                                 false
% 7.36/1.49  --stats_out                             all
% 7.36/1.49  
% 7.36/1.49  ------ General Options
% 7.36/1.49  
% 7.36/1.49  --fof                                   false
% 7.36/1.49  --time_out_real                         305.
% 7.36/1.49  --time_out_virtual                      -1.
% 7.36/1.49  --symbol_type_check                     false
% 7.36/1.49  --clausify_out                          false
% 7.36/1.49  --sig_cnt_out                           false
% 7.36/1.49  --trig_cnt_out                          false
% 7.36/1.49  --trig_cnt_out_tolerance                1.
% 7.36/1.49  --trig_cnt_out_sk_spl                   false
% 7.36/1.49  --abstr_cl_out                          false
% 7.36/1.49  
% 7.36/1.49  ------ Global Options
% 7.36/1.49  
% 7.36/1.49  --schedule                              default
% 7.36/1.49  --add_important_lit                     false
% 7.36/1.49  --prop_solver_per_cl                    1000
% 7.36/1.49  --min_unsat_core                        false
% 7.36/1.49  --soft_assumptions                      false
% 7.36/1.49  --soft_lemma_size                       3
% 7.36/1.49  --prop_impl_unit_size                   0
% 7.36/1.49  --prop_impl_unit                        []
% 7.36/1.49  --share_sel_clauses                     true
% 7.36/1.49  --reset_solvers                         false
% 7.36/1.49  --bc_imp_inh                            [conj_cone]
% 7.36/1.49  --conj_cone_tolerance                   3.
% 7.36/1.49  --extra_neg_conj                        none
% 7.36/1.49  --large_theory_mode                     true
% 7.36/1.49  --prolific_symb_bound                   200
% 7.36/1.49  --lt_threshold                          2000
% 7.36/1.49  --clause_weak_htbl                      true
% 7.36/1.49  --gc_record_bc_elim                     false
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing Options
% 7.36/1.49  
% 7.36/1.49  --preprocessing_flag                    true
% 7.36/1.49  --time_out_prep_mult                    0.1
% 7.36/1.49  --splitting_mode                        input
% 7.36/1.49  --splitting_grd                         true
% 7.36/1.49  --splitting_cvd                         false
% 7.36/1.49  --splitting_cvd_svl                     false
% 7.36/1.49  --splitting_nvd                         32
% 7.36/1.49  --sub_typing                            true
% 7.36/1.49  --prep_gs_sim                           true
% 7.36/1.49  --prep_unflatten                        true
% 7.36/1.49  --prep_res_sim                          true
% 7.36/1.49  --prep_upred                            true
% 7.36/1.49  --prep_sem_filter                       exhaustive
% 7.36/1.49  --prep_sem_filter_out                   false
% 7.36/1.49  --pred_elim                             true
% 7.36/1.49  --res_sim_input                         true
% 7.36/1.49  --eq_ax_congr_red                       true
% 7.36/1.49  --pure_diseq_elim                       true
% 7.36/1.49  --brand_transform                       false
% 7.36/1.49  --non_eq_to_eq                          false
% 7.36/1.49  --prep_def_merge                        true
% 7.36/1.49  --prep_def_merge_prop_impl              false
% 7.36/1.49  --prep_def_merge_mbd                    true
% 7.36/1.49  --prep_def_merge_tr_red                 false
% 7.36/1.49  --prep_def_merge_tr_cl                  false
% 7.36/1.49  --smt_preprocessing                     true
% 7.36/1.49  --smt_ac_axioms                         fast
% 7.36/1.49  --preprocessed_out                      false
% 7.36/1.49  --preprocessed_stats                    false
% 7.36/1.49  
% 7.36/1.49  ------ Abstraction refinement Options
% 7.36/1.49  
% 7.36/1.49  --abstr_ref                             []
% 7.36/1.49  --abstr_ref_prep                        false
% 7.36/1.49  --abstr_ref_until_sat                   false
% 7.36/1.49  --abstr_ref_sig_restrict                funpre
% 7.36/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.36/1.49  --abstr_ref_under                       []
% 7.36/1.49  
% 7.36/1.49  ------ SAT Options
% 7.36/1.49  
% 7.36/1.49  --sat_mode                              false
% 7.36/1.49  --sat_fm_restart_options                ""
% 7.36/1.49  --sat_gr_def                            false
% 7.36/1.49  --sat_epr_types                         true
% 7.36/1.49  --sat_non_cyclic_types                  false
% 7.36/1.49  --sat_finite_models                     false
% 7.36/1.49  --sat_fm_lemmas                         false
% 7.36/1.49  --sat_fm_prep                           false
% 7.36/1.49  --sat_fm_uc_incr                        true
% 7.36/1.49  --sat_out_model                         small
% 7.36/1.49  --sat_out_clauses                       false
% 7.36/1.49  
% 7.36/1.49  ------ QBF Options
% 7.36/1.49  
% 7.36/1.49  --qbf_mode                              false
% 7.36/1.49  --qbf_elim_univ                         false
% 7.36/1.49  --qbf_dom_inst                          none
% 7.36/1.49  --qbf_dom_pre_inst                      false
% 7.36/1.49  --qbf_sk_in                             false
% 7.36/1.49  --qbf_pred_elim                         true
% 7.36/1.49  --qbf_split                             512
% 7.36/1.49  
% 7.36/1.49  ------ BMC1 Options
% 7.36/1.49  
% 7.36/1.49  --bmc1_incremental                      false
% 7.36/1.49  --bmc1_axioms                           reachable_all
% 7.36/1.49  --bmc1_min_bound                        0
% 7.36/1.49  --bmc1_max_bound                        -1
% 7.36/1.49  --bmc1_max_bound_default                -1
% 7.36/1.49  --bmc1_symbol_reachability              true
% 7.36/1.49  --bmc1_property_lemmas                  false
% 7.36/1.49  --bmc1_k_induction                      false
% 7.36/1.49  --bmc1_non_equiv_states                 false
% 7.36/1.49  --bmc1_deadlock                         false
% 7.36/1.49  --bmc1_ucm                              false
% 7.36/1.49  --bmc1_add_unsat_core                   none
% 7.36/1.49  --bmc1_unsat_core_children              false
% 7.36/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.36/1.49  --bmc1_out_stat                         full
% 7.36/1.49  --bmc1_ground_init                      false
% 7.36/1.49  --bmc1_pre_inst_next_state              false
% 7.36/1.49  --bmc1_pre_inst_state                   false
% 7.36/1.49  --bmc1_pre_inst_reach_state             false
% 7.36/1.49  --bmc1_out_unsat_core                   false
% 7.36/1.49  --bmc1_aig_witness_out                  false
% 7.36/1.49  --bmc1_verbose                          false
% 7.36/1.49  --bmc1_dump_clauses_tptp                false
% 7.36/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.36/1.49  --bmc1_dump_file                        -
% 7.36/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.36/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.36/1.49  --bmc1_ucm_extend_mode                  1
% 7.36/1.49  --bmc1_ucm_init_mode                    2
% 7.36/1.49  --bmc1_ucm_cone_mode                    none
% 7.36/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.36/1.49  --bmc1_ucm_relax_model                  4
% 7.36/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.36/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.36/1.49  --bmc1_ucm_layered_model                none
% 7.36/1.49  --bmc1_ucm_max_lemma_size               10
% 7.36/1.49  
% 7.36/1.49  ------ AIG Options
% 7.36/1.49  
% 7.36/1.49  --aig_mode                              false
% 7.36/1.49  
% 7.36/1.49  ------ Instantiation Options
% 7.36/1.49  
% 7.36/1.49  --instantiation_flag                    true
% 7.36/1.49  --inst_sos_flag                         true
% 7.36/1.49  --inst_sos_phase                        true
% 7.36/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.36/1.49  --inst_lit_sel_side                     none
% 7.36/1.49  --inst_solver_per_active                1400
% 7.36/1.49  --inst_solver_calls_frac                1.
% 7.36/1.49  --inst_passive_queue_type               priority_queues
% 7.36/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.36/1.49  --inst_passive_queues_freq              [25;2]
% 7.36/1.49  --inst_dismatching                      true
% 7.36/1.49  --inst_eager_unprocessed_to_passive     true
% 7.36/1.49  --inst_prop_sim_given                   true
% 7.36/1.49  --inst_prop_sim_new                     false
% 7.36/1.49  --inst_subs_new                         false
% 7.36/1.49  --inst_eq_res_simp                      false
% 7.36/1.49  --inst_subs_given                       false
% 7.36/1.49  --inst_orphan_elimination               true
% 7.36/1.49  --inst_learning_loop_flag               true
% 7.36/1.49  --inst_learning_start                   3000
% 7.36/1.49  --inst_learning_factor                  2
% 7.36/1.49  --inst_start_prop_sim_after_learn       3
% 7.36/1.49  --inst_sel_renew                        solver
% 7.36/1.49  --inst_lit_activity_flag                true
% 7.36/1.49  --inst_restr_to_given                   false
% 7.36/1.49  --inst_activity_threshold               500
% 7.36/1.49  --inst_out_proof                        true
% 7.36/1.49  
% 7.36/1.49  ------ Resolution Options
% 7.36/1.49  
% 7.36/1.49  --resolution_flag                       false
% 7.36/1.49  --res_lit_sel                           adaptive
% 7.36/1.49  --res_lit_sel_side                      none
% 7.36/1.49  --res_ordering                          kbo
% 7.36/1.49  --res_to_prop_solver                    active
% 7.36/1.49  --res_prop_simpl_new                    false
% 7.36/1.49  --res_prop_simpl_given                  true
% 7.36/1.49  --res_passive_queue_type                priority_queues
% 7.36/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.36/1.49  --res_passive_queues_freq               [15;5]
% 7.36/1.49  --res_forward_subs                      full
% 7.36/1.49  --res_backward_subs                     full
% 7.36/1.49  --res_forward_subs_resolution           true
% 7.36/1.49  --res_backward_subs_resolution          true
% 7.36/1.49  --res_orphan_elimination                true
% 7.36/1.49  --res_time_limit                        2.
% 7.36/1.49  --res_out_proof                         true
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Options
% 7.36/1.49  
% 7.36/1.49  --superposition_flag                    true
% 7.36/1.49  --sup_passive_queue_type                priority_queues
% 7.36/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.36/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.36/1.49  --demod_completeness_check              fast
% 7.36/1.49  --demod_use_ground                      true
% 7.36/1.49  --sup_to_prop_solver                    passive
% 7.36/1.49  --sup_prop_simpl_new                    true
% 7.36/1.49  --sup_prop_simpl_given                  true
% 7.36/1.49  --sup_fun_splitting                     true
% 7.36/1.49  --sup_smt_interval                      50000
% 7.36/1.49  
% 7.36/1.49  ------ Superposition Simplification Setup
% 7.36/1.49  
% 7.36/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.36/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.36/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.36/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.36/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_immed_triv                        [TrivRules]
% 7.36/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_immed_bw_main                     []
% 7.36/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.36/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.36/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.36/1.49  --sup_input_bw                          []
% 7.36/1.49  
% 7.36/1.49  ------ Combination Options
% 7.36/1.49  
% 7.36/1.49  --comb_res_mult                         3
% 7.36/1.49  --comb_sup_mult                         2
% 7.36/1.49  --comb_inst_mult                        10
% 7.36/1.49  
% 7.36/1.49  ------ Debug Options
% 7.36/1.49  
% 7.36/1.49  --dbg_backtrace                         false
% 7.36/1.49  --dbg_dump_prop_clauses                 false
% 7.36/1.49  --dbg_dump_prop_clauses_file            -
% 7.36/1.49  --dbg_out_stat                          false
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  ------ Proving...
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  % SZS status Theorem for theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  fof(f11,axiom,(
% 7.36/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f24,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.36/1.49    inference(ennf_transformation,[],[f11])).
% 7.36/1.49  
% 7.36/1.49  fof(f25,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(flattening,[],[f24])).
% 7.36/1.49  
% 7.36/1.49  fof(f40,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(nnf_transformation,[],[f25])).
% 7.36/1.49  
% 7.36/1.49  fof(f41,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(rectify,[],[f40])).
% 7.36/1.49  
% 7.36/1.49  fof(f44,plain,(
% 7.36/1.49    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f43,plain,(
% 7.36/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f42,plain,(
% 7.36/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f45,plain,(
% 7.36/1.49    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 7.36/1.49  
% 7.36/1.49  fof(f67,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f45])).
% 7.36/1.49  
% 7.36/1.49  fof(f16,conjecture,(
% 7.36/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f17,negated_conjecture,(
% 7.36/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.36/1.49    inference(negated_conjecture,[],[f16])).
% 7.36/1.49  
% 7.36/1.49  fof(f18,plain,(
% 7.36/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.36/1.49    inference(pure_predicate_removal,[],[f17])).
% 7.36/1.49  
% 7.36/1.49  fof(f31,plain,(
% 7.36/1.49    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 7.36/1.49    inference(ennf_transformation,[],[f18])).
% 7.36/1.49  
% 7.36/1.49  fof(f32,plain,(
% 7.36/1.49    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 7.36/1.49    inference(flattening,[],[f31])).
% 7.36/1.49  
% 7.36/1.49  fof(f46,plain,(
% 7.36/1.49    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4))) & k1_xboole_0 != sK5 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_1(sK7))),
% 7.36/1.49    introduced(choice_axiom,[])).
% 7.36/1.49  
% 7.36/1.49  fof(f47,plain,(
% 7.36/1.49    ~r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4))) & k1_xboole_0 != sK5 & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5))) & v1_funct_1(sK7)),
% 7.36/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f32,f46])).
% 7.36/1.49  
% 7.36/1.49  fof(f75,plain,(
% 7.36/1.49    v1_funct_1(sK7)),
% 7.36/1.49    inference(cnf_transformation,[],[f47])).
% 7.36/1.49  
% 7.36/1.49  fof(f7,axiom,(
% 7.36/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f21,plain,(
% 7.36/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.36/1.49    inference(ennf_transformation,[],[f7])).
% 7.36/1.49  
% 7.36/1.49  fof(f58,plain,(
% 7.36/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f21])).
% 7.36/1.49  
% 7.36/1.49  fof(f76,plain,(
% 7.36/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK4),sK5)))),
% 7.36/1.49    inference(cnf_transformation,[],[f47])).
% 7.36/1.49  
% 7.36/1.49  fof(f3,axiom,(
% 7.36/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f52,plain,(
% 7.36/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f3])).
% 7.36/1.49  
% 7.36/1.49  fof(f4,axiom,(
% 7.36/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f53,plain,(
% 7.36/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f4])).
% 7.36/1.49  
% 7.36/1.49  fof(f5,axiom,(
% 7.36/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f54,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f5])).
% 7.36/1.49  
% 7.36/1.49  fof(f79,plain,(
% 7.36/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.36/1.49    inference(definition_unfolding,[],[f53,f54])).
% 7.36/1.49  
% 7.36/1.49  fof(f80,plain,(
% 7.36/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.36/1.49    inference(definition_unfolding,[],[f52,f79])).
% 7.36/1.49  
% 7.36/1.49  fof(f86,plain,(
% 7.36/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)))),
% 7.36/1.49    inference(definition_unfolding,[],[f76,f80])).
% 7.36/1.49  
% 7.36/1.49  fof(f9,axiom,(
% 7.36/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f61,plain,(
% 7.36/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f9])).
% 7.36/1.49  
% 7.36/1.49  fof(f66,plain,(
% 7.36/1.49    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f45])).
% 7.36/1.49  
% 7.36/1.49  fof(f89,plain,(
% 7.36/1.49    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(equality_resolution,[],[f66])).
% 7.36/1.49  
% 7.36/1.49  fof(f90,plain,(
% 7.36/1.49    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(equality_resolution,[],[f89])).
% 7.36/1.49  
% 7.36/1.49  fof(f2,axiom,(
% 7.36/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f51,plain,(
% 7.36/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f2])).
% 7.36/1.49  
% 7.36/1.49  fof(f64,plain,(
% 7.36/1.49    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f45])).
% 7.36/1.49  
% 7.36/1.49  fof(f92,plain,(
% 7.36/1.49    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.36/1.49    inference(equality_resolution,[],[f64])).
% 7.36/1.49  
% 7.36/1.49  fof(f13,axiom,(
% 7.36/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f28,plain,(
% 7.36/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.36/1.49    inference(ennf_transformation,[],[f13])).
% 7.36/1.49  
% 7.36/1.49  fof(f72,plain,(
% 7.36/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f28])).
% 7.36/1.49  
% 7.36/1.49  fof(f8,axiom,(
% 7.36/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f22,plain,(
% 7.36/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.36/1.49    inference(ennf_transformation,[],[f8])).
% 7.36/1.49  
% 7.36/1.49  fof(f39,plain,(
% 7.36/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.36/1.49    inference(nnf_transformation,[],[f22])).
% 7.36/1.49  
% 7.36/1.49  fof(f59,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f39])).
% 7.36/1.49  
% 7.36/1.49  fof(f14,axiom,(
% 7.36/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f19,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.36/1.49    inference(pure_predicate_removal,[],[f14])).
% 7.36/1.49  
% 7.36/1.49  fof(f29,plain,(
% 7.36/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.36/1.49    inference(ennf_transformation,[],[f19])).
% 7.36/1.49  
% 7.36/1.49  fof(f73,plain,(
% 7.36/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f29])).
% 7.36/1.49  
% 7.36/1.49  fof(f6,axiom,(
% 7.36/1.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f37,plain,(
% 7.36/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.36/1.49    inference(nnf_transformation,[],[f6])).
% 7.36/1.49  
% 7.36/1.49  fof(f38,plain,(
% 7.36/1.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 7.36/1.49    inference(flattening,[],[f37])).
% 7.36/1.49  
% 7.36/1.49  fof(f55,plain,(
% 7.36/1.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f38])).
% 7.36/1.49  
% 7.36/1.49  fof(f83,plain,(
% 7.36/1.49    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 7.36/1.49    inference(definition_unfolding,[],[f55,f80,f80])).
% 7.36/1.49  
% 7.36/1.49  fof(f78,plain,(
% 7.36/1.49    ~r1_tarski(k7_relset_1(k1_tarski(sK4),sK5,sK7,sK6),k1_tarski(k1_funct_1(sK7,sK4)))),
% 7.36/1.49    inference(cnf_transformation,[],[f47])).
% 7.36/1.49  
% 7.36/1.49  fof(f85,plain,(
% 7.36/1.49    ~r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))),
% 7.36/1.49    inference(definition_unfolding,[],[f78,f80,f80])).
% 7.36/1.49  
% 7.36/1.49  fof(f15,axiom,(
% 7.36/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f30,plain,(
% 7.36/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.36/1.49    inference(ennf_transformation,[],[f15])).
% 7.36/1.49  
% 7.36/1.49  fof(f74,plain,(
% 7.36/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.36/1.49    inference(cnf_transformation,[],[f30])).
% 7.36/1.49  
% 7.36/1.49  fof(f12,axiom,(
% 7.36/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f26,plain,(
% 7.36/1.49    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.36/1.49    inference(ennf_transformation,[],[f12])).
% 7.36/1.49  
% 7.36/1.49  fof(f27,plain,(
% 7.36/1.49    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.36/1.49    inference(flattening,[],[f26])).
% 7.36/1.49  
% 7.36/1.49  fof(f71,plain,(
% 7.36/1.49    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f27])).
% 7.36/1.49  
% 7.36/1.49  fof(f84,plain,(
% 7.36/1.49    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.36/1.49    inference(definition_unfolding,[],[f71,f80,f80])).
% 7.36/1.49  
% 7.36/1.49  fof(f10,axiom,(
% 7.36/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 7.36/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.36/1.49  
% 7.36/1.49  fof(f23,plain,(
% 7.36/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.36/1.49    inference(ennf_transformation,[],[f10])).
% 7.36/1.49  
% 7.36/1.49  fof(f62,plain,(
% 7.36/1.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.36/1.49    inference(cnf_transformation,[],[f23])).
% 7.36/1.49  
% 7.36/1.49  cnf(c_15,plain,
% 7.36/1.49      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
% 7.36/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.36/1.49      | ~ v1_funct_1(X0)
% 7.36/1.49      | ~ v1_relat_1(X0)
% 7.36/1.49      | k9_relat_1(X0,X1) = X2 ),
% 7.36/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_27,negated_conjecture,
% 7.36/1.49      ( v1_funct_1(sK7) ),
% 7.36/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_387,plain,
% 7.36/1.49      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
% 7.36/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 7.36/1.49      | ~ v1_relat_1(X0)
% 7.36/1.49      | k9_relat_1(X0,X1) = X2
% 7.36/1.49      | sK7 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_27]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_388,plain,
% 7.36/1.49      ( r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7))
% 7.36/1.49      | r2_hidden(sK1(sK7,X0,X1),X1)
% 7.36/1.49      | ~ v1_relat_1(sK7)
% 7.36/1.49      | k9_relat_1(sK7,X0) = X1 ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_387]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1726,plain,
% 7.36/1.49      ( k9_relat_1(sK7,X0) = X1
% 7.36/1.49      | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
% 7.36/1.49      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_389,plain,
% 7.36/1.49      ( k9_relat_1(sK7,X0) = X1
% 7.36/1.49      | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
% 7.36/1.49      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_7,plain,
% 7.36/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | v1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_26,negated_conjecture,
% 7.36/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5))) ),
% 7.36/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_307,plain,
% 7.36/1.49      ( ~ v1_relat_1(X0)
% 7.36/1.49      | v1_relat_1(X1)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0)
% 7.36/1.49      | sK7 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_308,plain,
% 7.36/1.49      ( ~ v1_relat_1(X0)
% 7.36/1.49      | v1_relat_1(sK7)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_307]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1729,plain,
% 7.36/1.49      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(X0)
% 7.36/1.49      | v1_relat_1(X0) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1997,plain,
% 7.36/1.49      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) = iProver_top ),
% 7.36/1.49      inference(equality_resolution,[status(thm)],[c_1729]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_10,plain,
% 7.36/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.36/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2000,plain,
% 7.36/1.49      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2001,plain,
% 7.36/1.49      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_2000]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2387,plain,
% 7.36/1.49      ( r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 7.36/1.49      | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
% 7.36/1.49      | k9_relat_1(sK7,X0) = X1 ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_1726,c_389,c_1997,c_2001]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2388,plain,
% 7.36/1.49      ( k9_relat_1(sK7,X0) = X1
% 7.36/1.49      | r2_hidden(sK2(sK7,X0,X1),k1_relat_1(sK7)) = iProver_top
% 7.36/1.49      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top ),
% 7.36/1.49      inference(renaming,[status(thm)],[c_2387]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_16,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1)
% 7.36/1.49      | ~ r2_hidden(X0,k1_relat_1(X2))
% 7.36/1.49      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 7.36/1.49      | ~ v1_funct_1(X2)
% 7.36/1.49      | ~ v1_relat_1(X2) ),
% 7.36/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_441,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1)
% 7.36/1.49      | ~ r2_hidden(X0,k1_relat_1(X2))
% 7.36/1.49      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 7.36/1.49      | ~ v1_relat_1(X2)
% 7.36/1.49      | sK7 != X2 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_442,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1)
% 7.36/1.49      | ~ r2_hidden(X0,k1_relat_1(sK7))
% 7.36/1.49      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1))
% 7.36/1.49      | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_441]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1723,plain,
% 7.36/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.49      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.36/1.49      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_443,plain,
% 7.36/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.49      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.36/1.49      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2188,plain,
% 7.36/1.49      ( r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top
% 7.36/1.49      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.36/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_1723,c_443,c_1997,c_2001]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2189,plain,
% 7.36/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.49      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.36/1.49      | r2_hidden(k1_funct_1(sK7,X0),k9_relat_1(sK7,X1)) = iProver_top ),
% 7.36/1.49      inference(renaming,[status(thm)],[c_2188]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3,plain,
% 7.36/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1737,plain,
% 7.36/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_18,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.36/1.49      | r2_hidden(sK3(X1,X2,X0),X2)
% 7.36/1.49      | ~ v1_funct_1(X1)
% 7.36/1.49      | ~ v1_relat_1(X1) ),
% 7.36/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_498,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.36/1.49      | r2_hidden(sK3(X1,X2,X0),X2)
% 7.36/1.49      | ~ v1_relat_1(X1)
% 7.36/1.49      | sK7 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_499,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 7.36/1.49      | r2_hidden(sK3(sK7,X1,X0),X1)
% 7.36/1.49      | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_498]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1720,plain,
% 7.36/1.49      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.36/1.49      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_21,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1731,plain,
% 7.36/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.36/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2120,plain,
% 7.36/1.49      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.36/1.49      | r1_tarski(X1,sK3(sK7,X1,X0)) != iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1720,c_1731]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2519,plain,
% 7.36/1.49      ( r1_tarski(X1,sK3(sK7,X1,X0)) != iProver_top
% 7.36/1.49      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_2120,c_1997,c_2001]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2520,plain,
% 7.36/1.49      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 7.36/1.49      | r1_tarski(X1,sK3(sK7,X1,X0)) != iProver_top ),
% 7.36/1.49      inference(renaming,[status(thm)],[c_2519]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2525,plain,
% 7.36/1.49      ( r2_hidden(X0,k9_relat_1(sK7,k1_xboole_0)) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_1737,c_2520]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3445,plain,
% 7.36/1.49      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.36/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2189,c_2525]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_719,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_3,c_21]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_720,plain,
% 7.36/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_719]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_721,plain,
% 7.36/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3586,plain,
% 7.36/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_3445,c_721]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_3592,plain,
% 7.36/1.49      ( k9_relat_1(sK7,X0) = k1_xboole_0
% 7.36/1.49      | r2_hidden(sK2(sK7,X0,k1_xboole_0),k1_relat_1(sK7)) = iProver_top ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2388,c_3586]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_9,plain,
% 7.36/1.49      ( ~ v4_relat_1(X0,X1)
% 7.36/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.36/1.49      | ~ v1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_22,plain,
% 7.36/1.49      ( v4_relat_1(X0,X1)
% 7.36/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.36/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_331,plain,
% 7.36/1.49      ( v4_relat_1(X0,X1)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 7.36/1.49      | sK7 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_332,plain,
% 7.36/1.49      ( v4_relat_1(sK7,X0)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_331]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_353,plain,
% 7.36/1.49      ( r1_tarski(k1_relat_1(X0),X1)
% 7.36/1.49      | ~ v1_relat_1(X0)
% 7.36/1.49      | X2 != X1
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 7.36/1.49      | sK7 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_332]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_354,plain,
% 7.36/1.49      ( r1_tarski(k1_relat_1(sK7),X0)
% 7.36/1.49      | ~ v1_relat_1(sK7)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_353]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1728,plain,
% 7.36/1.49      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.36/1.49      | r1_tarski(k1_relat_1(sK7),X0) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_355,plain,
% 7.36/1.49      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.36/1.49      | r1_tarski(k1_relat_1(sK7),X0) = iProver_top
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2627,plain,
% 7.36/1.49      ( r1_tarski(k1_relat_1(sK7),X0) = iProver_top
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_1728,c_355,c_1997,c_2001]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2628,plain,
% 7.36/1.49      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.36/1.49      | r1_tarski(k1_relat_1(sK7),X0) = iProver_top ),
% 7.36/1.49      inference(renaming,[status(thm)],[c_2627]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2633,plain,
% 7.36/1.49      ( r1_tarski(k1_relat_1(sK7),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.36/1.49      inference(equality_resolution,[status(thm)],[c_2628]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_6,plain,
% 7.36/1.49      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 7.36/1.49      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.36/1.49      | k1_xboole_0 = X0 ),
% 7.36/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1734,plain,
% 7.36/1.49      ( k2_enumset1(X0,X0,X0,X0) = X1
% 7.36/1.49      | k1_xboole_0 = X1
% 7.36/1.49      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_9967,plain,
% 7.36/1.49      ( k2_enumset1(sK4,sK4,sK4,sK4) = k1_relat_1(sK7)
% 7.36/1.49      | k1_relat_1(sK7) = k1_xboole_0 ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_2633,c_1734]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_24,negated_conjecture,
% 7.36/1.49      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) ),
% 7.36/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_23,plain,
% 7.36/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.36/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.36/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_322,plain,
% 7.36/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 7.36/1.49      | sK7 != X2 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_323,plain,
% 7.36/1.49      ( k7_relset_1(X0,X1,sK7,X2) = k9_relat_1(sK7,X2)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_322]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1794,plain,
% 7.36/1.49      ( k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,X0) = k9_relat_1(sK7,X0)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_323]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1849,plain,
% 7.36/1.49      ( k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) = k9_relat_1(sK7,sK6)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1794]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1351,plain,
% 7.36/1.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.36/1.49      theory(equality) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1798,plain,
% 7.36/1.49      ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_zfmisc_1(X0,X1)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1351]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1883,plain,
% 7.36/1.49      ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)
% 7.36/1.49      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1798]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1998,plain,
% 7.36/1.49      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5))
% 7.36/1.49      | v1_relat_1(sK7) ),
% 7.36/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1997]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1345,plain,( X0 = X0 ),theory(equality) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2003,plain,
% 7.36/1.49      ( k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_zfmisc_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1345]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_20,plain,
% 7.36/1.49      ( ~ v1_funct_1(X0)
% 7.36/1.49      | ~ v1_relat_1(X0)
% 7.36/1.49      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 7.36/1.49      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_372,plain,
% 7.36/1.49      ( ~ v1_relat_1(X0)
% 7.36/1.49      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 7.36/1.49      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 7.36/1.49      | sK7 != X0 ),
% 7.36/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_373,plain,
% 7.36/1.49      ( ~ v1_relat_1(sK7)
% 7.36/1.49      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7)
% 7.36/1.49      | k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7) ),
% 7.36/1.49      inference(unflattening,[status(thm)],[c_372]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1727,plain,
% 7.36/1.49      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7)
% 7.36/1.49      | k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7)
% 7.36/1.49      | v1_relat_1(sK7) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2281,plain,
% 7.36/1.49      ( k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7)
% 7.36/1.49      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7) ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_1727,c_373,c_1998,c_2000]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2282,plain,
% 7.36/1.49      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK7)
% 7.36/1.49      | k2_enumset1(k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0),k1_funct_1(sK7,X0)) = k2_relat_1(sK7) ),
% 7.36/1.49      inference(renaming,[status(thm)],[c_2281]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_2283,plain,
% 7.36/1.49      ( k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) = k2_relat_1(sK7)
% 7.36/1.49      | k2_enumset1(sK4,sK4,sK4,sK4) != k1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_2282]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_11,plain,
% 7.36/1.49      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.36/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_4721,plain,
% 7.36/1.49      ( r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7))
% 7.36/1.49      | ~ v1_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1347,plain,
% 7.36/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.36/1.49      theory(equality) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1780,plain,
% 7.36/1.49      ( ~ r1_tarski(X0,X1)
% 7.36/1.49      | r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))
% 7.36/1.49      | k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) != X0
% 7.36/1.49      | k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) != X1 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1347]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1850,plain,
% 7.36/1.49      ( r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))
% 7.36/1.49      | ~ r1_tarski(k9_relat_1(sK7,sK6),X0)
% 7.36/1.49      | k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
% 7.36/1.49      | k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) != X0 ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1780]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_5537,plain,
% 7.36/1.49      ( r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)))
% 7.36/1.49      | ~ r1_tarski(k9_relat_1(sK7,sK6),k2_relat_1(sK7))
% 7.36/1.49      | k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6) != k9_relat_1(sK7,sK6)
% 7.36/1.49      | k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4)) != k2_relat_1(sK7) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_1850]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_9971,plain,
% 7.36/1.49      ( k1_relat_1(sK7) = k1_xboole_0 ),
% 7.36/1.49      inference(global_propositional_subsumption,
% 7.36/1.49                [status(thm)],
% 7.36/1.49                [c_9967,c_24,c_1849,c_1883,c_1998,c_2000,c_2003,c_2283,
% 7.36/1.49                 c_4721,c_5537]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_14126,plain,
% 7.36/1.49      ( k9_relat_1(sK7,X0) = k1_xboole_0
% 7.36/1.49      | r2_hidden(sK2(sK7,X0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.36/1.49      inference(light_normalisation,[status(thm)],[c_3592,c_9971]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_14132,plain,
% 7.36/1.49      ( k9_relat_1(sK7,X0) = k1_xboole_0 ),
% 7.36/1.49      inference(superposition,[status(thm)],[c_14126,c_3586]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1730,plain,
% 7.36/1.49      ( r1_tarski(k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) != iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1800,plain,
% 7.36/1.49      ( k7_relset_1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 7.36/1.49      inference(equality_resolution,[status(thm)],[c_323]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1845,plain,
% 7.36/1.49      ( r1_tarski(k9_relat_1(sK7,sK6),k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) != iProver_top ),
% 7.36/1.49      inference(demodulation,[status(thm)],[c_1730,c_1800]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_21975,plain,
% 7.36/1.49      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) != iProver_top ),
% 7.36/1.49      inference(demodulation,[status(thm)],[c_14132,c_1845]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1974,plain,
% 7.36/1.49      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) ),
% 7.36/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(c_1975,plain,
% 7.36/1.49      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4),k1_funct_1(sK7,sK4))) = iProver_top ),
% 7.36/1.49      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 7.36/1.49  
% 7.36/1.49  cnf(contradiction,plain,
% 7.36/1.49      ( $false ),
% 7.36/1.49      inference(minisat,[status(thm)],[c_21975,c_1975]) ).
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.36/1.49  
% 7.36/1.49  ------                               Statistics
% 7.36/1.49  
% 7.36/1.49  ------ General
% 7.36/1.49  
% 7.36/1.49  abstr_ref_over_cycles:                  0
% 7.36/1.49  abstr_ref_under_cycles:                 0
% 7.36/1.49  gc_basic_clause_elim:                   0
% 7.36/1.49  forced_gc_time:                         0
% 7.36/1.49  parsing_time:                           0.011
% 7.36/1.49  unif_index_cands_time:                  0.
% 7.36/1.49  unif_index_add_time:                    0.
% 7.36/1.49  orderings_time:                         0.
% 7.36/1.49  out_proof_time:                         0.012
% 7.36/1.49  total_time:                             0.849
% 7.36/1.49  num_of_symbols:                         54
% 7.36/1.49  num_of_terms:                           26526
% 7.36/1.49  
% 7.36/1.49  ------ Preprocessing
% 7.36/1.49  
% 7.36/1.49  num_of_splits:                          0
% 7.36/1.49  num_of_split_atoms:                     0
% 7.36/1.49  num_of_reused_defs:                     0
% 7.36/1.49  num_eq_ax_congr_red:                    35
% 7.36/1.49  num_of_sem_filtered_clauses:            1
% 7.36/1.49  num_of_subtypes:                        0
% 7.36/1.49  monotx_restored_types:                  0
% 7.36/1.49  sat_num_of_epr_types:                   0
% 7.36/1.49  sat_num_of_non_cyclic_types:            0
% 7.36/1.49  sat_guarded_non_collapsed_types:        0
% 7.36/1.49  num_pure_diseq_elim:                    0
% 7.36/1.49  simp_replaced_by:                       0
% 7.36/1.49  res_preprocessed:                       133
% 7.36/1.49  prep_upred:                             0
% 7.36/1.49  prep_unflattend:                        104
% 7.36/1.49  smt_new_axioms:                         0
% 7.36/1.49  pred_elim_cands:                        3
% 7.36/1.49  pred_elim:                              3
% 7.36/1.49  pred_elim_cl:                           4
% 7.36/1.49  pred_elim_cycles:                       5
% 7.36/1.49  merged_defs:                            0
% 7.36/1.49  merged_defs_ncl:                        0
% 7.36/1.49  bin_hyper_res:                          0
% 7.36/1.49  prep_cycles:                            4
% 7.36/1.49  pred_elim_time:                         0.018
% 7.36/1.49  splitting_time:                         0.
% 7.36/1.49  sem_filter_time:                        0.
% 7.36/1.49  monotx_time:                            0.001
% 7.36/1.49  subtype_inf_time:                       0.
% 7.36/1.49  
% 7.36/1.49  ------ Problem properties
% 7.36/1.49  
% 7.36/1.49  clauses:                                24
% 7.36/1.49  conjectures:                            2
% 7.36/1.49  epr:                                    4
% 7.36/1.49  horn:                                   19
% 7.36/1.49  ground:                                 2
% 7.36/1.49  unary:                                  6
% 7.36/1.49  binary:                                 5
% 7.36/1.49  lits:                                   62
% 7.36/1.49  lits_eq:                                16
% 7.36/1.49  fd_pure:                                0
% 7.36/1.49  fd_pseudo:                              0
% 7.36/1.49  fd_cond:                                0
% 7.36/1.49  fd_pseudo_cond:                         5
% 7.36/1.49  ac_symbols:                             0
% 7.36/1.49  
% 7.36/1.49  ------ Propositional Solver
% 7.36/1.49  
% 7.36/1.49  prop_solver_calls:                      32
% 7.36/1.49  prop_fast_solver_calls:                 2893
% 7.36/1.49  smt_solver_calls:                       0
% 7.36/1.49  smt_fast_solver_calls:                  0
% 7.36/1.49  prop_num_of_clauses:                    10657
% 7.36/1.49  prop_preprocess_simplified:             15887
% 7.36/1.49  prop_fo_subsumed:                       108
% 7.36/1.49  prop_solver_time:                       0.
% 7.36/1.49  smt_solver_time:                        0.
% 7.36/1.49  smt_fast_solver_time:                   0.
% 7.36/1.49  prop_fast_solver_time:                  0.
% 7.36/1.49  prop_unsat_core_time:                   0.001
% 7.36/1.49  
% 7.36/1.49  ------ QBF
% 7.36/1.49  
% 7.36/1.49  qbf_q_res:                              0
% 7.36/1.49  qbf_num_tautologies:                    0
% 7.36/1.49  qbf_prep_cycles:                        0
% 7.36/1.49  
% 7.36/1.49  ------ BMC1
% 7.36/1.49  
% 7.36/1.49  bmc1_current_bound:                     -1
% 7.36/1.49  bmc1_last_solved_bound:                 -1
% 7.36/1.49  bmc1_unsat_core_size:                   -1
% 7.36/1.49  bmc1_unsat_core_parents_size:           -1
% 7.36/1.49  bmc1_merge_next_fun:                    0
% 7.36/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.36/1.49  
% 7.36/1.49  ------ Instantiation
% 7.36/1.49  
% 7.36/1.49  inst_num_of_clauses:                    2103
% 7.36/1.49  inst_num_in_passive:                    231
% 7.36/1.49  inst_num_in_active:                     840
% 7.36/1.49  inst_num_in_unprocessed:                1032
% 7.36/1.49  inst_num_of_loops:                      1070
% 7.36/1.49  inst_num_of_learning_restarts:          0
% 7.36/1.49  inst_num_moves_active_passive:          226
% 7.36/1.49  inst_lit_activity:                      0
% 7.36/1.49  inst_lit_activity_moves:                0
% 7.36/1.49  inst_num_tautologies:                   0
% 7.36/1.49  inst_num_prop_implied:                  0
% 7.36/1.49  inst_num_existing_simplified:           0
% 7.36/1.49  inst_num_eq_res_simplified:             0
% 7.36/1.49  inst_num_child_elim:                    0
% 7.36/1.49  inst_num_of_dismatching_blockings:      791
% 7.36/1.49  inst_num_of_non_proper_insts:           2375
% 7.36/1.49  inst_num_of_duplicates:                 0
% 7.36/1.49  inst_inst_num_from_inst_to_res:         0
% 7.36/1.49  inst_dismatching_checking_time:         0.
% 7.36/1.49  
% 7.36/1.49  ------ Resolution
% 7.36/1.49  
% 7.36/1.49  res_num_of_clauses:                     0
% 7.36/1.49  res_num_in_passive:                     0
% 7.36/1.49  res_num_in_active:                      0
% 7.36/1.49  res_num_of_loops:                       137
% 7.36/1.49  res_forward_subset_subsumed:            220
% 7.36/1.49  res_backward_subset_subsumed:           0
% 7.36/1.49  res_forward_subsumed:                   3
% 7.36/1.49  res_backward_subsumed:                  1
% 7.36/1.49  res_forward_subsumption_resolution:     0
% 7.36/1.49  res_backward_subsumption_resolution:    0
% 7.36/1.49  res_clause_to_clause_subsumption:       5481
% 7.36/1.49  res_orphan_elimination:                 0
% 7.36/1.49  res_tautology_del:                      244
% 7.36/1.49  res_num_eq_res_simplified:              0
% 7.36/1.49  res_num_sel_changes:                    0
% 7.36/1.49  res_moves_from_active_to_pass:          0
% 7.36/1.49  
% 7.36/1.49  ------ Superposition
% 7.36/1.49  
% 7.36/1.49  sup_time_total:                         0.
% 7.36/1.49  sup_time_generating:                    0.
% 7.36/1.49  sup_time_sim_full:                      0.
% 7.36/1.49  sup_time_sim_immed:                     0.
% 7.36/1.49  
% 7.36/1.49  sup_num_of_clauses:                     1216
% 7.36/1.49  sup_num_in_active:                      82
% 7.36/1.49  sup_num_in_passive:                     1134
% 7.36/1.49  sup_num_of_loops:                       212
% 7.36/1.49  sup_fw_superposition:                   941
% 7.36/1.49  sup_bw_superposition:                   1062
% 7.36/1.49  sup_immediate_simplified:               968
% 7.36/1.49  sup_given_eliminated:                   4
% 7.36/1.49  comparisons_done:                       0
% 7.36/1.49  comparisons_avoided:                    74
% 7.36/1.49  
% 7.36/1.49  ------ Simplifications
% 7.36/1.49  
% 7.36/1.49  
% 7.36/1.49  sim_fw_subset_subsumed:                 120
% 7.36/1.49  sim_bw_subset_subsumed:                 58
% 7.36/1.49  sim_fw_subsumed:                        221
% 7.36/1.49  sim_bw_subsumed:                        211
% 7.36/1.49  sim_fw_subsumption_res:                 0
% 7.36/1.49  sim_bw_subsumption_res:                 0
% 7.36/1.49  sim_tautology_del:                      1
% 7.36/1.49  sim_eq_tautology_del:                   245
% 7.36/1.49  sim_eq_res_simp:                        0
% 7.36/1.49  sim_fw_demodulated:                     386
% 7.36/1.49  sim_bw_demodulated:                     111
% 7.36/1.49  sim_light_normalised:                   693
% 7.36/1.49  sim_joinable_taut:                      0
% 7.36/1.49  sim_joinable_simp:                      0
% 7.36/1.49  sim_ac_normalised:                      0
% 7.36/1.49  sim_smt_subsumption:                    0
% 7.36/1.49  
%------------------------------------------------------------------------------
