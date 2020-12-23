%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:12 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 755 expanded)
%              Number of clauses        :   89 ( 249 expanded)
%              Number of leaves         :   21 ( 194 expanded)
%              Depth                    :   19
%              Number of atoms          :  686 (4624 expanded)
%              Number of equality atoms :  211 (1383 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
        | ~ v1_funct_2(sK9,sK7,sK8)
        | ~ v1_funct_1(sK9) )
      & r2_hidden(sK9,k1_funct_2(sK7,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      | ~ v1_funct_2(sK9,sK7,sK8)
      | ~ v1_funct_1(sK9) )
    & r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f55])).

fof(f101,plain,(
    r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f11,f32])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f90])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X0)
                  | k1_relat_1(X4) != X1
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X0)
                  & k1_relat_1(X5) = X1
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X0)
                  & k1_relat_1(X8) = X1
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f50,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
        & k1_relat_1(sK5(X0,X1,X6)) = X1
        & sK5(X0,X1,X6) = X6
        & v1_funct_1(sK5(X0,X1,X6))
        & v1_relat_1(sK5(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0)
        & k1_relat_1(sK4(X0,X1,X2)) = X1
        & sK4(X0,X1,X2) = X3
        & v1_funct_1(sK4(X0,X1,X2))
        & v1_relat_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X0)
                & k1_relat_1(X5) = X1
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X0)
              | k1_relat_1(X4) != X1
              | sK3(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK3(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK3(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0)
              & k1_relat_1(sK4(X0,X1,X2)) = X1
              & sK3(X0,X1,X2) = sK4(X0,X1,X2)
              & v1_funct_1(sK4(X0,X1,X2))
              & v1_relat_1(sK4(X0,X1,X2)) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
                & k1_relat_1(sK5(X0,X1,X6)) = X1
                & sK5(X0,X1,X6) = X6
                & v1_funct_1(sK5(X0,X1,X6))
                & v1_relat_1(sK5(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f47,f50,f49,f48])).

fof(f80,plain,(
    ! [X6,X2,X0,X1] :
      ( sK5(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK5(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f102,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1)
        & r2_hidden(sK6(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f53])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f115,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f97])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_45,negated_conjecture,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_9673,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_34,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_9677,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK5(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9681,plain,
    ( sK5(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_11290,plain,
    ( sK5(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9677,c_9681])).

cnf(c_11680,plain,
    ( sK5(sK8,sK7,sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_9673,c_11290])).

cnf(c_28,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_9683,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11976,plain,
    ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9677,c_9683])).

cnf(c_17604,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11680,c_11976])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_9691,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_9682,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11624,plain,
    ( k1_relat_1(sK5(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9677,c_9682])).

cnf(c_11954,plain,
    ( k1_relat_1(sK5(sK8,sK7,sK9)) = sK7 ),
    inference(superposition,[status(thm)],[c_9673,c_11624])).

cnf(c_11956,plain,
    ( k1_relat_1(sK9) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_11954,c_11680])).

cnf(c_36,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_44,negated_conjecture,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_670,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | k2_relat_1(X0) != sK8
    | k1_relat_1(X0) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_44])).

cnf(c_671,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK9)
    | k2_relat_1(sK9) != sK8
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_9672,plain,
    ( k2_relat_1(sK9) != sK8
    | k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_12443,plain,
    ( k2_relat_1(sK9) != sK8
    | sK7 != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11956,c_9672])).

cnf(c_12444,plain,
    ( k2_relat_1(sK9) != sK8
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12443])).

cnf(c_46,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_143,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_147,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_577,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_578,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_35,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_582,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_578,c_35])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_657,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | sK8 != X2
    | sK7 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_44])).

cnf(c_658,plain,
    ( ~ v1_partfun1(sK9,sK7)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_810,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_582,c_658])).

cnf(c_811,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(k2_relat_1(sK9))
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_812,plain,
    ( k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_811])).

cnf(c_10,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_689,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | k1_relat_1(X0) != sK7
    | sK8 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_44])).

cnf(c_690,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_funct_1(sK9)
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_689])).

cnf(c_3020,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_xboole_0(X0)
    | k1_relat_1(sK9) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_690])).

cnf(c_3021,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
    | ~ v1_relat_1(sK9)
    | ~ v1_xboole_0(sK9)
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_3020])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2781,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_2782,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_2781])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2794,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2782,c_1])).

cnf(c_3028,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_relat_1(sK9)
    | ~ v1_xboole_0(sK9)
    | k1_relat_1(sK9) != sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3021,c_2794])).

cnf(c_3033,plain,
    ( k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3028])).

cnf(c_10201,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_10204,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10201])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_10077,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK5(X0,X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_10361,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK5(sK8,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_10077])).

cnf(c_10363,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
    | v1_relat_1(sK5(sK8,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10361])).

cnf(c_10114,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK5(X0,X1,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_10360,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK5(sK8,sK7,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_10114])).

cnf(c_8756,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_10451,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK5(sK8,sK7,sK9))
    | X0 != sK5(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_8756])).

cnf(c_10470,plain,
    ( X0 != sK5(sK8,sK7,sK9)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10451])).

cnf(c_10472,plain,
    ( sK9 != sK5(sK8,sK7,sK9)
    | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10470])).

cnf(c_8747,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_11107,plain,
    ( X0 != X1
    | X0 = sK5(sK8,sK7,sK9)
    | sK5(sK8,sK7,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_8747])).

cnf(c_11108,plain,
    ( sK5(sK8,sK7,sK9) != sK9
    | sK9 = sK5(sK8,sK7,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_11107])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK5(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9680,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK5(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_11464,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK5(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9677,c_9680])).

cnf(c_11866,plain,
    ( v1_funct_1(sK5(sK8,sK7,sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9673,c_11464])).

cnf(c_11868,plain,
    ( v1_funct_1(sK9) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11866,c_11680])).

cnf(c_9676,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12520,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_11956,c_9676])).

cnf(c_12731,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12520,c_45,c_46,c_143,c_147,c_10201,c_10204,c_10363,c_10360,c_10472,c_11108,c_11868])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_9692,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12737,plain,
    ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_12731,c_9692])).

cnf(c_12891,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12444,c_45,c_46,c_143,c_147,c_812,c_3033,c_10201,c_10204,c_10363,c_10360,c_10472,c_11108,c_11868,c_11956,c_12737])).

cnf(c_13843,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_9691,c_12891])).

cnf(c_13847,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13843,c_11956])).

cnf(c_13875,plain,
    ( r1_tarski(sK7,sK7) != iProver_top
    | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13847,c_45,c_46,c_143,c_147,c_10201,c_10204,c_10363,c_10360,c_10472,c_11108])).

cnf(c_13876,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
    | r1_tarski(sK7,sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_13875])).

cnf(c_9699,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13881,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13876,c_9699])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17604,c_13881,c_46])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.11/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/0.93  
% 4.11/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/0.93  
% 4.11/0.93  ------  iProver source info
% 4.11/0.93  
% 4.11/0.93  git: date: 2020-06-30 10:37:57 +0100
% 4.11/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/0.93  git: non_committed_changes: false
% 4.11/0.93  git: last_make_outside_of_git: false
% 4.11/0.93  
% 4.11/0.93  ------ 
% 4.11/0.93  
% 4.11/0.93  ------ Input Options
% 4.11/0.93  
% 4.11/0.93  --out_options                           all
% 4.11/0.93  --tptp_safe_out                         true
% 4.11/0.93  --problem_path                          ""
% 4.11/0.93  --include_path                          ""
% 4.11/0.93  --clausifier                            res/vclausify_rel
% 4.11/0.93  --clausifier_options                    --mode clausify
% 4.11/0.93  --stdin                                 false
% 4.11/0.93  --stats_out                             all
% 4.11/0.93  
% 4.11/0.93  ------ General Options
% 4.11/0.93  
% 4.11/0.93  --fof                                   false
% 4.11/0.93  --time_out_real                         305.
% 4.11/0.93  --time_out_virtual                      -1.
% 4.11/0.93  --symbol_type_check                     false
% 4.11/0.93  --clausify_out                          false
% 4.11/0.93  --sig_cnt_out                           false
% 4.11/0.93  --trig_cnt_out                          false
% 4.11/0.93  --trig_cnt_out_tolerance                1.
% 4.11/0.93  --trig_cnt_out_sk_spl                   false
% 4.11/0.93  --abstr_cl_out                          false
% 4.11/0.93  
% 4.11/0.93  ------ Global Options
% 4.11/0.93  
% 4.11/0.93  --schedule                              default
% 4.11/0.93  --add_important_lit                     false
% 4.11/0.93  --prop_solver_per_cl                    1000
% 4.11/0.93  --min_unsat_core                        false
% 4.11/0.93  --soft_assumptions                      false
% 4.11/0.93  --soft_lemma_size                       3
% 4.11/0.93  --prop_impl_unit_size                   0
% 4.11/0.93  --prop_impl_unit                        []
% 4.11/0.93  --share_sel_clauses                     true
% 4.11/0.93  --reset_solvers                         false
% 4.11/0.93  --bc_imp_inh                            [conj_cone]
% 4.11/0.93  --conj_cone_tolerance                   3.
% 4.11/0.93  --extra_neg_conj                        none
% 4.11/0.93  --large_theory_mode                     true
% 4.11/0.93  --prolific_symb_bound                   200
% 4.11/0.93  --lt_threshold                          2000
% 4.11/0.93  --clause_weak_htbl                      true
% 4.11/0.93  --gc_record_bc_elim                     false
% 4.11/0.93  
% 4.11/0.93  ------ Preprocessing Options
% 4.11/0.93  
% 4.11/0.93  --preprocessing_flag                    true
% 4.11/0.93  --time_out_prep_mult                    0.1
% 4.11/0.93  --splitting_mode                        input
% 4.11/0.93  --splitting_grd                         true
% 4.11/0.93  --splitting_cvd                         false
% 4.11/0.93  --splitting_cvd_svl                     false
% 4.11/0.93  --splitting_nvd                         32
% 4.11/0.93  --sub_typing                            true
% 4.11/0.93  --prep_gs_sim                           true
% 4.11/0.93  --prep_unflatten                        true
% 4.11/0.93  --prep_res_sim                          true
% 4.11/0.93  --prep_upred                            true
% 4.11/0.93  --prep_sem_filter                       exhaustive
% 4.11/0.93  --prep_sem_filter_out                   false
% 4.11/0.93  --pred_elim                             true
% 4.11/0.93  --res_sim_input                         true
% 4.11/0.93  --eq_ax_congr_red                       true
% 4.11/0.93  --pure_diseq_elim                       true
% 4.11/0.93  --brand_transform                       false
% 4.11/0.93  --non_eq_to_eq                          false
% 4.11/0.93  --prep_def_merge                        true
% 4.11/0.93  --prep_def_merge_prop_impl              false
% 4.11/0.93  --prep_def_merge_mbd                    true
% 4.11/0.93  --prep_def_merge_tr_red                 false
% 4.11/0.93  --prep_def_merge_tr_cl                  false
% 4.11/0.93  --smt_preprocessing                     true
% 4.11/0.93  --smt_ac_axioms                         fast
% 4.11/0.93  --preprocessed_out                      false
% 4.11/0.93  --preprocessed_stats                    false
% 4.11/0.93  
% 4.11/0.93  ------ Abstraction refinement Options
% 4.11/0.93  
% 4.11/0.93  --abstr_ref                             []
% 4.11/0.93  --abstr_ref_prep                        false
% 4.11/0.93  --abstr_ref_until_sat                   false
% 4.11/0.93  --abstr_ref_sig_restrict                funpre
% 4.11/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/0.93  --abstr_ref_under                       []
% 4.11/0.93  
% 4.11/0.93  ------ SAT Options
% 4.11/0.93  
% 4.11/0.93  --sat_mode                              false
% 4.11/0.93  --sat_fm_restart_options                ""
% 4.11/0.93  --sat_gr_def                            false
% 4.11/0.93  --sat_epr_types                         true
% 4.11/0.93  --sat_non_cyclic_types                  false
% 4.11/0.93  --sat_finite_models                     false
% 4.11/0.93  --sat_fm_lemmas                         false
% 4.11/0.93  --sat_fm_prep                           false
% 4.11/0.93  --sat_fm_uc_incr                        true
% 4.11/0.93  --sat_out_model                         small
% 4.11/0.93  --sat_out_clauses                       false
% 4.11/0.93  
% 4.11/0.93  ------ QBF Options
% 4.11/0.93  
% 4.11/0.93  --qbf_mode                              false
% 4.11/0.93  --qbf_elim_univ                         false
% 4.11/0.93  --qbf_dom_inst                          none
% 4.11/0.93  --qbf_dom_pre_inst                      false
% 4.11/0.93  --qbf_sk_in                             false
% 4.11/0.93  --qbf_pred_elim                         true
% 4.11/0.93  --qbf_split                             512
% 4.11/0.93  
% 4.11/0.93  ------ BMC1 Options
% 4.11/0.93  
% 4.11/0.93  --bmc1_incremental                      false
% 4.11/0.93  --bmc1_axioms                           reachable_all
% 4.11/0.93  --bmc1_min_bound                        0
% 4.11/0.93  --bmc1_max_bound                        -1
% 4.11/0.93  --bmc1_max_bound_default                -1
% 4.11/0.93  --bmc1_symbol_reachability              true
% 4.11/0.93  --bmc1_property_lemmas                  false
% 4.11/0.93  --bmc1_k_induction                      false
% 4.11/0.93  --bmc1_non_equiv_states                 false
% 4.11/0.93  --bmc1_deadlock                         false
% 4.11/0.93  --bmc1_ucm                              false
% 4.11/0.93  --bmc1_add_unsat_core                   none
% 4.11/0.93  --bmc1_unsat_core_children              false
% 4.11/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/0.93  --bmc1_out_stat                         full
% 4.11/0.93  --bmc1_ground_init                      false
% 4.11/0.93  --bmc1_pre_inst_next_state              false
% 4.11/0.93  --bmc1_pre_inst_state                   false
% 4.11/0.93  --bmc1_pre_inst_reach_state             false
% 4.11/0.93  --bmc1_out_unsat_core                   false
% 4.11/0.93  --bmc1_aig_witness_out                  false
% 4.11/0.93  --bmc1_verbose                          false
% 4.11/0.93  --bmc1_dump_clauses_tptp                false
% 4.11/0.93  --bmc1_dump_unsat_core_tptp             false
% 4.11/0.93  --bmc1_dump_file                        -
% 4.11/0.93  --bmc1_ucm_expand_uc_limit              128
% 4.11/0.93  --bmc1_ucm_n_expand_iterations          6
% 4.11/0.93  --bmc1_ucm_extend_mode                  1
% 4.11/0.93  --bmc1_ucm_init_mode                    2
% 4.11/0.93  --bmc1_ucm_cone_mode                    none
% 4.11/0.93  --bmc1_ucm_reduced_relation_type        0
% 4.11/0.93  --bmc1_ucm_relax_model                  4
% 4.11/0.93  --bmc1_ucm_full_tr_after_sat            true
% 4.11/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/0.93  --bmc1_ucm_layered_model                none
% 4.11/0.93  --bmc1_ucm_max_lemma_size               10
% 4.11/0.93  
% 4.11/0.93  ------ AIG Options
% 4.11/0.93  
% 4.11/0.93  --aig_mode                              false
% 4.11/0.93  
% 4.11/0.93  ------ Instantiation Options
% 4.11/0.93  
% 4.11/0.93  --instantiation_flag                    true
% 4.11/0.93  --inst_sos_flag                         false
% 4.11/0.93  --inst_sos_phase                        true
% 4.11/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/0.93  --inst_lit_sel_side                     num_symb
% 4.11/0.93  --inst_solver_per_active                1400
% 4.11/0.93  --inst_solver_calls_frac                1.
% 4.11/0.93  --inst_passive_queue_type               priority_queues
% 4.11/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/0.93  --inst_passive_queues_freq              [25;2]
% 4.11/0.93  --inst_dismatching                      true
% 4.11/0.93  --inst_eager_unprocessed_to_passive     true
% 4.11/0.93  --inst_prop_sim_given                   true
% 4.11/0.93  --inst_prop_sim_new                     false
% 4.11/0.93  --inst_subs_new                         false
% 4.11/0.93  --inst_eq_res_simp                      false
% 4.11/0.93  --inst_subs_given                       false
% 4.11/0.93  --inst_orphan_elimination               true
% 4.11/0.93  --inst_learning_loop_flag               true
% 4.11/0.93  --inst_learning_start                   3000
% 4.11/0.93  --inst_learning_factor                  2
% 4.11/0.93  --inst_start_prop_sim_after_learn       3
% 4.11/0.93  --inst_sel_renew                        solver
% 4.11/0.93  --inst_lit_activity_flag                true
% 4.11/0.93  --inst_restr_to_given                   false
% 4.11/0.93  --inst_activity_threshold               500
% 4.11/0.93  --inst_out_proof                        true
% 4.11/0.93  
% 4.11/0.93  ------ Resolution Options
% 4.11/0.93  
% 4.11/0.93  --resolution_flag                       true
% 4.11/0.93  --res_lit_sel                           adaptive
% 4.11/0.93  --res_lit_sel_side                      none
% 4.11/0.93  --res_ordering                          kbo
% 4.11/0.93  --res_to_prop_solver                    active
% 4.11/0.93  --res_prop_simpl_new                    false
% 4.11/0.93  --res_prop_simpl_given                  true
% 4.11/0.93  --res_passive_queue_type                priority_queues
% 4.11/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/0.93  --res_passive_queues_freq               [15;5]
% 4.11/0.93  --res_forward_subs                      full
% 4.11/0.93  --res_backward_subs                     full
% 4.11/0.93  --res_forward_subs_resolution           true
% 4.11/0.93  --res_backward_subs_resolution          true
% 4.11/0.93  --res_orphan_elimination                true
% 4.11/0.93  --res_time_limit                        2.
% 4.11/0.93  --res_out_proof                         true
% 4.11/0.93  
% 4.11/0.93  ------ Superposition Options
% 4.11/0.93  
% 4.11/0.93  --superposition_flag                    true
% 4.11/0.93  --sup_passive_queue_type                priority_queues
% 4.11/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/0.93  --sup_passive_queues_freq               [8;1;4]
% 4.11/0.93  --demod_completeness_check              fast
% 4.11/0.93  --demod_use_ground                      true
% 4.11/0.93  --sup_to_prop_solver                    passive
% 4.11/0.93  --sup_prop_simpl_new                    true
% 4.11/0.93  --sup_prop_simpl_given                  true
% 4.11/0.93  --sup_fun_splitting                     false
% 4.11/0.93  --sup_smt_interval                      50000
% 4.11/0.93  
% 4.11/0.93  ------ Superposition Simplification Setup
% 4.11/0.93  
% 4.11/0.93  --sup_indices_passive                   []
% 4.11/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.93  --sup_full_bw                           [BwDemod]
% 4.11/0.93  --sup_immed_triv                        [TrivRules]
% 4.11/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.93  --sup_immed_bw_main                     []
% 4.11/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.93  
% 4.11/0.93  ------ Combination Options
% 4.11/0.93  
% 4.11/0.93  --comb_res_mult                         3
% 4.11/0.93  --comb_sup_mult                         2
% 4.11/0.93  --comb_inst_mult                        10
% 4.11/0.93  
% 4.11/0.93  ------ Debug Options
% 4.11/0.93  
% 4.11/0.93  --dbg_backtrace                         false
% 4.11/0.93  --dbg_dump_prop_clauses                 false
% 4.11/0.93  --dbg_dump_prop_clauses_file            -
% 4.11/0.93  --dbg_out_stat                          false
% 4.11/0.93  ------ Parsing...
% 4.11/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/0.93  
% 4.11/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.11/0.93  
% 4.11/0.93  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/0.93  
% 4.11/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/0.93  ------ Proving...
% 4.11/0.93  ------ Problem Properties 
% 4.11/0.93  
% 4.11/0.93  
% 4.11/0.93  clauses                                 40
% 4.11/0.93  conjectures                             1
% 4.11/0.93  EPR                                     5
% 4.11/0.93  Horn                                    30
% 4.11/0.93  unary                                   3
% 4.11/0.93  binary                                  9
% 4.11/0.93  lits                                    127
% 4.11/0.93  lits eq                                 15
% 4.11/0.93  fd_pure                                 0
% 4.11/0.93  fd_pseudo                               0
% 4.11/0.93  fd_cond                                 0
% 4.11/0.93  fd_pseudo_cond                          3
% 4.11/0.93  AC symbols                              0
% 4.11/0.93  
% 4.11/0.93  ------ Schedule dynamic 5 is on 
% 4.11/0.93  
% 4.11/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.11/0.93  
% 4.11/0.93  
% 4.11/0.93  ------ 
% 4.11/0.93  Current options:
% 4.11/0.93  ------ 
% 4.11/0.93  
% 4.11/0.93  ------ Input Options
% 4.11/0.93  
% 4.11/0.93  --out_options                           all
% 4.11/0.93  --tptp_safe_out                         true
% 4.11/0.93  --problem_path                          ""
% 4.11/0.93  --include_path                          ""
% 4.11/0.93  --clausifier                            res/vclausify_rel
% 4.11/0.93  --clausifier_options                    --mode clausify
% 4.11/0.93  --stdin                                 false
% 4.11/0.93  --stats_out                             all
% 4.11/0.93  
% 4.11/0.93  ------ General Options
% 4.11/0.93  
% 4.11/0.93  --fof                                   false
% 4.11/0.93  --time_out_real                         305.
% 4.11/0.93  --time_out_virtual                      -1.
% 4.11/0.93  --symbol_type_check                     false
% 4.11/0.93  --clausify_out                          false
% 4.11/0.93  --sig_cnt_out                           false
% 4.11/0.93  --trig_cnt_out                          false
% 4.11/0.93  --trig_cnt_out_tolerance                1.
% 4.11/0.93  --trig_cnt_out_sk_spl                   false
% 4.11/0.93  --abstr_cl_out                          false
% 4.11/0.93  
% 4.11/0.93  ------ Global Options
% 4.11/0.93  
% 4.11/0.93  --schedule                              default
% 4.11/0.93  --add_important_lit                     false
% 4.11/0.93  --prop_solver_per_cl                    1000
% 4.11/0.93  --min_unsat_core                        false
% 4.11/0.93  --soft_assumptions                      false
% 4.11/0.93  --soft_lemma_size                       3
% 4.11/0.93  --prop_impl_unit_size                   0
% 4.11/0.93  --prop_impl_unit                        []
% 4.11/0.93  --share_sel_clauses                     true
% 4.11/0.93  --reset_solvers                         false
% 4.11/0.93  --bc_imp_inh                            [conj_cone]
% 4.11/0.93  --conj_cone_tolerance                   3.
% 4.11/0.93  --extra_neg_conj                        none
% 4.11/0.93  --large_theory_mode                     true
% 4.11/0.93  --prolific_symb_bound                   200
% 4.11/0.93  --lt_threshold                          2000
% 4.11/0.93  --clause_weak_htbl                      true
% 4.11/0.93  --gc_record_bc_elim                     false
% 4.11/0.93  
% 4.11/0.93  ------ Preprocessing Options
% 4.11/0.93  
% 4.11/0.93  --preprocessing_flag                    true
% 4.11/0.93  --time_out_prep_mult                    0.1
% 4.11/0.93  --splitting_mode                        input
% 4.11/0.93  --splitting_grd                         true
% 4.11/0.93  --splitting_cvd                         false
% 4.11/0.93  --splitting_cvd_svl                     false
% 4.11/0.93  --splitting_nvd                         32
% 4.11/0.93  --sub_typing                            true
% 4.11/0.93  --prep_gs_sim                           true
% 4.11/0.93  --prep_unflatten                        true
% 4.11/0.93  --prep_res_sim                          true
% 4.11/0.93  --prep_upred                            true
% 4.11/0.93  --prep_sem_filter                       exhaustive
% 4.11/0.93  --prep_sem_filter_out                   false
% 4.11/0.93  --pred_elim                             true
% 4.11/0.93  --res_sim_input                         true
% 4.11/0.93  --eq_ax_congr_red                       true
% 4.11/0.93  --pure_diseq_elim                       true
% 4.11/0.93  --brand_transform                       false
% 4.11/0.93  --non_eq_to_eq                          false
% 4.11/0.93  --prep_def_merge                        true
% 4.11/0.93  --prep_def_merge_prop_impl              false
% 4.11/0.93  --prep_def_merge_mbd                    true
% 4.11/0.93  --prep_def_merge_tr_red                 false
% 4.11/0.93  --prep_def_merge_tr_cl                  false
% 4.11/0.93  --smt_preprocessing                     true
% 4.11/0.93  --smt_ac_axioms                         fast
% 4.11/0.93  --preprocessed_out                      false
% 4.11/0.93  --preprocessed_stats                    false
% 4.11/0.93  
% 4.11/0.93  ------ Abstraction refinement Options
% 4.11/0.93  
% 4.11/0.93  --abstr_ref                             []
% 4.11/0.93  --abstr_ref_prep                        false
% 4.11/0.93  --abstr_ref_until_sat                   false
% 4.11/0.93  --abstr_ref_sig_restrict                funpre
% 4.11/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/0.93  --abstr_ref_under                       []
% 4.11/0.93  
% 4.11/0.93  ------ SAT Options
% 4.11/0.93  
% 4.11/0.93  --sat_mode                              false
% 4.11/0.93  --sat_fm_restart_options                ""
% 4.11/0.93  --sat_gr_def                            false
% 4.11/0.93  --sat_epr_types                         true
% 4.11/0.93  --sat_non_cyclic_types                  false
% 4.11/0.93  --sat_finite_models                     false
% 4.11/0.93  --sat_fm_lemmas                         false
% 4.11/0.93  --sat_fm_prep                           false
% 4.11/0.93  --sat_fm_uc_incr                        true
% 4.11/0.93  --sat_out_model                         small
% 4.11/0.93  --sat_out_clauses                       false
% 4.11/0.93  
% 4.11/0.93  ------ QBF Options
% 4.11/0.93  
% 4.11/0.93  --qbf_mode                              false
% 4.11/0.93  --qbf_elim_univ                         false
% 4.11/0.93  --qbf_dom_inst                          none
% 4.11/0.93  --qbf_dom_pre_inst                      false
% 4.11/0.93  --qbf_sk_in                             false
% 4.11/0.93  --qbf_pred_elim                         true
% 4.11/0.93  --qbf_split                             512
% 4.11/0.93  
% 4.11/0.93  ------ BMC1 Options
% 4.11/0.93  
% 4.11/0.93  --bmc1_incremental                      false
% 4.11/0.93  --bmc1_axioms                           reachable_all
% 4.11/0.93  --bmc1_min_bound                        0
% 4.11/0.93  --bmc1_max_bound                        -1
% 4.11/0.93  --bmc1_max_bound_default                -1
% 4.11/0.93  --bmc1_symbol_reachability              true
% 4.11/0.93  --bmc1_property_lemmas                  false
% 4.11/0.93  --bmc1_k_induction                      false
% 4.11/0.93  --bmc1_non_equiv_states                 false
% 4.11/0.93  --bmc1_deadlock                         false
% 4.11/0.93  --bmc1_ucm                              false
% 4.11/0.93  --bmc1_add_unsat_core                   none
% 4.11/0.93  --bmc1_unsat_core_children              false
% 4.11/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/0.93  --bmc1_out_stat                         full
% 4.11/0.93  --bmc1_ground_init                      false
% 4.11/0.93  --bmc1_pre_inst_next_state              false
% 4.11/0.93  --bmc1_pre_inst_state                   false
% 4.11/0.93  --bmc1_pre_inst_reach_state             false
% 4.11/0.93  --bmc1_out_unsat_core                   false
% 4.11/0.93  --bmc1_aig_witness_out                  false
% 4.11/0.93  --bmc1_verbose                          false
% 4.11/0.93  --bmc1_dump_clauses_tptp                false
% 4.11/0.93  --bmc1_dump_unsat_core_tptp             false
% 4.11/0.93  --bmc1_dump_file                        -
% 4.11/0.93  --bmc1_ucm_expand_uc_limit              128
% 4.11/0.93  --bmc1_ucm_n_expand_iterations          6
% 4.11/0.93  --bmc1_ucm_extend_mode                  1
% 4.11/0.93  --bmc1_ucm_init_mode                    2
% 4.11/0.93  --bmc1_ucm_cone_mode                    none
% 4.11/0.93  --bmc1_ucm_reduced_relation_type        0
% 4.11/0.93  --bmc1_ucm_relax_model                  4
% 4.11/0.93  --bmc1_ucm_full_tr_after_sat            true
% 4.11/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/0.93  --bmc1_ucm_layered_model                none
% 4.11/0.93  --bmc1_ucm_max_lemma_size               10
% 4.11/0.93  
% 4.11/0.93  ------ AIG Options
% 4.11/0.93  
% 4.11/0.93  --aig_mode                              false
% 4.11/0.93  
% 4.11/0.93  ------ Instantiation Options
% 4.11/0.93  
% 4.11/0.93  --instantiation_flag                    true
% 4.11/0.93  --inst_sos_flag                         false
% 4.11/0.93  --inst_sos_phase                        true
% 4.11/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/0.93  --inst_lit_sel_side                     none
% 4.11/0.93  --inst_solver_per_active                1400
% 4.11/0.93  --inst_solver_calls_frac                1.
% 4.11/0.93  --inst_passive_queue_type               priority_queues
% 4.11/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/0.93  --inst_passive_queues_freq              [25;2]
% 4.11/0.93  --inst_dismatching                      true
% 4.11/0.93  --inst_eager_unprocessed_to_passive     true
% 4.11/0.93  --inst_prop_sim_given                   true
% 4.11/0.93  --inst_prop_sim_new                     false
% 4.11/0.93  --inst_subs_new                         false
% 4.11/0.93  --inst_eq_res_simp                      false
% 4.11/0.93  --inst_subs_given                       false
% 4.11/0.93  --inst_orphan_elimination               true
% 4.11/0.93  --inst_learning_loop_flag               true
% 4.11/0.93  --inst_learning_start                   3000
% 4.11/0.93  --inst_learning_factor                  2
% 4.11/0.93  --inst_start_prop_sim_after_learn       3
% 4.11/0.93  --inst_sel_renew                        solver
% 4.11/0.93  --inst_lit_activity_flag                true
% 4.11/0.93  --inst_restr_to_given                   false
% 4.11/0.93  --inst_activity_threshold               500
% 4.11/0.93  --inst_out_proof                        true
% 4.11/0.93  
% 4.11/0.93  ------ Resolution Options
% 4.11/0.93  
% 4.11/0.93  --resolution_flag                       false
% 4.11/0.93  --res_lit_sel                           adaptive
% 4.11/0.93  --res_lit_sel_side                      none
% 4.11/0.93  --res_ordering                          kbo
% 4.11/0.93  --res_to_prop_solver                    active
% 4.11/0.93  --res_prop_simpl_new                    false
% 4.11/0.93  --res_prop_simpl_given                  true
% 4.11/0.93  --res_passive_queue_type                priority_queues
% 4.11/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/0.93  --res_passive_queues_freq               [15;5]
% 4.11/0.93  --res_forward_subs                      full
% 4.11/0.93  --res_backward_subs                     full
% 4.11/0.93  --res_forward_subs_resolution           true
% 4.11/0.93  --res_backward_subs_resolution          true
% 4.11/0.93  --res_orphan_elimination                true
% 4.11/0.93  --res_time_limit                        2.
% 4.11/0.93  --res_out_proof                         true
% 4.11/0.93  
% 4.11/0.93  ------ Superposition Options
% 4.11/0.93  
% 4.11/0.93  --superposition_flag                    true
% 4.11/0.93  --sup_passive_queue_type                priority_queues
% 4.11/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/0.93  --sup_passive_queues_freq               [8;1;4]
% 4.11/0.93  --demod_completeness_check              fast
% 4.11/0.93  --demod_use_ground                      true
% 4.11/0.93  --sup_to_prop_solver                    passive
% 4.11/0.93  --sup_prop_simpl_new                    true
% 4.11/0.93  --sup_prop_simpl_given                  true
% 4.11/0.93  --sup_fun_splitting                     false
% 4.11/0.93  --sup_smt_interval                      50000
% 4.11/0.93  
% 4.11/0.93  ------ Superposition Simplification Setup
% 4.11/0.93  
% 4.11/0.93  --sup_indices_passive                   []
% 4.11/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.93  --sup_full_bw                           [BwDemod]
% 4.11/0.93  --sup_immed_triv                        [TrivRules]
% 4.11/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.93  --sup_immed_bw_main                     []
% 4.11/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.93  
% 4.11/0.93  ------ Combination Options
% 4.11/0.93  
% 4.11/0.93  --comb_res_mult                         3
% 4.11/0.93  --comb_sup_mult                         2
% 4.11/0.93  --comb_inst_mult                        10
% 4.11/0.93  
% 4.11/0.93  ------ Debug Options
% 4.11/0.93  
% 4.11/0.93  --dbg_backtrace                         false
% 4.11/0.93  --dbg_dump_prop_clauses                 false
% 4.11/0.93  --dbg_dump_prop_clauses_file            -
% 4.11/0.93  --dbg_out_stat                          false
% 4.11/0.93  
% 4.11/0.93  
% 4.11/0.93  
% 4.11/0.93  
% 4.11/0.93  ------ Proving...
% 4.11/0.93  
% 4.11/0.93  
% 4.11/0.93  % SZS status Theorem for theBenchmark.p
% 4.11/0.93  
% 4.11/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/0.93  
% 4.11/0.93  fof(f14,conjecture,(
% 4.11/0.93    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f15,negated_conjecture,(
% 4.11/0.93    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 4.11/0.93    inference(negated_conjecture,[],[f14])).
% 4.11/0.93  
% 4.11/0.93  fof(f31,plain,(
% 4.11/0.93    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 4.11/0.93    inference(ennf_transformation,[],[f15])).
% 4.11/0.93  
% 4.11/0.93  fof(f55,plain,(
% 4.11/0.93    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8)))),
% 4.11/0.93    introduced(choice_axiom,[])).
% 4.11/0.93  
% 4.11/0.93  fof(f56,plain,(
% 4.11/0.93    (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 4.11/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f31,f55])).
% 4.11/0.93  
% 4.11/0.93  fof(f101,plain,(
% 4.11/0.93    r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 4.11/0.93    inference(cnf_transformation,[],[f56])).
% 4.11/0.93  
% 4.11/0.93  fof(f11,axiom,(
% 4.11/0.93    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f32,plain,(
% 4.11/0.93    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 4.11/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.11/0.93  
% 4.11/0.93  fof(f33,plain,(
% 4.11/0.93    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 4.11/0.93    inference(definition_folding,[],[f11,f32])).
% 4.11/0.93  
% 4.11/0.93  fof(f52,plain,(
% 4.11/0.93    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 4.11/0.93    inference(nnf_transformation,[],[f33])).
% 4.11/0.93  
% 4.11/0.93  fof(f90,plain,(
% 4.11/0.93    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 4.11/0.93    inference(cnf_transformation,[],[f52])).
% 4.11/0.93  
% 4.11/0.93  fof(f111,plain,(
% 4.11/0.93    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 4.11/0.93    inference(equality_resolution,[],[f90])).
% 4.11/0.93  
% 4.11/0.93  fof(f46,plain,(
% 4.11/0.93    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 4.11/0.93    inference(nnf_transformation,[],[f32])).
% 4.11/0.93  
% 4.11/0.93  fof(f47,plain,(
% 4.11/0.93    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 4.11/0.93    inference(rectify,[],[f46])).
% 4.11/0.93  
% 4.11/0.93  fof(f50,plain,(
% 4.11/0.93    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))))),
% 4.11/0.93    introduced(choice_axiom,[])).
% 4.11/0.93  
% 4.11/0.93  fof(f49,plain,(
% 4.11/0.93    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK4(X0,X1,X2) = X3 & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))))) )),
% 4.11/0.93    introduced(choice_axiom,[])).
% 4.11/0.93  
% 4.11/0.93  fof(f48,plain,(
% 4.11/0.93    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK3(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 4.11/0.93    introduced(choice_axiom,[])).
% 4.11/0.93  
% 4.11/0.93  fof(f51,plain,(
% 4.11/0.93    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK3(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK4(X0,X1,X2)),X0) & k1_relat_1(sK4(X0,X1,X2)) = X1 & sK3(X0,X1,X2) = sK4(X0,X1,X2) & v1_funct_1(sK4(X0,X1,X2)) & v1_relat_1(sK4(X0,X1,X2))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) & k1_relat_1(sK5(X0,X1,X6)) = X1 & sK5(X0,X1,X6) = X6 & v1_funct_1(sK5(X0,X1,X6)) & v1_relat_1(sK5(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 4.11/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f47,f50,f49,f48])).
% 4.11/0.93  
% 4.11/0.93  fof(f80,plain,(
% 4.11/0.93    ( ! [X6,X2,X0,X1] : (sK5(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f51])).
% 4.11/0.93  
% 4.11/0.93  fof(f82,plain,(
% 4.11/0.93    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK5(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f51])).
% 4.11/0.93  
% 4.11/0.93  fof(f8,axiom,(
% 4.11/0.93    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f21,plain,(
% 4.11/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 4.11/0.93    inference(ennf_transformation,[],[f8])).
% 4.11/0.93  
% 4.11/0.93  fof(f22,plain,(
% 4.11/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 4.11/0.93    inference(flattening,[],[f21])).
% 4.11/0.93  
% 4.11/0.93  fof(f73,plain,(
% 4.11/0.93    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f22])).
% 4.11/0.93  
% 4.11/0.93  fof(f81,plain,(
% 4.11/0.93    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK5(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f51])).
% 4.11/0.93  
% 4.11/0.93  fof(f12,axiom,(
% 4.11/0.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f27,plain,(
% 4.11/0.93    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/0.93    inference(ennf_transformation,[],[f12])).
% 4.11/0.93  
% 4.11/0.93  fof(f28,plain,(
% 4.11/0.93    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.93    inference(flattening,[],[f27])).
% 4.11/0.93  
% 4.11/0.93  fof(f93,plain,(
% 4.11/0.93    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f28])).
% 4.11/0.93  
% 4.11/0.93  fof(f102,plain,(
% 4.11/0.93    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)),
% 4.11/0.93    inference(cnf_transformation,[],[f56])).
% 4.11/0.93  
% 4.11/0.93  fof(f3,axiom,(
% 4.11/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f42,plain,(
% 4.11/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.11/0.93    inference(nnf_transformation,[],[f3])).
% 4.11/0.93  
% 4.11/0.93  fof(f43,plain,(
% 4.11/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.11/0.93    inference(flattening,[],[f42])).
% 4.11/0.93  
% 4.11/0.93  fof(f62,plain,(
% 4.11/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.11/0.93    inference(cnf_transformation,[],[f43])).
% 4.11/0.93  
% 4.11/0.93  fof(f104,plain,(
% 4.11/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.11/0.93    inference(equality_resolution,[],[f62])).
% 4.11/0.93  
% 4.11/0.93  fof(f64,plain,(
% 4.11/0.93    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f43])).
% 4.11/0.93  
% 4.11/0.93  fof(f10,axiom,(
% 4.11/0.93    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f25,plain,(
% 4.11/0.93    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.11/0.93    inference(ennf_transformation,[],[f10])).
% 4.11/0.93  
% 4.11/0.93  fof(f26,plain,(
% 4.11/0.93    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 4.11/0.93    inference(flattening,[],[f25])).
% 4.11/0.93  
% 4.11/0.93  fof(f77,plain,(
% 4.11/0.93    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f26])).
% 4.11/0.93  
% 4.11/0.93  fof(f94,plain,(
% 4.11/0.93    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f28])).
% 4.11/0.93  
% 4.11/0.93  fof(f9,axiom,(
% 4.11/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f23,plain,(
% 4.11/0.93    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.93    inference(ennf_transformation,[],[f9])).
% 4.11/0.93  
% 4.11/0.93  fof(f24,plain,(
% 4.11/0.93    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.11/0.93    inference(flattening,[],[f23])).
% 4.11/0.93  
% 4.11/0.93  fof(f75,plain,(
% 4.11/0.93    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.11/0.93    inference(cnf_transformation,[],[f24])).
% 4.11/0.93  
% 4.11/0.93  fof(f5,axiom,(
% 4.11/0.93    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f17,plain,(
% 4.11/0.93    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 4.11/0.93    inference(ennf_transformation,[],[f5])).
% 4.11/0.93  
% 4.11/0.93  fof(f67,plain,(
% 4.11/0.93    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f17])).
% 4.11/0.93  
% 4.11/0.93  fof(f13,axiom,(
% 4.11/0.93    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f29,plain,(
% 4.11/0.93    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.11/0.93    inference(ennf_transformation,[],[f13])).
% 4.11/0.93  
% 4.11/0.93  fof(f30,plain,(
% 4.11/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.11/0.93    inference(flattening,[],[f29])).
% 4.11/0.93  
% 4.11/0.93  fof(f53,plain,(
% 4.11/0.93    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)))),
% 4.11/0.93    introduced(choice_axiom,[])).
% 4.11/0.93  
% 4.11/0.93  fof(f54,plain,(
% 4.11/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.11/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f53])).
% 4.11/0.93  
% 4.11/0.93  fof(f97,plain,(
% 4.11/0.93    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK6(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f54])).
% 4.11/0.93  
% 4.11/0.93  fof(f115,plain,(
% 4.11/0.93    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK6(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.11/0.93    inference(equality_resolution,[],[f97])).
% 4.11/0.93  
% 4.11/0.93  fof(f6,axiom,(
% 4.11/0.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f18,plain,(
% 4.11/0.93    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/0.93    inference(ennf_transformation,[],[f6])).
% 4.11/0.93  
% 4.11/0.93  fof(f19,plain,(
% 4.11/0.93    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.93    inference(flattening,[],[f18])).
% 4.11/0.93  
% 4.11/0.93  fof(f45,plain,(
% 4.11/0.93    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.93    inference(nnf_transformation,[],[f19])).
% 4.11/0.93  
% 4.11/0.93  fof(f68,plain,(
% 4.11/0.93    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f45])).
% 4.11/0.93  
% 4.11/0.93  fof(f107,plain,(
% 4.11/0.93    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.93    inference(equality_resolution,[],[f68])).
% 4.11/0.93  
% 4.11/0.93  fof(f1,axiom,(
% 4.11/0.93    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f34,plain,(
% 4.11/0.93    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 4.11/0.93    inference(nnf_transformation,[],[f1])).
% 4.11/0.93  
% 4.11/0.93  fof(f35,plain,(
% 4.11/0.93    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.11/0.93    inference(rectify,[],[f34])).
% 4.11/0.93  
% 4.11/0.93  fof(f36,plain,(
% 4.11/0.93    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 4.11/0.93    introduced(choice_axiom,[])).
% 4.11/0.93  
% 4.11/0.93  fof(f37,plain,(
% 4.11/0.93    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 4.11/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 4.11/0.93  
% 4.11/0.93  fof(f57,plain,(
% 4.11/0.93    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f37])).
% 4.11/0.93  
% 4.11/0.93  fof(f78,plain,(
% 4.11/0.93    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f51])).
% 4.11/0.93  
% 4.11/0.93  fof(f79,plain,(
% 4.11/0.93    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK5(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f51])).
% 4.11/0.93  
% 4.11/0.93  fof(f7,axiom,(
% 4.11/0.93    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 4.11/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.93  
% 4.11/0.93  fof(f20,plain,(
% 4.11/0.93    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 4.11/0.93    inference(ennf_transformation,[],[f7])).
% 4.11/0.93  
% 4.11/0.93  fof(f72,plain,(
% 4.11/0.93    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 4.11/0.93    inference(cnf_transformation,[],[f20])).
% 4.11/0.93  
% 4.11/0.93  cnf(c_45,negated_conjecture,
% 4.11/0.93      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
% 4.11/0.93      inference(cnf_transformation,[],[f101]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_9673,plain,
% 4.11/0.93      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 4.11/0.93      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_34,plain,
% 4.11/0.93      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 4.11/0.93      inference(cnf_transformation,[],[f111]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_9677,plain,
% 4.11/0.93      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 4.11/0.93      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_30,plain,
% 4.11/0.93      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK5(X0,X1,X3) = X3 ),
% 4.11/0.93      inference(cnf_transformation,[],[f80]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_9681,plain,
% 4.11/0.93      ( sK5(X0,X1,X2) = X2
% 4.11/0.93      | sP0(X0,X1,X3) != iProver_top
% 4.11/0.93      | r2_hidden(X2,X3) != iProver_top ),
% 4.11/0.93      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_11290,plain,
% 4.11/0.93      ( sK5(X0,X1,X2) = X2
% 4.11/0.93      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 4.11/0.93      inference(superposition,[status(thm)],[c_9677,c_9681]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_11680,plain,
% 4.11/0.93      ( sK5(sK8,sK7,sK9) = sK9 ),
% 4.11/0.93      inference(superposition,[status(thm)],[c_9673,c_11290]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_28,plain,
% 4.11/0.93      ( ~ sP0(X0,X1,X2)
% 4.11/0.93      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0)
% 4.11/0.93      | ~ r2_hidden(X3,X2) ),
% 4.11/0.93      inference(cnf_transformation,[],[f82]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_9683,plain,
% 4.11/0.93      ( sP0(X0,X1,X2) != iProver_top
% 4.11/0.93      | r1_tarski(k2_relat_1(sK5(X0,X1,X3)),X0) = iProver_top
% 4.11/0.93      | r2_hidden(X3,X2) != iProver_top ),
% 4.11/0.93      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_11976,plain,
% 4.11/0.93      ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) = iProver_top
% 4.11/0.93      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 4.11/0.93      inference(superposition,[status(thm)],[c_9677,c_9683]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_17604,plain,
% 4.11/0.93      ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
% 4.11/0.93      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
% 4.11/0.93      inference(superposition,[status(thm)],[c_11680,c_11976]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_16,plain,
% 4.11/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.93      | ~ r1_tarski(k2_relat_1(X0),X2)
% 4.11/0.93      | ~ r1_tarski(k1_relat_1(X0),X1)
% 4.11/0.93      | ~ v1_relat_1(X0) ),
% 4.11/0.93      inference(cnf_transformation,[],[f73]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_9691,plain,
% 4.11/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 4.11/0.93      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 4.11/0.93      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 4.11/0.93      | v1_relat_1(X0) != iProver_top ),
% 4.11/0.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_29,plain,
% 4.11/0.93      ( ~ sP0(X0,X1,X2)
% 4.11/0.93      | ~ r2_hidden(X3,X2)
% 4.11/0.93      | k1_relat_1(sK5(X0,X1,X3)) = X1 ),
% 4.11/0.93      inference(cnf_transformation,[],[f81]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_9682,plain,
% 4.11/0.93      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 4.11/0.93      | sP0(X0,X1,X3) != iProver_top
% 4.11/0.93      | r2_hidden(X2,X3) != iProver_top ),
% 4.11/0.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_11624,plain,
% 4.11/0.93      ( k1_relat_1(sK5(X0,X1,X2)) = X1
% 4.11/0.93      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 4.11/0.93      inference(superposition,[status(thm)],[c_9677,c_9682]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_11954,plain,
% 4.11/0.93      ( k1_relat_1(sK5(sK8,sK7,sK9)) = sK7 ),
% 4.11/0.93      inference(superposition,[status(thm)],[c_9673,c_11624]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_11956,plain,
% 4.11/0.93      ( k1_relat_1(sK9) = sK7 ),
% 4.11/0.93      inference(light_normalisation,[status(thm)],[c_11954,c_11680]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_36,plain,
% 4.11/0.93      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 4.11/0.93      | ~ v1_relat_1(X0)
% 4.11/0.93      | ~ v1_funct_1(X0) ),
% 4.11/0.93      inference(cnf_transformation,[],[f93]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_44,negated_conjecture,
% 4.11/0.93      ( ~ v1_funct_2(sK9,sK7,sK8)
% 4.11/0.93      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.93      | ~ v1_funct_1(sK9) ),
% 4.11/0.93      inference(cnf_transformation,[],[f102]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_670,plain,
% 4.11/0.93      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.93      | ~ v1_relat_1(X0)
% 4.11/0.93      | ~ v1_funct_1(X0)
% 4.11/0.93      | ~ v1_funct_1(sK9)
% 4.11/0.93      | k2_relat_1(X0) != sK8
% 4.11/0.93      | k1_relat_1(X0) != sK7
% 4.11/0.93      | sK9 != X0 ),
% 4.11/0.93      inference(resolution_lifted,[status(thm)],[c_36,c_44]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_671,plain,
% 4.11/0.93      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.93      | ~ v1_relat_1(sK9)
% 4.11/0.93      | ~ v1_funct_1(sK9)
% 4.11/0.93      | k2_relat_1(sK9) != sK8
% 4.11/0.93      | k1_relat_1(sK9) != sK7 ),
% 4.11/0.93      inference(unflattening,[status(thm)],[c_670]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_9672,plain,
% 4.11/0.93      ( k2_relat_1(sK9) != sK8
% 4.11/0.93      | k1_relat_1(sK9) != sK7
% 4.11/0.93      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 4.11/0.93      | v1_relat_1(sK9) != iProver_top
% 4.11/0.93      | v1_funct_1(sK9) != iProver_top ),
% 4.11/0.93      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_12443,plain,
% 4.11/0.93      ( k2_relat_1(sK9) != sK8
% 4.11/0.93      | sK7 != sK7
% 4.11/0.93      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 4.11/0.93      | v1_relat_1(sK9) != iProver_top
% 4.11/0.93      | v1_funct_1(sK9) != iProver_top ),
% 4.11/0.93      inference(demodulation,[status(thm)],[c_11956,c_9672]) ).
% 4.11/0.93  
% 4.11/0.93  cnf(c_12444,plain,
% 4.11/0.93      ( k2_relat_1(sK9) != sK8
% 4.11/0.93      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 4.11/0.94      | v1_relat_1(sK9) != iProver_top
% 4.11/0.94      | v1_funct_1(sK9) != iProver_top ),
% 4.11/0.94      inference(equality_resolution_simp,[status(thm)],[c_12443]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_46,plain,
% 4.11/0.94      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_7,plain,
% 4.11/0.94      ( r1_tarski(X0,X0) ),
% 4.11/0.94      inference(cnf_transformation,[],[f104]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_143,plain,
% 4.11/0.94      ( r1_tarski(sK9,sK9) ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_7]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_5,plain,
% 4.11/0.94      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 4.11/0.94      inference(cnf_transformation,[],[f64]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_147,plain,
% 4.11/0.94      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_5]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_19,plain,
% 4.11/0.94      ( ~ v1_funct_2(X0,X1,X2)
% 4.11/0.94      | v1_partfun1(X0,X1)
% 4.11/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.94      | ~ v1_funct_1(X0)
% 4.11/0.94      | v1_xboole_0(X2) ),
% 4.11/0.94      inference(cnf_transformation,[],[f77]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_577,plain,
% 4.11/0.94      ( v1_partfun1(X0,X1)
% 4.11/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.94      | ~ v1_relat_1(X3)
% 4.11/0.94      | ~ v1_funct_1(X0)
% 4.11/0.94      | ~ v1_funct_1(X3)
% 4.11/0.94      | v1_xboole_0(X2)
% 4.11/0.94      | X3 != X0
% 4.11/0.94      | k2_relat_1(X3) != X2
% 4.11/0.94      | k1_relat_1(X3) != X1 ),
% 4.11/0.94      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_578,plain,
% 4.11/0.94      ( v1_partfun1(X0,k1_relat_1(X0))
% 4.11/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 4.11/0.94      | ~ v1_relat_1(X0)
% 4.11/0.94      | ~ v1_funct_1(X0)
% 4.11/0.94      | v1_xboole_0(k2_relat_1(X0)) ),
% 4.11/0.94      inference(unflattening,[status(thm)],[c_577]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_35,plain,
% 4.11/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 4.11/0.94      | ~ v1_relat_1(X0)
% 4.11/0.94      | ~ v1_funct_1(X0) ),
% 4.11/0.94      inference(cnf_transformation,[],[f94]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_582,plain,
% 4.11/0.94      ( v1_partfun1(X0,k1_relat_1(X0))
% 4.11/0.94      | ~ v1_relat_1(X0)
% 4.11/0.94      | ~ v1_funct_1(X0)
% 4.11/0.94      | v1_xboole_0(k2_relat_1(X0)) ),
% 4.11/0.94      inference(global_propositional_subsumption,
% 4.11/0.94                [status(thm)],
% 4.11/0.94                [c_578,c_35]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_17,plain,
% 4.11/0.94      ( v1_funct_2(X0,X1,X2)
% 4.11/0.94      | ~ v1_partfun1(X0,X1)
% 4.11/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.94      | ~ v1_funct_1(X0) ),
% 4.11/0.94      inference(cnf_transformation,[],[f75]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_657,plain,
% 4.11/0.94      ( ~ v1_partfun1(X0,X1)
% 4.11/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.94      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | ~ v1_funct_1(X0)
% 4.11/0.94      | ~ v1_funct_1(sK9)
% 4.11/0.94      | sK8 != X2
% 4.11/0.94      | sK7 != X1
% 4.11/0.94      | sK9 != X0 ),
% 4.11/0.94      inference(resolution_lifted,[status(thm)],[c_17,c_44]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_658,plain,
% 4.11/0.94      ( ~ v1_partfun1(sK9,sK7)
% 4.11/0.94      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | ~ v1_funct_1(sK9) ),
% 4.11/0.94      inference(unflattening,[status(thm)],[c_657]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_810,plain,
% 4.11/0.94      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | ~ v1_relat_1(X0)
% 4.11/0.94      | ~ v1_funct_1(X0)
% 4.11/0.94      | ~ v1_funct_1(sK9)
% 4.11/0.94      | v1_xboole_0(k2_relat_1(X0))
% 4.11/0.94      | k1_relat_1(X0) != sK7
% 4.11/0.94      | sK9 != X0 ),
% 4.11/0.94      inference(resolution_lifted,[status(thm)],[c_582,c_658]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_811,plain,
% 4.11/0.94      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | ~ v1_relat_1(sK9)
% 4.11/0.94      | ~ v1_funct_1(sK9)
% 4.11/0.94      | v1_xboole_0(k2_relat_1(sK9))
% 4.11/0.94      | k1_relat_1(sK9) != sK7 ),
% 4.11/0.94      inference(unflattening,[status(thm)],[c_810]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_812,plain,
% 4.11/0.94      ( k1_relat_1(sK9) != sK7
% 4.11/0.94      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 4.11/0.94      | v1_relat_1(sK9) != iProver_top
% 4.11/0.94      | v1_funct_1(sK9) != iProver_top
% 4.11/0.94      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_811]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10,plain,
% 4.11/0.94      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 4.11/0.94      inference(cnf_transformation,[],[f67]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_41,plain,
% 4.11/0.94      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 4.11/0.94      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 4.11/0.94      | ~ v1_relat_1(X0)
% 4.11/0.94      | ~ v1_funct_1(X0) ),
% 4.11/0.94      inference(cnf_transformation,[],[f115]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_689,plain,
% 4.11/0.94      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | r2_hidden(sK6(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 4.11/0.94      | ~ v1_relat_1(X0)
% 4.11/0.94      | ~ v1_funct_1(X0)
% 4.11/0.94      | ~ v1_funct_1(sK9)
% 4.11/0.94      | k1_relat_1(X0) != sK7
% 4.11/0.94      | sK8 != X1
% 4.11/0.94      | sK9 != X0 ),
% 4.11/0.94      inference(resolution_lifted,[status(thm)],[c_41,c_44]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_690,plain,
% 4.11/0.94      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 4.11/0.94      | ~ v1_relat_1(sK9)
% 4.11/0.94      | ~ v1_funct_1(sK9)
% 4.11/0.94      | k1_relat_1(sK9) != sK7 ),
% 4.11/0.94      inference(unflattening,[status(thm)],[c_689]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_3020,plain,
% 4.11/0.94      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 4.11/0.94      | ~ v1_relat_1(sK9)
% 4.11/0.94      | ~ v1_xboole_0(X0)
% 4.11/0.94      | k1_relat_1(sK9) != sK7
% 4.11/0.94      | sK9 != X0 ),
% 4.11/0.94      inference(resolution_lifted,[status(thm)],[c_10,c_690]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_3021,plain,
% 4.11/0.94      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | r2_hidden(sK6(k1_relat_1(sK9),sK8,sK9),k1_relat_1(sK9))
% 4.11/0.94      | ~ v1_relat_1(sK9)
% 4.11/0.94      | ~ v1_xboole_0(sK9)
% 4.11/0.94      | k1_relat_1(sK9) != sK7 ),
% 4.11/0.94      inference(unflattening,[status(thm)],[c_3020]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_14,plain,
% 4.11/0.94      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.94      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 4.11/0.94      | ~ v1_relat_1(X1)
% 4.11/0.94      | ~ v1_funct_1(X1) ),
% 4.11/0.94      inference(cnf_transformation,[],[f107]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_2781,plain,
% 4.11/0.94      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.94      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 4.11/0.94      | ~ v1_relat_1(X1)
% 4.11/0.94      | ~ v1_xboole_0(X2)
% 4.11/0.94      | X1 != X2 ),
% 4.11/0.94      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_2782,plain,
% 4.11/0.94      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.94      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 4.11/0.94      | ~ v1_relat_1(X1)
% 4.11/0.94      | ~ v1_xboole_0(X1) ),
% 4.11/0.94      inference(unflattening,[status(thm)],[c_2781]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_1,plain,
% 4.11/0.94      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 4.11/0.94      inference(cnf_transformation,[],[f57]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_2794,plain,
% 4.11/0.94      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.94      | ~ v1_relat_1(X1)
% 4.11/0.94      | ~ v1_xboole_0(X1) ),
% 4.11/0.94      inference(forward_subsumption_resolution,
% 4.11/0.94                [status(thm)],
% 4.11/0.94                [c_2782,c_1]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_3028,plain,
% 4.11/0.94      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.11/0.94      | ~ v1_relat_1(sK9)
% 4.11/0.94      | ~ v1_xboole_0(sK9)
% 4.11/0.94      | k1_relat_1(sK9) != sK7 ),
% 4.11/0.94      inference(forward_subsumption_resolution,
% 4.11/0.94                [status(thm)],
% 4.11/0.94                [c_3021,c_2794]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_3033,plain,
% 4.11/0.94      ( k1_relat_1(sK9) != sK7
% 4.11/0.94      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 4.11/0.94      | v1_relat_1(sK9) != iProver_top
% 4.11/0.94      | v1_xboole_0(sK9) != iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_3028]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10201,plain,
% 4.11/0.94      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_34]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10204,plain,
% 4.11/0.94      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_10201]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_32,plain,
% 4.11/0.94      ( ~ sP0(X0,X1,X2)
% 4.11/0.94      | ~ r2_hidden(X3,X2)
% 4.11/0.94      | v1_relat_1(sK5(X0,X1,X3)) ),
% 4.11/0.94      inference(cnf_transformation,[],[f78]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10077,plain,
% 4.11/0.94      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 4.11/0.94      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 4.11/0.94      | v1_relat_1(sK5(X0,X1,sK9)) ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_32]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10361,plain,
% 4.11/0.94      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 4.11/0.94      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 4.11/0.94      | v1_relat_1(sK5(sK8,sK7,sK9)) ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_10077]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10363,plain,
% 4.11/0.94      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
% 4.11/0.94      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
% 4.11/0.94      | v1_relat_1(sK5(sK8,sK7,sK9)) = iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_10361]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10114,plain,
% 4.11/0.94      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 4.11/0.94      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 4.11/0.94      | sK5(X0,X1,sK9) = sK9 ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_30]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10360,plain,
% 4.11/0.94      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 4.11/0.94      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 4.11/0.94      | sK5(sK8,sK7,sK9) = sK9 ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_10114]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_8756,plain,
% 4.11/0.94      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 4.11/0.94      theory(equality) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10451,plain,
% 4.11/0.94      ( v1_relat_1(X0)
% 4.11/0.94      | ~ v1_relat_1(sK5(sK8,sK7,sK9))
% 4.11/0.94      | X0 != sK5(sK8,sK7,sK9) ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_8756]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10470,plain,
% 4.11/0.94      ( X0 != sK5(sK8,sK7,sK9)
% 4.11/0.94      | v1_relat_1(X0) = iProver_top
% 4.11/0.94      | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_10451]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_10472,plain,
% 4.11/0.94      ( sK9 != sK5(sK8,sK7,sK9)
% 4.11/0.94      | v1_relat_1(sK5(sK8,sK7,sK9)) != iProver_top
% 4.11/0.94      | v1_relat_1(sK9) = iProver_top ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_10470]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_8747,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_11107,plain,
% 4.11/0.94      ( X0 != X1 | X0 = sK5(sK8,sK7,sK9) | sK5(sK8,sK7,sK9) != X1 ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_8747]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_11108,plain,
% 4.11/0.94      ( sK5(sK8,sK7,sK9) != sK9 | sK9 = sK5(sK8,sK7,sK9) | sK9 != sK9 ),
% 4.11/0.94      inference(instantiation,[status(thm)],[c_11107]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_31,plain,
% 4.11/0.94      ( ~ sP0(X0,X1,X2)
% 4.11/0.94      | ~ r2_hidden(X3,X2)
% 4.11/0.94      | v1_funct_1(sK5(X0,X1,X3)) ),
% 4.11/0.94      inference(cnf_transformation,[],[f79]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_9680,plain,
% 4.11/0.94      ( sP0(X0,X1,X2) != iProver_top
% 4.11/0.94      | r2_hidden(X3,X2) != iProver_top
% 4.11/0.94      | v1_funct_1(sK5(X0,X1,X3)) = iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_11464,plain,
% 4.11/0.94      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 4.11/0.94      | v1_funct_1(sK5(X2,X1,X0)) = iProver_top ),
% 4.11/0.94      inference(superposition,[status(thm)],[c_9677,c_9680]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_11866,plain,
% 4.11/0.94      ( v1_funct_1(sK5(sK8,sK7,sK9)) = iProver_top ),
% 4.11/0.94      inference(superposition,[status(thm)],[c_9673,c_11464]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_11868,plain,
% 4.11/0.94      ( v1_funct_1(sK9) = iProver_top ),
% 4.11/0.94      inference(light_normalisation,[status(thm)],[c_11866,c_11680]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_9676,plain,
% 4.11/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 4.11/0.94      | v1_relat_1(X0) != iProver_top
% 4.11/0.94      | v1_funct_1(X0) != iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_12520,plain,
% 4.11/0.94      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
% 4.11/0.94      | v1_relat_1(sK9) != iProver_top
% 4.11/0.94      | v1_funct_1(sK9) != iProver_top ),
% 4.11/0.94      inference(superposition,[status(thm)],[c_11956,c_9676]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_12731,plain,
% 4.11/0.94      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top ),
% 4.11/0.94      inference(global_propositional_subsumption,
% 4.11/0.94                [status(thm)],
% 4.11/0.94                [c_12520,c_45,c_46,c_143,c_147,c_10201,c_10204,c_10363,
% 4.11/0.94                 c_10360,c_10472,c_11108,c_11868]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_15,plain,
% 4.11/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.11/0.94      | ~ v1_xboole_0(X2)
% 4.11/0.94      | v1_xboole_0(X0) ),
% 4.11/0.94      inference(cnf_transformation,[],[f72]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_9692,plain,
% 4.11/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.11/0.94      | v1_xboole_0(X2) != iProver_top
% 4.11/0.94      | v1_xboole_0(X0) = iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_12737,plain,
% 4.11/0.94      ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
% 4.11/0.94      | v1_xboole_0(sK9) = iProver_top ),
% 4.11/0.94      inference(superposition,[status(thm)],[c_12731,c_9692]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_12891,plain,
% 4.11/0.94      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top ),
% 4.11/0.94      inference(global_propositional_subsumption,
% 4.11/0.94                [status(thm)],
% 4.11/0.94                [c_12444,c_45,c_46,c_143,c_147,c_812,c_3033,c_10201,
% 4.11/0.94                 c_10204,c_10363,c_10360,c_10472,c_11108,c_11868,c_11956,
% 4.11/0.94                 c_12737]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_13843,plain,
% 4.11/0.94      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 4.11/0.94      | r1_tarski(k1_relat_1(sK9),sK7) != iProver_top
% 4.11/0.94      | v1_relat_1(sK9) != iProver_top ),
% 4.11/0.94      inference(superposition,[status(thm)],[c_9691,c_12891]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_13847,plain,
% 4.11/0.94      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 4.11/0.94      | r1_tarski(sK7,sK7) != iProver_top
% 4.11/0.94      | v1_relat_1(sK9) != iProver_top ),
% 4.11/0.94      inference(light_normalisation,[status(thm)],[c_13843,c_11956]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_13875,plain,
% 4.11/0.94      ( r1_tarski(sK7,sK7) != iProver_top
% 4.11/0.94      | r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
% 4.11/0.94      inference(global_propositional_subsumption,
% 4.11/0.94                [status(thm)],
% 4.11/0.94                [c_13847,c_45,c_46,c_143,c_147,c_10201,c_10204,c_10363,
% 4.11/0.94                 c_10360,c_10472,c_11108]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_13876,plain,
% 4.11/0.94      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top
% 4.11/0.94      | r1_tarski(sK7,sK7) != iProver_top ),
% 4.11/0.94      inference(renaming,[status(thm)],[c_13875]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_9699,plain,
% 4.11/0.94      ( r1_tarski(X0,X0) = iProver_top ),
% 4.11/0.94      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(c_13881,plain,
% 4.11/0.94      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
% 4.11/0.94      inference(forward_subsumption_resolution,
% 4.11/0.94                [status(thm)],
% 4.11/0.94                [c_13876,c_9699]) ).
% 4.11/0.94  
% 4.11/0.94  cnf(contradiction,plain,
% 4.11/0.94      ( $false ),
% 4.11/0.94      inference(minisat,[status(thm)],[c_17604,c_13881,c_46]) ).
% 4.11/0.94  
% 4.11/0.94  
% 4.11/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/0.94  
% 4.11/0.94  ------                               Statistics
% 4.11/0.94  
% 4.11/0.94  ------ General
% 4.11/0.94  
% 4.11/0.94  abstr_ref_over_cycles:                  0
% 4.11/0.94  abstr_ref_under_cycles:                 0
% 4.11/0.94  gc_basic_clause_elim:                   0
% 4.11/0.94  forced_gc_time:                         0
% 4.11/0.94  parsing_time:                           0.009
% 4.11/0.94  unif_index_cands_time:                  0.
% 4.11/0.94  unif_index_add_time:                    0.
% 4.11/0.94  orderings_time:                         0.
% 4.11/0.94  out_proof_time:                         0.017
% 4.11/0.94  total_time:                             0.469
% 4.11/0.94  num_of_symbols:                         59
% 4.11/0.94  num_of_terms:                           10367
% 4.11/0.94  
% 4.11/0.94  ------ Preprocessing
% 4.11/0.94  
% 4.11/0.94  num_of_splits:                          2
% 4.11/0.94  num_of_split_atoms:                     2
% 4.11/0.94  num_of_reused_defs:                     0
% 4.11/0.94  num_eq_ax_congr_red:                    48
% 4.11/0.94  num_of_sem_filtered_clauses:            1
% 4.11/0.94  num_of_subtypes:                        0
% 4.11/0.94  monotx_restored_types:                  0
% 4.11/0.94  sat_num_of_epr_types:                   0
% 4.11/0.94  sat_num_of_non_cyclic_types:            0
% 4.11/0.94  sat_guarded_non_collapsed_types:        0
% 4.11/0.94  num_pure_diseq_elim:                    0
% 4.11/0.94  simp_replaced_by:                       0
% 4.11/0.94  res_preprocessed:                       194
% 4.11/0.94  prep_upred:                             0
% 4.11/0.94  prep_unflattend:                        282
% 4.11/0.94  smt_new_axioms:                         0
% 4.11/0.94  pred_elim_cands:                        7
% 4.11/0.94  pred_elim:                              2
% 4.11/0.94  pred_elim_cl:                           1
% 4.11/0.94  pred_elim_cycles:                       11
% 4.11/0.94  merged_defs:                            8
% 4.11/0.94  merged_defs_ncl:                        0
% 4.11/0.94  bin_hyper_res:                          8
% 4.11/0.94  prep_cycles:                            4
% 4.11/0.94  pred_elim_time:                         0.121
% 4.11/0.94  splitting_time:                         0.
% 4.11/0.94  sem_filter_time:                        0.
% 4.11/0.94  monotx_time:                            0.
% 4.11/0.94  subtype_inf_time:                       0.
% 4.11/0.94  
% 4.11/0.94  ------ Problem properties
% 4.11/0.94  
% 4.11/0.94  clauses:                                40
% 4.11/0.94  conjectures:                            1
% 4.11/0.94  epr:                                    5
% 4.11/0.94  horn:                                   30
% 4.11/0.94  ground:                                 6
% 4.11/0.94  unary:                                  3
% 4.11/0.94  binary:                                 9
% 4.11/0.94  lits:                                   127
% 4.11/0.94  lits_eq:                                15
% 4.11/0.94  fd_pure:                                0
% 4.11/0.94  fd_pseudo:                              0
% 4.11/0.94  fd_cond:                                0
% 4.11/0.94  fd_pseudo_cond:                         3
% 4.11/0.94  ac_symbols:                             0
% 4.11/0.94  
% 4.11/0.94  ------ Propositional Solver
% 4.11/0.94  
% 4.11/0.94  prop_solver_calls:                      28
% 4.11/0.94  prop_fast_solver_calls:                 3489
% 4.11/0.94  smt_solver_calls:                       0
% 4.11/0.94  smt_fast_solver_calls:                  0
% 4.11/0.94  prop_num_of_clauses:                    4070
% 4.11/0.94  prop_preprocess_simplified:             12133
% 4.11/0.94  prop_fo_subsumed:                       99
% 4.11/0.94  prop_solver_time:                       0.
% 4.11/0.94  smt_solver_time:                        0.
% 4.11/0.94  smt_fast_solver_time:                   0.
% 4.11/0.94  prop_fast_solver_time:                  0.
% 4.11/0.94  prop_unsat_core_time:                   0.
% 4.11/0.94  
% 4.11/0.94  ------ QBF
% 4.11/0.94  
% 4.11/0.94  qbf_q_res:                              0
% 4.11/0.94  qbf_num_tautologies:                    0
% 4.11/0.94  qbf_prep_cycles:                        0
% 4.11/0.94  
% 4.11/0.94  ------ BMC1
% 4.11/0.94  
% 4.11/0.94  bmc1_current_bound:                     -1
% 4.11/0.94  bmc1_last_solved_bound:                 -1
% 4.11/0.94  bmc1_unsat_core_size:                   -1
% 4.11/0.94  bmc1_unsat_core_parents_size:           -1
% 4.11/0.94  bmc1_merge_next_fun:                    0
% 4.11/0.94  bmc1_unsat_core_clauses_time:           0.
% 4.11/0.94  
% 4.11/0.94  ------ Instantiation
% 4.11/0.94  
% 4.11/0.94  inst_num_of_clauses:                    863
% 4.11/0.94  inst_num_in_passive:                    109
% 4.11/0.94  inst_num_in_active:                     375
% 4.11/0.94  inst_num_in_unprocessed:                379
% 4.11/0.94  inst_num_of_loops:                      530
% 4.11/0.94  inst_num_of_learning_restarts:          0
% 4.11/0.94  inst_num_moves_active_passive:          152
% 4.11/0.94  inst_lit_activity:                      0
% 4.11/0.94  inst_lit_activity_moves:                0
% 4.11/0.94  inst_num_tautologies:                   0
% 4.11/0.94  inst_num_prop_implied:                  0
% 4.11/0.94  inst_num_existing_simplified:           0
% 4.11/0.94  inst_num_eq_res_simplified:             0
% 4.11/0.94  inst_num_child_elim:                    0
% 4.11/0.94  inst_num_of_dismatching_blockings:      282
% 4.11/0.94  inst_num_of_non_proper_insts:           923
% 4.11/0.94  inst_num_of_duplicates:                 0
% 4.11/0.94  inst_inst_num_from_inst_to_res:         0
% 4.11/0.94  inst_dismatching_checking_time:         0.
% 4.11/0.94  
% 4.11/0.94  ------ Resolution
% 4.11/0.94  
% 4.11/0.94  res_num_of_clauses:                     0
% 4.11/0.94  res_num_in_passive:                     0
% 4.11/0.94  res_num_in_active:                      0
% 4.11/0.94  res_num_of_loops:                       198
% 4.11/0.94  res_forward_subset_subsumed:            68
% 4.11/0.94  res_backward_subset_subsumed:           4
% 4.11/0.94  res_forward_subsumed:                   9
% 4.11/0.94  res_backward_subsumed:                  4
% 4.11/0.94  res_forward_subsumption_resolution:     6
% 4.11/0.94  res_backward_subsumption_resolution:    1
% 4.11/0.94  res_clause_to_clause_subsumption:       1046
% 4.11/0.94  res_orphan_elimination:                 0
% 4.11/0.94  res_tautology_del:                      83
% 4.11/0.94  res_num_eq_res_simplified:              0
% 4.11/0.94  res_num_sel_changes:                    0
% 4.11/0.94  res_moves_from_active_to_pass:          0
% 4.11/0.94  
% 4.11/0.94  ------ Superposition
% 4.11/0.94  
% 4.11/0.94  sup_time_total:                         0.
% 4.11/0.94  sup_time_generating:                    0.
% 4.11/0.94  sup_time_sim_full:                      0.
% 4.11/0.94  sup_time_sim_immed:                     0.
% 4.11/0.94  
% 4.11/0.94  sup_num_of_clauses:                     202
% 4.11/0.94  sup_num_in_active:                      98
% 4.11/0.94  sup_num_in_passive:                     104
% 4.11/0.94  sup_num_of_loops:                       105
% 4.11/0.94  sup_fw_superposition:                   87
% 4.11/0.94  sup_bw_superposition:                   123
% 4.11/0.94  sup_immediate_simplified:               34
% 4.11/0.94  sup_given_eliminated:                   0
% 4.11/0.94  comparisons_done:                       0
% 4.11/0.94  comparisons_avoided:                    2
% 4.11/0.94  
% 4.11/0.94  ------ Simplifications
% 4.11/0.94  
% 4.11/0.94  
% 4.11/0.94  sim_fw_subset_subsumed:                 14
% 4.11/0.94  sim_bw_subset_subsumed:                 5
% 4.11/0.94  sim_fw_subsumed:                        10
% 4.11/0.94  sim_bw_subsumed:                        0
% 4.11/0.94  sim_fw_subsumption_res:                 1
% 4.11/0.94  sim_bw_subsumption_res:                 0
% 4.11/0.94  sim_tautology_del:                      4
% 4.11/0.94  sim_eq_tautology_del:                   5
% 4.11/0.94  sim_eq_res_simp:                        5
% 4.11/0.94  sim_fw_demodulated:                     0
% 4.11/0.94  sim_bw_demodulated:                     8
% 4.11/0.94  sim_light_normalised:                   15
% 4.11/0.94  sim_joinable_taut:                      0
% 4.11/0.94  sim_joinable_simp:                      0
% 4.11/0.94  sim_ac_normalised:                      0
% 4.11/0.94  sim_smt_subsumption:                    0
% 4.11/0.94  
%------------------------------------------------------------------------------
