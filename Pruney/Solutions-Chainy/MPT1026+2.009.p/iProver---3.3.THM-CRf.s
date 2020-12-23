%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:14 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 930 expanded)
%              Number of clauses        :   96 ( 322 expanded)
%              Number of leaves         :   25 ( 238 expanded)
%              Depth                    :   21
%              Number of atoms          :  720 (5786 expanded)
%              Number of equality atoms :  253 (1751 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3,f39])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f30,plain,(
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
   => ( ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
        | ~ v1_funct_2(sK11,sK9,sK10)
        | ~ v1_funct_1(sK11) )
      & r2_hidden(sK11,k1_funct_2(sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
      | ~ v1_funct_2(sK11,sK9,sK10)
      | ~ v1_funct_1(sK11) )
    & r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f30,f55])).

fof(f96,plain,(
    r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
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

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f12,f31])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f91])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f52,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0)
        & k1_relat_1(sK8(X0,X1,X6)) = X1
        & sK8(X0,X1,X6) = X6
        & v1_funct_1(sK8(X0,X1,X6))
        & v1_relat_1(sK8(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
        & k1_relat_1(sK7(X0,X1,X2)) = X1
        & sK7(X0,X1,X2) = X3
        & v1_funct_1(sK7(X0,X1,X2))
        & v1_relat_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
              | sK6(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK6(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK6(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0)
              & k1_relat_1(sK7(X0,X1,X2)) = X1
              & sK6(X0,X1,X2) = sK7(X0,X1,X2)
              & v1_funct_1(sK7(X0,X1,X2))
              & v1_relat_1(sK7(X0,X1,X2)) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0)
                & k1_relat_1(sK8(X0,X1,X6)) = X1
                & sK8(X0,X1,X6) = X6
                & v1_funct_1(sK8(X0,X1,X6))
                & v1_relat_1(sK8(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f49,f52,f51,f50])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f46,f45,f44])).

fof(f69,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f101,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f97,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_2(sK11,sK9,sK10)
    | ~ v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7012,plain,
    ( m1_subset_1(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_7011,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8078,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7012,c_7011])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6985,plain,
    ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_35,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_6987,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_30,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK8(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6992,plain,
    ( k1_relat_1(sK8(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8244,plain,
    ( k1_relat_1(sK8(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6987,c_6992])).

cnf(c_8654,plain,
    ( k1_relat_1(sK8(sK10,sK9,sK11)) = sK9 ),
    inference(superposition,[status(thm)],[c_6985,c_8244])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK8(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_6991,plain,
    ( sK8(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8161,plain,
    ( sK8(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6987,c_6991])).

cnf(c_8339,plain,
    ( sK8(sK10,sK9,sK11) = sK11 ),
    inference(superposition,[status(thm)],[c_6985,c_8161])).

cnf(c_8656,plain,
    ( k1_relat_1(sK11) = sK9 ),
    inference(light_normalisation,[status(thm)],[c_8654,c_8339])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_7004,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7015,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10300,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7004,c_7015])).

cnf(c_19763,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8656,c_10300])).

cnf(c_41,plain,
    ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_140,plain,
    ( r1_tarski(sK11,sK11) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_144,plain,
    ( ~ r1_tarski(sK11,sK11)
    | sK11 = sK11 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_32,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK8(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_7344,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_funct_1(sK8(X0,X1,sK11)) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_7437,plain,
    ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_funct_1(sK8(sK10,sK9,sK11)) ),
    inference(instantiation,[status(thm)],[c_7344])).

cnf(c_7439,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
    | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
    | v1_funct_1(sK8(sK10,sK9,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7437])).

cnf(c_7438,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_7441,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7438])).

cnf(c_6153,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_7595,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK8(sK10,sK9,sK11))
    | X0 != sK8(sK10,sK9,sK11) ),
    inference(instantiation,[status(thm)],[c_6153])).

cnf(c_7596,plain,
    ( X0 != sK8(sK10,sK9,sK11)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK8(sK10,sK9,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7595])).

cnf(c_7598,plain,
    ( sK11 != sK8(sK10,sK9,sK11)
    | v1_funct_1(sK8(sK10,sK9,sK11)) != iProver_top
    | v1_funct_1(sK11) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7596])).

cnf(c_33,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK8(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7349,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_relat_1(sK8(X0,X1,sK11)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_7660,plain,
    ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | v1_relat_1(sK8(sK10,sK9,sK11)) ),
    inference(instantiation,[status(thm)],[c_7349])).

cnf(c_7662,plain,
    ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
    | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
    | v1_relat_1(sK8(sK10,sK9,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7660])).

cnf(c_7385,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | sK8(X0,X1,sK11) = sK11 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_7659,plain,
    ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
    | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
    | sK8(sK10,sK9,sK11) = sK11 ),
    inference(instantiation,[status(thm)],[c_7385])).

cnf(c_6142,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7838,plain,
    ( X0 != X1
    | X0 = sK8(sK10,sK9,sK11)
    | sK8(sK10,sK9,sK11) != X1 ),
    inference(instantiation,[status(thm)],[c_6142])).

cnf(c_7839,plain,
    ( sK8(sK10,sK9,sK11) != sK11
    | sK11 = sK8(sK10,sK9,sK11)
    | sK11 != sK11 ),
    inference(instantiation,[status(thm)],[c_7838])).

cnf(c_6151,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_8118,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK8(sK10,sK9,sK11))
    | X0 != sK8(sK10,sK9,sK11) ),
    inference(instantiation,[status(thm)],[c_6151])).

cnf(c_8127,plain,
    ( X0 != sK8(sK10,sK9,sK11)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK8(sK10,sK9,sK11)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8118])).

cnf(c_8129,plain,
    ( sK11 != sK8(sK10,sK9,sK11)
    | v1_relat_1(sK8(sK10,sK9,sK11)) != iProver_top
    | v1_relat_1(sK11) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8127])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_571,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_37])).

cnf(c_572,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_36,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_576,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_36])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,negated_conjecture,
    ( ~ v1_funct_2(sK11,sK9,sK10)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_595,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK11)
    | sK10 != X2
    | sK9 != X1
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_39])).

cnf(c_596,plain,
    ( ~ v1_partfun1(sK11,sK9)
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(sK11) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_660,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK11)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK9
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_576,c_596])).

cnf(c_661,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(sK11)
    | ~ v1_relat_1(sK11)
    | v1_xboole_0(k2_relat_1(sK11))
    | k1_relat_1(sK11) != sK9 ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_6981,plain,
    ( k1_relat_1(sK11) != sK9
    | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_9038,plain,
    ( sK9 != sK9
    | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8656,c_6981])).

cnf(c_9049,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9038])).

cnf(c_662,plain,
    ( k1_relat_1(sK11) != sK9
    | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_9414,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9049,c_40,c_41,c_140,c_144,c_662,c_7439,c_7438,c_7441,c_7598,c_7662,c_7659,c_7839,c_8129,c_8656])).

cnf(c_10886,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | r1_tarski(k1_relat_1(sK11),sK9) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7001,c_9414])).

cnf(c_10904,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | r1_tarski(sK9,sK9) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10886,c_8656])).

cnf(c_11307,plain,
    ( r1_tarski(sK9,sK9) != iProver_top
    | r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10904,c_40,c_41,c_140,c_144,c_7438,c_7441,c_7662,c_7659,c_7839,c_8129])).

cnf(c_11308,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | r1_tarski(sK9,sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11307])).

cnf(c_7013,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11314,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11308,c_7013])).

cnf(c_29,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_6993,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8669,plain,
    ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6987,c_6993])).

cnf(c_12715,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) = iProver_top
    | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8339,c_8669])).

cnf(c_20065,plain,
    ( r2_hidden(X0,sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19763,c_40,c_41,c_140,c_144,c_7439,c_7438,c_7441,c_7598,c_7662,c_7659,c_7839,c_8129,c_11314,c_12715])).

cnf(c_20080,plain,
    ( v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_8078,c_20065])).

cnf(c_19,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_642,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(sK11)
    | ~ v1_xboole_0(X1)
    | sK9 != X1
    | sK11 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_596])).

cnf(c_643,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,X0)))
    | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(sK11)
    | ~ v1_xboole_0(sK9) ),
    inference(unflattening,[status(thm)],[c_642])).

cnf(c_6139,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ v1_funct_1(sK11)
    | ~ v1_xboole_0(sK9)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_643])).

cnf(c_6982,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_xboole_0(sK9) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6139])).

cnf(c_6138,plain,
    ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_643])).

cnf(c_6983,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6138])).

cnf(c_7123,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6982,c_6983])).

cnf(c_10887,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | r1_tarski(k1_relat_1(sK11),sK9) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_7001,c_7123])).

cnf(c_10894,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | r1_tarski(sK9,sK9) != iProver_top
    | v1_funct_1(sK11) != iProver_top
    | v1_relat_1(sK11) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10887,c_8656])).

cnf(c_11317,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | r1_tarski(sK9,sK9) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10894,c_40,c_41,c_140,c_144,c_7439,c_7438,c_7441,c_7598,c_7662,c_7659,c_7839,c_8129])).

cnf(c_11324,plain,
    ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11317,c_7013])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20080,c_12715,c_11324,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:08:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 6.93/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/1.49  
% 6.93/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.93/1.49  
% 6.93/1.49  ------  iProver source info
% 6.93/1.49  
% 6.93/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.93/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.93/1.49  git: non_committed_changes: false
% 6.93/1.49  git: last_make_outside_of_git: false
% 6.93/1.49  
% 6.93/1.49  ------ 
% 6.93/1.49  
% 6.93/1.49  ------ Input Options
% 6.93/1.49  
% 6.93/1.49  --out_options                           all
% 6.93/1.49  --tptp_safe_out                         true
% 6.93/1.49  --problem_path                          ""
% 6.93/1.49  --include_path                          ""
% 6.93/1.49  --clausifier                            res/vclausify_rel
% 6.93/1.49  --clausifier_options                    --mode clausify
% 6.93/1.49  --stdin                                 false
% 6.93/1.49  --stats_out                             all
% 6.93/1.49  
% 6.93/1.49  ------ General Options
% 6.93/1.49  
% 6.93/1.49  --fof                                   false
% 6.93/1.49  --time_out_real                         305.
% 6.93/1.49  --time_out_virtual                      -1.
% 6.93/1.49  --symbol_type_check                     false
% 6.93/1.49  --clausify_out                          false
% 6.93/1.49  --sig_cnt_out                           false
% 6.93/1.49  --trig_cnt_out                          false
% 6.93/1.49  --trig_cnt_out_tolerance                1.
% 6.93/1.49  --trig_cnt_out_sk_spl                   false
% 6.93/1.49  --abstr_cl_out                          false
% 6.93/1.49  
% 6.93/1.49  ------ Global Options
% 6.93/1.49  
% 6.93/1.49  --schedule                              default
% 6.93/1.49  --add_important_lit                     false
% 6.93/1.49  --prop_solver_per_cl                    1000
% 6.93/1.49  --min_unsat_core                        false
% 6.93/1.49  --soft_assumptions                      false
% 6.93/1.49  --soft_lemma_size                       3
% 6.93/1.49  --prop_impl_unit_size                   0
% 6.93/1.49  --prop_impl_unit                        []
% 6.93/1.49  --share_sel_clauses                     true
% 6.93/1.49  --reset_solvers                         false
% 6.93/1.49  --bc_imp_inh                            [conj_cone]
% 6.93/1.49  --conj_cone_tolerance                   3.
% 6.93/1.49  --extra_neg_conj                        none
% 6.93/1.49  --large_theory_mode                     true
% 6.93/1.49  --prolific_symb_bound                   200
% 6.93/1.49  --lt_threshold                          2000
% 6.93/1.49  --clause_weak_htbl                      true
% 6.93/1.49  --gc_record_bc_elim                     false
% 6.93/1.49  
% 6.93/1.49  ------ Preprocessing Options
% 6.93/1.49  
% 6.93/1.49  --preprocessing_flag                    true
% 6.93/1.49  --time_out_prep_mult                    0.1
% 6.93/1.49  --splitting_mode                        input
% 6.93/1.49  --splitting_grd                         true
% 6.93/1.49  --splitting_cvd                         false
% 6.93/1.49  --splitting_cvd_svl                     false
% 6.93/1.49  --splitting_nvd                         32
% 6.93/1.49  --sub_typing                            true
% 6.93/1.49  --prep_gs_sim                           true
% 6.93/1.49  --prep_unflatten                        true
% 6.93/1.49  --prep_res_sim                          true
% 6.93/1.49  --prep_upred                            true
% 6.93/1.49  --prep_sem_filter                       exhaustive
% 6.93/1.49  --prep_sem_filter_out                   false
% 6.93/1.49  --pred_elim                             true
% 6.93/1.49  --res_sim_input                         true
% 6.93/1.49  --eq_ax_congr_red                       true
% 6.93/1.49  --pure_diseq_elim                       true
% 6.93/1.49  --brand_transform                       false
% 6.93/1.49  --non_eq_to_eq                          false
% 6.93/1.49  --prep_def_merge                        true
% 6.93/1.49  --prep_def_merge_prop_impl              false
% 6.93/1.49  --prep_def_merge_mbd                    true
% 6.93/1.49  --prep_def_merge_tr_red                 false
% 6.93/1.49  --prep_def_merge_tr_cl                  false
% 6.93/1.49  --smt_preprocessing                     true
% 6.93/1.49  --smt_ac_axioms                         fast
% 6.93/1.49  --preprocessed_out                      false
% 6.93/1.49  --preprocessed_stats                    false
% 6.93/1.49  
% 6.93/1.49  ------ Abstraction refinement Options
% 6.93/1.49  
% 6.93/1.49  --abstr_ref                             []
% 6.93/1.49  --abstr_ref_prep                        false
% 6.93/1.49  --abstr_ref_until_sat                   false
% 6.93/1.49  --abstr_ref_sig_restrict                funpre
% 6.93/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.93/1.49  --abstr_ref_under                       []
% 6.93/1.49  
% 6.93/1.49  ------ SAT Options
% 6.93/1.49  
% 6.93/1.49  --sat_mode                              false
% 6.93/1.49  --sat_fm_restart_options                ""
% 6.93/1.49  --sat_gr_def                            false
% 6.93/1.49  --sat_epr_types                         true
% 6.93/1.49  --sat_non_cyclic_types                  false
% 6.93/1.49  --sat_finite_models                     false
% 6.93/1.49  --sat_fm_lemmas                         false
% 6.93/1.49  --sat_fm_prep                           false
% 6.93/1.49  --sat_fm_uc_incr                        true
% 6.93/1.49  --sat_out_model                         small
% 6.93/1.49  --sat_out_clauses                       false
% 6.93/1.49  
% 6.93/1.49  ------ QBF Options
% 6.93/1.49  
% 6.93/1.49  --qbf_mode                              false
% 6.93/1.49  --qbf_elim_univ                         false
% 6.93/1.49  --qbf_dom_inst                          none
% 6.93/1.49  --qbf_dom_pre_inst                      false
% 6.93/1.49  --qbf_sk_in                             false
% 6.93/1.49  --qbf_pred_elim                         true
% 6.93/1.49  --qbf_split                             512
% 6.93/1.49  
% 6.93/1.49  ------ BMC1 Options
% 6.93/1.49  
% 6.93/1.49  --bmc1_incremental                      false
% 6.93/1.49  --bmc1_axioms                           reachable_all
% 6.93/1.49  --bmc1_min_bound                        0
% 6.93/1.49  --bmc1_max_bound                        -1
% 6.93/1.49  --bmc1_max_bound_default                -1
% 6.93/1.49  --bmc1_symbol_reachability              true
% 6.93/1.49  --bmc1_property_lemmas                  false
% 6.93/1.49  --bmc1_k_induction                      false
% 6.93/1.49  --bmc1_non_equiv_states                 false
% 6.93/1.49  --bmc1_deadlock                         false
% 6.93/1.49  --bmc1_ucm                              false
% 6.93/1.49  --bmc1_add_unsat_core                   none
% 6.93/1.49  --bmc1_unsat_core_children              false
% 6.93/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.93/1.49  --bmc1_out_stat                         full
% 6.93/1.49  --bmc1_ground_init                      false
% 6.93/1.49  --bmc1_pre_inst_next_state              false
% 6.93/1.49  --bmc1_pre_inst_state                   false
% 6.93/1.49  --bmc1_pre_inst_reach_state             false
% 6.93/1.49  --bmc1_out_unsat_core                   false
% 6.93/1.49  --bmc1_aig_witness_out                  false
% 6.93/1.49  --bmc1_verbose                          false
% 6.93/1.49  --bmc1_dump_clauses_tptp                false
% 6.93/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.93/1.49  --bmc1_dump_file                        -
% 6.93/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.93/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.93/1.49  --bmc1_ucm_extend_mode                  1
% 6.93/1.49  --bmc1_ucm_init_mode                    2
% 6.93/1.49  --bmc1_ucm_cone_mode                    none
% 6.93/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.93/1.49  --bmc1_ucm_relax_model                  4
% 6.93/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.93/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.93/1.49  --bmc1_ucm_layered_model                none
% 6.93/1.49  --bmc1_ucm_max_lemma_size               10
% 6.93/1.49  
% 6.93/1.49  ------ AIG Options
% 6.93/1.49  
% 6.93/1.49  --aig_mode                              false
% 6.93/1.49  
% 6.93/1.49  ------ Instantiation Options
% 6.93/1.49  
% 6.93/1.49  --instantiation_flag                    true
% 6.93/1.49  --inst_sos_flag                         false
% 6.93/1.49  --inst_sos_phase                        true
% 6.93/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.93/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.93/1.49  --inst_lit_sel_side                     num_symb
% 6.93/1.49  --inst_solver_per_active                1400
% 6.93/1.49  --inst_solver_calls_frac                1.
% 6.93/1.49  --inst_passive_queue_type               priority_queues
% 6.93/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.93/1.49  --inst_passive_queues_freq              [25;2]
% 6.93/1.49  --inst_dismatching                      true
% 6.93/1.49  --inst_eager_unprocessed_to_passive     true
% 6.93/1.49  --inst_prop_sim_given                   true
% 6.93/1.49  --inst_prop_sim_new                     false
% 6.93/1.49  --inst_subs_new                         false
% 6.93/1.49  --inst_eq_res_simp                      false
% 6.93/1.49  --inst_subs_given                       false
% 6.93/1.49  --inst_orphan_elimination               true
% 6.93/1.49  --inst_learning_loop_flag               true
% 6.93/1.49  --inst_learning_start                   3000
% 6.93/1.49  --inst_learning_factor                  2
% 6.93/1.49  --inst_start_prop_sim_after_learn       3
% 6.93/1.49  --inst_sel_renew                        solver
% 6.93/1.49  --inst_lit_activity_flag                true
% 6.93/1.49  --inst_restr_to_given                   false
% 6.93/1.49  --inst_activity_threshold               500
% 6.93/1.49  --inst_out_proof                        true
% 6.93/1.49  
% 6.93/1.49  ------ Resolution Options
% 6.93/1.49  
% 6.93/1.49  --resolution_flag                       true
% 6.93/1.49  --res_lit_sel                           adaptive
% 6.93/1.49  --res_lit_sel_side                      none
% 6.93/1.49  --res_ordering                          kbo
% 6.93/1.49  --res_to_prop_solver                    active
% 6.93/1.49  --res_prop_simpl_new                    false
% 6.93/1.49  --res_prop_simpl_given                  true
% 6.93/1.49  --res_passive_queue_type                priority_queues
% 6.93/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.93/1.49  --res_passive_queues_freq               [15;5]
% 6.93/1.49  --res_forward_subs                      full
% 6.93/1.49  --res_backward_subs                     full
% 6.93/1.49  --res_forward_subs_resolution           true
% 6.93/1.49  --res_backward_subs_resolution          true
% 6.93/1.49  --res_orphan_elimination                true
% 6.93/1.49  --res_time_limit                        2.
% 6.93/1.49  --res_out_proof                         true
% 6.93/1.49  
% 6.93/1.49  ------ Superposition Options
% 6.93/1.49  
% 6.93/1.49  --superposition_flag                    true
% 6.93/1.49  --sup_passive_queue_type                priority_queues
% 6.93/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.93/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.93/1.49  --demod_completeness_check              fast
% 6.93/1.49  --demod_use_ground                      true
% 6.93/1.49  --sup_to_prop_solver                    passive
% 6.93/1.49  --sup_prop_simpl_new                    true
% 6.93/1.49  --sup_prop_simpl_given                  true
% 6.93/1.49  --sup_fun_splitting                     false
% 6.93/1.49  --sup_smt_interval                      50000
% 6.93/1.49  
% 6.93/1.49  ------ Superposition Simplification Setup
% 6.93/1.49  
% 6.93/1.49  --sup_indices_passive                   []
% 6.93/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.93/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.93/1.49  --sup_full_bw                           [BwDemod]
% 6.93/1.49  --sup_immed_triv                        [TrivRules]
% 6.93/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.93/1.49  --sup_immed_bw_main                     []
% 6.93/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.93/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.93/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.93/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.93/1.49  
% 6.93/1.49  ------ Combination Options
% 6.93/1.49  
% 6.93/1.49  --comb_res_mult                         3
% 6.93/1.49  --comb_sup_mult                         2
% 6.93/1.49  --comb_inst_mult                        10
% 6.93/1.49  
% 6.93/1.49  ------ Debug Options
% 6.93/1.49  
% 6.93/1.49  --dbg_backtrace                         false
% 6.93/1.49  --dbg_dump_prop_clauses                 false
% 6.93/1.49  --dbg_dump_prop_clauses_file            -
% 6.93/1.49  --dbg_out_stat                          false
% 6.93/1.49  ------ Parsing...
% 6.93/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.93/1.49  
% 6.93/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.93/1.49  
% 6.93/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.93/1.49  
% 6.93/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.93/1.49  ------ Proving...
% 6.93/1.49  ------ Problem Properties 
% 6.93/1.49  
% 6.93/1.49  
% 6.93/1.49  clauses                                 36
% 6.93/1.49  conjectures                             1
% 6.93/1.49  EPR                                     4
% 6.93/1.49  Horn                                    27
% 6.93/1.49  unary                                   4
% 6.93/1.49  binary                                  7
% 6.93/1.49  lits                                    114
% 6.93/1.49  lits eq                                 16
% 6.93/1.49  fd_pure                                 0
% 6.93/1.49  fd_pseudo                               0
% 6.93/1.49  fd_cond                                 0
% 6.93/1.49  fd_pseudo_cond                          5
% 6.93/1.49  AC symbols                              0
% 6.93/1.49  
% 6.93/1.49  ------ Schedule dynamic 5 is on 
% 6.93/1.49  
% 6.93/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.93/1.49  
% 6.93/1.49  
% 6.93/1.49  ------ 
% 6.93/1.49  Current options:
% 6.93/1.49  ------ 
% 6.93/1.49  
% 6.93/1.49  ------ Input Options
% 6.93/1.49  
% 6.93/1.49  --out_options                           all
% 6.93/1.49  --tptp_safe_out                         true
% 6.93/1.49  --problem_path                          ""
% 6.93/1.49  --include_path                          ""
% 6.93/1.49  --clausifier                            res/vclausify_rel
% 6.93/1.49  --clausifier_options                    --mode clausify
% 6.93/1.49  --stdin                                 false
% 6.93/1.49  --stats_out                             all
% 6.93/1.49  
% 6.93/1.49  ------ General Options
% 6.93/1.49  
% 6.93/1.49  --fof                                   false
% 6.93/1.49  --time_out_real                         305.
% 6.93/1.49  --time_out_virtual                      -1.
% 6.93/1.49  --symbol_type_check                     false
% 6.93/1.49  --clausify_out                          false
% 6.93/1.49  --sig_cnt_out                           false
% 6.93/1.49  --trig_cnt_out                          false
% 6.93/1.49  --trig_cnt_out_tolerance                1.
% 6.93/1.49  --trig_cnt_out_sk_spl                   false
% 6.93/1.49  --abstr_cl_out                          false
% 6.93/1.49  
% 6.93/1.49  ------ Global Options
% 6.93/1.49  
% 6.93/1.49  --schedule                              default
% 6.93/1.49  --add_important_lit                     false
% 6.93/1.49  --prop_solver_per_cl                    1000
% 6.93/1.49  --min_unsat_core                        false
% 6.93/1.49  --soft_assumptions                      false
% 6.93/1.49  --soft_lemma_size                       3
% 6.93/1.49  --prop_impl_unit_size                   0
% 6.93/1.49  --prop_impl_unit                        []
% 6.93/1.49  --share_sel_clauses                     true
% 6.93/1.49  --reset_solvers                         false
% 6.93/1.49  --bc_imp_inh                            [conj_cone]
% 6.93/1.49  --conj_cone_tolerance                   3.
% 6.93/1.49  --extra_neg_conj                        none
% 6.93/1.49  --large_theory_mode                     true
% 6.93/1.49  --prolific_symb_bound                   200
% 6.93/1.49  --lt_threshold                          2000
% 6.93/1.49  --clause_weak_htbl                      true
% 6.93/1.49  --gc_record_bc_elim                     false
% 6.93/1.49  
% 6.93/1.49  ------ Preprocessing Options
% 6.93/1.49  
% 6.93/1.49  --preprocessing_flag                    true
% 6.93/1.49  --time_out_prep_mult                    0.1
% 6.93/1.49  --splitting_mode                        input
% 6.93/1.49  --splitting_grd                         true
% 6.93/1.49  --splitting_cvd                         false
% 6.93/1.49  --splitting_cvd_svl                     false
% 6.93/1.49  --splitting_nvd                         32
% 6.93/1.49  --sub_typing                            true
% 6.93/1.49  --prep_gs_sim                           true
% 6.93/1.49  --prep_unflatten                        true
% 6.93/1.49  --prep_res_sim                          true
% 6.93/1.49  --prep_upred                            true
% 6.93/1.49  --prep_sem_filter                       exhaustive
% 6.93/1.49  --prep_sem_filter_out                   false
% 6.93/1.49  --pred_elim                             true
% 6.93/1.49  --res_sim_input                         true
% 6.93/1.49  --eq_ax_congr_red                       true
% 6.93/1.49  --pure_diseq_elim                       true
% 6.93/1.49  --brand_transform                       false
% 6.93/1.49  --non_eq_to_eq                          false
% 6.93/1.49  --prep_def_merge                        true
% 6.93/1.49  --prep_def_merge_prop_impl              false
% 6.93/1.49  --prep_def_merge_mbd                    true
% 6.93/1.49  --prep_def_merge_tr_red                 false
% 6.93/1.49  --prep_def_merge_tr_cl                  false
% 6.93/1.49  --smt_preprocessing                     true
% 6.93/1.49  --smt_ac_axioms                         fast
% 6.93/1.49  --preprocessed_out                      false
% 6.93/1.49  --preprocessed_stats                    false
% 6.93/1.49  
% 6.93/1.49  ------ Abstraction refinement Options
% 6.93/1.49  
% 6.93/1.49  --abstr_ref                             []
% 6.93/1.49  --abstr_ref_prep                        false
% 6.93/1.49  --abstr_ref_until_sat                   false
% 6.93/1.49  --abstr_ref_sig_restrict                funpre
% 6.93/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.93/1.49  --abstr_ref_under                       []
% 6.93/1.49  
% 6.93/1.49  ------ SAT Options
% 6.93/1.49  
% 6.93/1.49  --sat_mode                              false
% 6.93/1.49  --sat_fm_restart_options                ""
% 6.93/1.49  --sat_gr_def                            false
% 6.93/1.49  --sat_epr_types                         true
% 6.93/1.49  --sat_non_cyclic_types                  false
% 6.93/1.49  --sat_finite_models                     false
% 6.93/1.49  --sat_fm_lemmas                         false
% 6.93/1.49  --sat_fm_prep                           false
% 6.93/1.49  --sat_fm_uc_incr                        true
% 6.93/1.49  --sat_out_model                         small
% 6.93/1.49  --sat_out_clauses                       false
% 6.93/1.49  
% 6.93/1.49  ------ QBF Options
% 6.93/1.49  
% 6.93/1.49  --qbf_mode                              false
% 6.93/1.49  --qbf_elim_univ                         false
% 6.93/1.49  --qbf_dom_inst                          none
% 6.93/1.49  --qbf_dom_pre_inst                      false
% 6.93/1.49  --qbf_sk_in                             false
% 6.93/1.49  --qbf_pred_elim                         true
% 6.93/1.49  --qbf_split                             512
% 6.93/1.49  
% 6.93/1.49  ------ BMC1 Options
% 6.93/1.49  
% 6.93/1.49  --bmc1_incremental                      false
% 6.93/1.49  --bmc1_axioms                           reachable_all
% 6.93/1.49  --bmc1_min_bound                        0
% 6.93/1.49  --bmc1_max_bound                        -1
% 6.93/1.49  --bmc1_max_bound_default                -1
% 6.93/1.49  --bmc1_symbol_reachability              true
% 6.93/1.49  --bmc1_property_lemmas                  false
% 6.93/1.49  --bmc1_k_induction                      false
% 6.93/1.49  --bmc1_non_equiv_states                 false
% 6.93/1.49  --bmc1_deadlock                         false
% 6.93/1.49  --bmc1_ucm                              false
% 6.93/1.49  --bmc1_add_unsat_core                   none
% 6.93/1.49  --bmc1_unsat_core_children              false
% 6.93/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.93/1.49  --bmc1_out_stat                         full
% 6.93/1.49  --bmc1_ground_init                      false
% 6.93/1.49  --bmc1_pre_inst_next_state              false
% 6.93/1.49  --bmc1_pre_inst_state                   false
% 6.93/1.49  --bmc1_pre_inst_reach_state             false
% 6.93/1.49  --bmc1_out_unsat_core                   false
% 6.93/1.49  --bmc1_aig_witness_out                  false
% 6.93/1.49  --bmc1_verbose                          false
% 6.93/1.49  --bmc1_dump_clauses_tptp                false
% 6.93/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.93/1.49  --bmc1_dump_file                        -
% 6.93/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.93/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.93/1.49  --bmc1_ucm_extend_mode                  1
% 6.93/1.49  --bmc1_ucm_init_mode                    2
% 6.93/1.49  --bmc1_ucm_cone_mode                    none
% 6.93/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.93/1.49  --bmc1_ucm_relax_model                  4
% 6.93/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.93/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.93/1.49  --bmc1_ucm_layered_model                none
% 6.93/1.49  --bmc1_ucm_max_lemma_size               10
% 6.93/1.49  
% 6.93/1.49  ------ AIG Options
% 6.93/1.49  
% 6.93/1.49  --aig_mode                              false
% 6.93/1.49  
% 6.93/1.49  ------ Instantiation Options
% 6.93/1.49  
% 6.93/1.49  --instantiation_flag                    true
% 6.93/1.49  --inst_sos_flag                         false
% 6.93/1.49  --inst_sos_phase                        true
% 6.93/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.93/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.93/1.49  --inst_lit_sel_side                     none
% 6.93/1.49  --inst_solver_per_active                1400
% 6.93/1.49  --inst_solver_calls_frac                1.
% 6.93/1.49  --inst_passive_queue_type               priority_queues
% 6.93/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.93/1.49  --inst_passive_queues_freq              [25;2]
% 6.93/1.49  --inst_dismatching                      true
% 6.93/1.49  --inst_eager_unprocessed_to_passive     true
% 6.93/1.49  --inst_prop_sim_given                   true
% 6.93/1.49  --inst_prop_sim_new                     false
% 6.93/1.49  --inst_subs_new                         false
% 6.93/1.49  --inst_eq_res_simp                      false
% 6.93/1.49  --inst_subs_given                       false
% 6.93/1.49  --inst_orphan_elimination               true
% 6.93/1.49  --inst_learning_loop_flag               true
% 6.93/1.49  --inst_learning_start                   3000
% 6.93/1.49  --inst_learning_factor                  2
% 6.93/1.49  --inst_start_prop_sim_after_learn       3
% 6.93/1.49  --inst_sel_renew                        solver
% 6.93/1.49  --inst_lit_activity_flag                true
% 6.93/1.49  --inst_restr_to_given                   false
% 6.93/1.49  --inst_activity_threshold               500
% 6.93/1.49  --inst_out_proof                        true
% 6.93/1.49  
% 6.93/1.49  ------ Resolution Options
% 6.93/1.49  
% 6.93/1.49  --resolution_flag                       false
% 6.93/1.49  --res_lit_sel                           adaptive
% 6.93/1.49  --res_lit_sel_side                      none
% 6.93/1.49  --res_ordering                          kbo
% 6.93/1.49  --res_to_prop_solver                    active
% 6.93/1.49  --res_prop_simpl_new                    false
% 6.93/1.49  --res_prop_simpl_given                  true
% 6.93/1.49  --res_passive_queue_type                priority_queues
% 6.93/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.93/1.49  --res_passive_queues_freq               [15;5]
% 6.93/1.49  --res_forward_subs                      full
% 6.93/1.49  --res_backward_subs                     full
% 6.93/1.49  --res_forward_subs_resolution           true
% 6.93/1.49  --res_backward_subs_resolution          true
% 6.93/1.49  --res_orphan_elimination                true
% 6.93/1.49  --res_time_limit                        2.
% 6.93/1.49  --res_out_proof                         true
% 6.93/1.49  
% 6.93/1.49  ------ Superposition Options
% 6.93/1.49  
% 6.93/1.49  --superposition_flag                    true
% 6.93/1.49  --sup_passive_queue_type                priority_queues
% 6.93/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.93/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.93/1.49  --demod_completeness_check              fast
% 6.93/1.49  --demod_use_ground                      true
% 6.93/1.49  --sup_to_prop_solver                    passive
% 6.93/1.49  --sup_prop_simpl_new                    true
% 6.93/1.49  --sup_prop_simpl_given                  true
% 6.93/1.49  --sup_fun_splitting                     false
% 6.93/1.49  --sup_smt_interval                      50000
% 6.93/1.49  
% 6.93/1.49  ------ Superposition Simplification Setup
% 6.93/1.49  
% 6.93/1.49  --sup_indices_passive                   []
% 6.93/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.93/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.93/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.93/1.49  --sup_full_bw                           [BwDemod]
% 6.93/1.49  --sup_immed_triv                        [TrivRules]
% 6.93/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.93/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.93/1.49  --sup_immed_bw_main                     []
% 6.93/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.93/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.93/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.93/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.93/1.49  
% 6.93/1.49  ------ Combination Options
% 6.93/1.49  
% 6.93/1.49  --comb_res_mult                         3
% 6.93/1.49  --comb_sup_mult                         2
% 6.93/1.49  --comb_inst_mult                        10
% 6.93/1.49  
% 6.93/1.49  ------ Debug Options
% 6.93/1.49  
% 6.93/1.49  --dbg_backtrace                         false
% 6.93/1.49  --dbg_dump_prop_clauses                 false
% 6.93/1.49  --dbg_dump_prop_clauses_file            -
% 6.93/1.49  --dbg_out_stat                          false
% 6.93/1.49  
% 6.93/1.49  
% 6.93/1.49  
% 6.93/1.49  
% 6.93/1.49  ------ Proving...
% 6.93/1.49  
% 6.93/1.49  
% 6.93/1.49  % SZS status Theorem for theBenchmark.p
% 6.93/1.49  
% 6.93/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.93/1.49  
% 6.93/1.49  fof(f3,axiom,(
% 6.93/1.49    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f39,plain,(
% 6.93/1.49    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f40,plain,(
% 6.93/1.49    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 6.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3,f39])).
% 6.93/1.49  
% 6.93/1.49  fof(f62,plain,(
% 6.93/1.49    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f40])).
% 6.93/1.49  
% 6.93/1.49  fof(f4,axiom,(
% 6.93/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f16,plain,(
% 6.93/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 6.93/1.49    inference(ennf_transformation,[],[f4])).
% 6.93/1.49  
% 6.93/1.49  fof(f17,plain,(
% 6.93/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 6.93/1.49    inference(flattening,[],[f16])).
% 6.93/1.49  
% 6.93/1.49  fof(f63,plain,(
% 6.93/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f17])).
% 6.93/1.49  
% 6.93/1.49  fof(f14,conjecture,(
% 6.93/1.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f15,negated_conjecture,(
% 6.93/1.49    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 6.93/1.49    inference(negated_conjecture,[],[f14])).
% 6.93/1.49  
% 6.93/1.49  fof(f30,plain,(
% 6.93/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 6.93/1.49    inference(ennf_transformation,[],[f15])).
% 6.93/1.49  
% 6.93/1.49  fof(f55,plain,(
% 6.93/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~v1_funct_2(sK11,sK9,sK10) | ~v1_funct_1(sK11)) & r2_hidden(sK11,k1_funct_2(sK9,sK10)))),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f56,plain,(
% 6.93/1.49    (~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~v1_funct_2(sK11,sK9,sK10) | ~v1_funct_1(sK11)) & r2_hidden(sK11,k1_funct_2(sK9,sK10))),
% 6.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f30,f55])).
% 6.93/1.49  
% 6.93/1.49  fof(f96,plain,(
% 6.93/1.49    r2_hidden(sK11,k1_funct_2(sK9,sK10))),
% 6.93/1.49    inference(cnf_transformation,[],[f56])).
% 6.93/1.49  
% 6.93/1.49  fof(f12,axiom,(
% 6.93/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f31,plain,(
% 6.93/1.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 6.93/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.93/1.49  
% 6.93/1.49  fof(f32,plain,(
% 6.93/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 6.93/1.49    inference(definition_folding,[],[f12,f31])).
% 6.93/1.49  
% 6.93/1.49  fof(f54,plain,(
% 6.93/1.49    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 6.93/1.49    inference(nnf_transformation,[],[f32])).
% 6.93/1.49  
% 6.93/1.49  fof(f91,plain,(
% 6.93/1.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 6.93/1.49    inference(cnf_transformation,[],[f54])).
% 6.93/1.49  
% 6.93/1.49  fof(f107,plain,(
% 6.93/1.49    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 6.93/1.49    inference(equality_resolution,[],[f91])).
% 6.93/1.49  
% 6.93/1.49  fof(f48,plain,(
% 6.93/1.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 6.93/1.49    inference(nnf_transformation,[],[f31])).
% 6.93/1.49  
% 6.93/1.49  fof(f49,plain,(
% 6.93/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 6.93/1.49    inference(rectify,[],[f48])).
% 6.93/1.49  
% 6.93/1.49  fof(f52,plain,(
% 6.93/1.49    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) & k1_relat_1(sK8(X0,X1,X6)) = X1 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))))),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f51,plain,(
% 6.93/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK7(X0,X1,X2) = X3 & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))) )),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f50,plain,(
% 6.93/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f53,plain,(
% 6.93/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) & k1_relat_1(sK8(X0,X1,X6)) = X1 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 6.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f49,f52,f51,f50])).
% 6.93/1.49  
% 6.93/1.49  fof(f82,plain,(
% 6.93/1.49    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK8(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f53])).
% 6.93/1.49  
% 6.93/1.49  fof(f81,plain,(
% 6.93/1.49    ( ! [X6,X2,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f53])).
% 6.93/1.49  
% 6.93/1.49  fof(f7,axiom,(
% 6.93/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f19,plain,(
% 6.93/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.93/1.49    inference(ennf_transformation,[],[f7])).
% 6.93/1.49  
% 6.93/1.49  fof(f20,plain,(
% 6.93/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.93/1.49    inference(flattening,[],[f19])).
% 6.93/1.49  
% 6.93/1.49  fof(f42,plain,(
% 6.93/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.93/1.49    inference(nnf_transformation,[],[f20])).
% 6.93/1.49  
% 6.93/1.49  fof(f43,plain,(
% 6.93/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.93/1.49    inference(rectify,[],[f42])).
% 6.93/1.49  
% 6.93/1.49  fof(f46,plain,(
% 6.93/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f45,plain,(
% 6.93/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f44,plain,(
% 6.93/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f47,plain,(
% 6.93/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f46,f45,f44])).
% 6.93/1.49  
% 6.93/1.49  fof(f69,plain,(
% 6.93/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f47])).
% 6.93/1.49  
% 6.93/1.49  fof(f100,plain,(
% 6.93/1.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.93/1.49    inference(equality_resolution,[],[f69])).
% 6.93/1.49  
% 6.93/1.49  fof(f101,plain,(
% 6.93/1.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.93/1.49    inference(equality_resolution,[],[f100])).
% 6.93/1.49  
% 6.93/1.49  fof(f1,axiom,(
% 6.93/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f33,plain,(
% 6.93/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 6.93/1.49    inference(nnf_transformation,[],[f1])).
% 6.93/1.49  
% 6.93/1.49  fof(f34,plain,(
% 6.93/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.93/1.49    inference(rectify,[],[f33])).
% 6.93/1.49  
% 6.93/1.49  fof(f35,plain,(
% 6.93/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 6.93/1.49    introduced(choice_axiom,[])).
% 6.93/1.49  
% 6.93/1.49  fof(f36,plain,(
% 6.93/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 6.93/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 6.93/1.49  
% 6.93/1.49  fof(f57,plain,(
% 6.93/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f36])).
% 6.93/1.49  
% 6.93/1.49  fof(f2,axiom,(
% 6.93/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f37,plain,(
% 6.93/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.93/1.49    inference(nnf_transformation,[],[f2])).
% 6.93/1.49  
% 6.93/1.49  fof(f38,plain,(
% 6.93/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.93/1.49    inference(flattening,[],[f37])).
% 6.93/1.49  
% 6.93/1.49  fof(f59,plain,(
% 6.93/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.93/1.49    inference(cnf_transformation,[],[f38])).
% 6.93/1.49  
% 6.93/1.49  fof(f99,plain,(
% 6.93/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.93/1.49    inference(equality_resolution,[],[f59])).
% 6.93/1.49  
% 6.93/1.49  fof(f61,plain,(
% 6.93/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f38])).
% 6.93/1.49  
% 6.93/1.49  fof(f80,plain,(
% 6.93/1.49    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f53])).
% 6.93/1.49  
% 6.93/1.49  fof(f79,plain,(
% 6.93/1.49    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f53])).
% 6.93/1.49  
% 6.93/1.49  fof(f8,axiom,(
% 6.93/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f21,plain,(
% 6.93/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 6.93/1.49    inference(ennf_transformation,[],[f8])).
% 6.93/1.49  
% 6.93/1.49  fof(f22,plain,(
% 6.93/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 6.93/1.49    inference(flattening,[],[f21])).
% 6.93/1.49  
% 6.93/1.49  fof(f73,plain,(
% 6.93/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f22])).
% 6.93/1.49  
% 6.93/1.49  fof(f11,axiom,(
% 6.93/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f26,plain,(
% 6.93/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 6.93/1.49    inference(ennf_transformation,[],[f11])).
% 6.93/1.49  
% 6.93/1.49  fof(f27,plain,(
% 6.93/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 6.93/1.49    inference(flattening,[],[f26])).
% 6.93/1.49  
% 6.93/1.49  fof(f78,plain,(
% 6.93/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f27])).
% 6.93/1.49  
% 6.93/1.49  fof(f13,axiom,(
% 6.93/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f28,plain,(
% 6.93/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.93/1.49    inference(ennf_transformation,[],[f13])).
% 6.93/1.49  
% 6.93/1.49  fof(f29,plain,(
% 6.93/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.93/1.49    inference(flattening,[],[f28])).
% 6.93/1.49  
% 6.93/1.49  fof(f94,plain,(
% 6.93/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f29])).
% 6.93/1.49  
% 6.93/1.49  fof(f95,plain,(
% 6.93/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f29])).
% 6.93/1.49  
% 6.93/1.49  fof(f9,axiom,(
% 6.93/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f23,plain,(
% 6.93/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.93/1.49    inference(ennf_transformation,[],[f9])).
% 6.93/1.49  
% 6.93/1.49  fof(f24,plain,(
% 6.93/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.93/1.49    inference(flattening,[],[f23])).
% 6.93/1.49  
% 6.93/1.49  fof(f75,plain,(
% 6.93/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.93/1.49    inference(cnf_transformation,[],[f24])).
% 6.93/1.49  
% 6.93/1.49  fof(f97,plain,(
% 6.93/1.49    ~m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~v1_funct_2(sK11,sK9,sK10) | ~v1_funct_1(sK11)),
% 6.93/1.49    inference(cnf_transformation,[],[f56])).
% 6.93/1.49  
% 6.93/1.49  fof(f83,plain,(
% 6.93/1.49    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f53])).
% 6.93/1.49  
% 6.93/1.49  fof(f10,axiom,(
% 6.93/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 6.93/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.93/1.49  
% 6.93/1.49  fof(f25,plain,(
% 6.93/1.49    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 6.93/1.49    inference(ennf_transformation,[],[f10])).
% 6.93/1.49  
% 6.93/1.49  fof(f76,plain,(
% 6.93/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 6.93/1.49    inference(cnf_transformation,[],[f25])).
% 6.93/1.49  
% 6.93/1.49  cnf(c_5,plain,
% 6.93/1.49      ( m1_subset_1(sK2(X0),X0) ),
% 6.93/1.49      inference(cnf_transformation,[],[f62]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7012,plain,
% 6.93/1.49      ( m1_subset_1(sK2(X0),X0) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6,plain,
% 6.93/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.93/1.49      inference(cnf_transformation,[],[f63]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7011,plain,
% 6.93/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 6.93/1.49      | r2_hidden(X0,X1) = iProver_top
% 6.93/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8078,plain,
% 6.93/1.49      ( r2_hidden(sK2(X0),X0) = iProver_top
% 6.93/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_7012,c_7011]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_40,negated_conjecture,
% 6.93/1.49      ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) ),
% 6.93/1.49      inference(cnf_transformation,[],[f96]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6985,plain,
% 6.93/1.49      ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_35,plain,
% 6.93/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 6.93/1.49      inference(cnf_transformation,[],[f107]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6987,plain,
% 6.93/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_30,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,X2)
% 6.93/1.49      | ~ r2_hidden(X3,X2)
% 6.93/1.49      | k1_relat_1(sK8(X0,X1,X3)) = X1 ),
% 6.93/1.49      inference(cnf_transformation,[],[f82]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6992,plain,
% 6.93/1.49      ( k1_relat_1(sK8(X0,X1,X2)) = X1
% 6.93/1.49      | sP0(X0,X1,X3) != iProver_top
% 6.93/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8244,plain,
% 6.93/1.49      ( k1_relat_1(sK8(X0,X1,X2)) = X1
% 6.93/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_6987,c_6992]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8654,plain,
% 6.93/1.49      ( k1_relat_1(sK8(sK10,sK9,sK11)) = sK9 ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_6985,c_8244]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_31,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK8(X0,X1,X3) = X3 ),
% 6.93/1.49      inference(cnf_transformation,[],[f81]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6991,plain,
% 6.93/1.49      ( sK8(X0,X1,X2) = X2
% 6.93/1.49      | sP0(X0,X1,X3) != iProver_top
% 6.93/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8161,plain,
% 6.93/1.49      ( sK8(X0,X1,X2) = X2
% 6.93/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_6987,c_6991]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8339,plain,
% 6.93/1.49      ( sK8(sK10,sK9,sK11) = sK11 ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_6985,c_8161]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8656,plain,
% 6.93/1.49      ( k1_relat_1(sK11) = sK9 ),
% 6.93/1.49      inference(light_normalisation,[status(thm)],[c_8654,c_8339]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_13,plain,
% 6.93/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 6.93/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 6.93/1.49      | ~ v1_funct_1(X1)
% 6.93/1.49      | ~ v1_relat_1(X1) ),
% 6.93/1.49      inference(cnf_transformation,[],[f101]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7004,plain,
% 6.93/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 6.93/1.49      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 6.93/1.49      | v1_funct_1(X1) != iProver_top
% 6.93/1.49      | v1_relat_1(X1) != iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_1,plain,
% 6.93/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.93/1.49      inference(cnf_transformation,[],[f57]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7015,plain,
% 6.93/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.93/1.49      | v1_xboole_0(X1) != iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_10300,plain,
% 6.93/1.49      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 6.93/1.49      | v1_funct_1(X1) != iProver_top
% 6.93/1.49      | v1_relat_1(X1) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(X1)) != iProver_top ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_7004,c_7015]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_19763,plain,
% 6.93/1.49      ( r2_hidden(X0,sK9) != iProver_top
% 6.93/1.49      | v1_funct_1(sK11) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) != iProver_top ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_8656,c_10300]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_41,plain,
% 6.93/1.49      ( r2_hidden(sK11,k1_funct_2(sK9,sK10)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_4,plain,
% 6.93/1.49      ( r1_tarski(X0,X0) ),
% 6.93/1.49      inference(cnf_transformation,[],[f99]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_140,plain,
% 6.93/1.49      ( r1_tarski(sK11,sK11) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_2,plain,
% 6.93/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 6.93/1.49      inference(cnf_transformation,[],[f61]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_144,plain,
% 6.93/1.49      ( ~ r1_tarski(sK11,sK11) | sK11 = sK11 ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_32,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,X2)
% 6.93/1.49      | ~ r2_hidden(X3,X2)
% 6.93/1.49      | v1_funct_1(sK8(X0,X1,X3)) ),
% 6.93/1.49      inference(cnf_transformation,[],[f80]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7344,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
% 6.93/1.49      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 6.93/1.49      | v1_funct_1(sK8(X0,X1,sK11)) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7437,plain,
% 6.93/1.49      ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
% 6.93/1.49      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 6.93/1.49      | v1_funct_1(sK8(sK10,sK9,sK11)) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_7344]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7439,plain,
% 6.93/1.49      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
% 6.93/1.49      | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
% 6.93/1.49      | v1_funct_1(sK8(sK10,sK9,sK11)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_7437]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7438,plain,
% 6.93/1.49      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_35]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7441,plain,
% 6.93/1.49      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_7438]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6153,plain,
% 6.93/1.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 6.93/1.49      theory(equality) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7595,plain,
% 6.93/1.49      ( v1_funct_1(X0)
% 6.93/1.49      | ~ v1_funct_1(sK8(sK10,sK9,sK11))
% 6.93/1.49      | X0 != sK8(sK10,sK9,sK11) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_6153]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7596,plain,
% 6.93/1.49      ( X0 != sK8(sK10,sK9,sK11)
% 6.93/1.49      | v1_funct_1(X0) = iProver_top
% 6.93/1.49      | v1_funct_1(sK8(sK10,sK9,sK11)) != iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_7595]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7598,plain,
% 6.93/1.49      ( sK11 != sK8(sK10,sK9,sK11)
% 6.93/1.49      | v1_funct_1(sK8(sK10,sK9,sK11)) != iProver_top
% 6.93/1.49      | v1_funct_1(sK11) = iProver_top ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_7596]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_33,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,X2)
% 6.93/1.49      | ~ r2_hidden(X3,X2)
% 6.93/1.49      | v1_relat_1(sK8(X0,X1,X3)) ),
% 6.93/1.49      inference(cnf_transformation,[],[f79]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7349,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
% 6.93/1.49      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 6.93/1.49      | v1_relat_1(sK8(X0,X1,sK11)) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_33]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7660,plain,
% 6.93/1.49      ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
% 6.93/1.49      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 6.93/1.49      | v1_relat_1(sK8(sK10,sK9,sK11)) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_7349]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7662,plain,
% 6.93/1.49      ( sP0(sK10,sK9,k1_funct_2(sK9,sK10)) != iProver_top
% 6.93/1.49      | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top
% 6.93/1.49      | v1_relat_1(sK8(sK10,sK9,sK11)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_7660]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7385,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,k1_funct_2(sK9,sK10))
% 6.93/1.49      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 6.93/1.49      | sK8(X0,X1,sK11) = sK11 ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_31]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7659,plain,
% 6.93/1.49      ( ~ sP0(sK10,sK9,k1_funct_2(sK9,sK10))
% 6.93/1.49      | ~ r2_hidden(sK11,k1_funct_2(sK9,sK10))
% 6.93/1.49      | sK8(sK10,sK9,sK11) = sK11 ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_7385]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6142,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7838,plain,
% 6.93/1.49      ( X0 != X1 | X0 = sK8(sK10,sK9,sK11) | sK8(sK10,sK9,sK11) != X1 ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_6142]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7839,plain,
% 6.93/1.49      ( sK8(sK10,sK9,sK11) != sK11
% 6.93/1.49      | sK11 = sK8(sK10,sK9,sK11)
% 6.93/1.49      | sK11 != sK11 ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_7838]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6151,plain,
% 6.93/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 6.93/1.49      theory(equality) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8118,plain,
% 6.93/1.49      ( v1_relat_1(X0)
% 6.93/1.49      | ~ v1_relat_1(sK8(sK10,sK9,sK11))
% 6.93/1.49      | X0 != sK8(sK10,sK9,sK11) ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_6151]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8127,plain,
% 6.93/1.49      ( X0 != sK8(sK10,sK9,sK11)
% 6.93/1.49      | v1_relat_1(X0) = iProver_top
% 6.93/1.49      | v1_relat_1(sK8(sK10,sK9,sK11)) != iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_8118]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_8129,plain,
% 6.93/1.49      ( sK11 != sK8(sK10,sK9,sK11)
% 6.93/1.49      | v1_relat_1(sK8(sK10,sK9,sK11)) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) = iProver_top ),
% 6.93/1.49      inference(instantiation,[status(thm)],[c_8127]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_16,plain,
% 6.93/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.93/1.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 6.93/1.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 6.93/1.49      | ~ v1_relat_1(X0) ),
% 6.93/1.49      inference(cnf_transformation,[],[f73]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7001,plain,
% 6.93/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 6.93/1.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 6.93/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 6.93/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_20,plain,
% 6.93/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.93/1.49      | v1_partfun1(X0,X1)
% 6.93/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | v1_xboole_0(X2) ),
% 6.93/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_37,plain,
% 6.93/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | ~ v1_relat_1(X0) ),
% 6.93/1.49      inference(cnf_transformation,[],[f94]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_571,plain,
% 6.93/1.49      ( v1_partfun1(X0,X1)
% 6.93/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | ~ v1_funct_1(X3)
% 6.93/1.49      | ~ v1_relat_1(X3)
% 6.93/1.49      | v1_xboole_0(X2)
% 6.93/1.49      | X3 != X0
% 6.93/1.49      | k2_relat_1(X3) != X2
% 6.93/1.49      | k1_relat_1(X3) != X1 ),
% 6.93/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_37]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_572,plain,
% 6.93/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 6.93/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | ~ v1_relat_1(X0)
% 6.93/1.49      | v1_xboole_0(k2_relat_1(X0)) ),
% 6.93/1.49      inference(unflattening,[status(thm)],[c_571]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_36,plain,
% 6.93/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | ~ v1_relat_1(X0) ),
% 6.93/1.49      inference(cnf_transformation,[],[f95]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_576,plain,
% 6.93/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | ~ v1_relat_1(X0)
% 6.93/1.49      | v1_xboole_0(k2_relat_1(X0)) ),
% 6.93/1.49      inference(global_propositional_subsumption,
% 6.93/1.49                [status(thm)],
% 6.93/1.49                [c_572,c_36]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_17,plain,
% 6.93/1.49      ( v1_funct_2(X0,X1,X2)
% 6.93/1.49      | ~ v1_partfun1(X0,X1)
% 6.93/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.93/1.49      | ~ v1_funct_1(X0) ),
% 6.93/1.49      inference(cnf_transformation,[],[f75]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_39,negated_conjecture,
% 6.93/1.49      ( ~ v1_funct_2(sK11,sK9,sK10)
% 6.93/1.49      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.49      | ~ v1_funct_1(sK11) ),
% 6.93/1.49      inference(cnf_transformation,[],[f97]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_595,plain,
% 6.93/1.49      ( ~ v1_partfun1(X0,X1)
% 6.93/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.93/1.49      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | ~ v1_funct_1(sK11)
% 6.93/1.49      | sK10 != X2
% 6.93/1.49      | sK9 != X1
% 6.93/1.49      | sK11 != X0 ),
% 6.93/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_39]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_596,plain,
% 6.93/1.49      ( ~ v1_partfun1(sK11,sK9)
% 6.93/1.49      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.49      | ~ v1_funct_1(sK11) ),
% 6.93/1.49      inference(unflattening,[status(thm)],[c_595]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_660,plain,
% 6.93/1.49      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.49      | ~ v1_funct_1(X0)
% 6.93/1.49      | ~ v1_funct_1(sK11)
% 6.93/1.49      | ~ v1_relat_1(X0)
% 6.93/1.49      | v1_xboole_0(k2_relat_1(X0))
% 6.93/1.49      | k1_relat_1(X0) != sK9
% 6.93/1.49      | sK11 != X0 ),
% 6.93/1.49      inference(resolution_lifted,[status(thm)],[c_576,c_596]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_661,plain,
% 6.93/1.49      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.49      | ~ v1_funct_1(sK11)
% 6.93/1.49      | ~ v1_relat_1(sK11)
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11))
% 6.93/1.49      | k1_relat_1(sK11) != sK9 ),
% 6.93/1.49      inference(unflattening,[status(thm)],[c_660]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_6981,plain,
% 6.93/1.49      ( k1_relat_1(sK11) != sK9
% 6.93/1.49      | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 6.93/1.49      | v1_funct_1(sK11) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_9038,plain,
% 6.93/1.49      ( sK9 != sK9
% 6.93/1.49      | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 6.93/1.49      | v1_funct_1(sK11) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(demodulation,[status(thm)],[c_8656,c_6981]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_9049,plain,
% 6.93/1.49      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 6.93/1.49      | v1_funct_1(sK11) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(equality_resolution_simp,[status(thm)],[c_9038]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_662,plain,
% 6.93/1.49      ( k1_relat_1(sK11) != sK9
% 6.93/1.49      | m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 6.93/1.49      | v1_funct_1(sK11) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_9414,plain,
% 6.93/1.49      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(global_propositional_subsumption,
% 6.93/1.49                [status(thm)],
% 6.93/1.49                [c_9049,c_40,c_41,c_140,c_144,c_662,c_7439,c_7438,c_7441,
% 6.93/1.49                 c_7598,c_7662,c_7659,c_7839,c_8129,c_8656]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_10886,plain,
% 6.93/1.49      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.49      | r1_tarski(k1_relat_1(sK11),sK9) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(superposition,[status(thm)],[c_7001,c_9414]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_10904,plain,
% 6.93/1.49      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.49      | r1_tarski(sK9,sK9) != iProver_top
% 6.93/1.49      | v1_relat_1(sK11) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(light_normalisation,[status(thm)],[c_10886,c_8656]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_11307,plain,
% 6.93/1.49      ( r1_tarski(sK9,sK9) != iProver_top
% 6.93/1.49      | r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(global_propositional_subsumption,
% 6.93/1.49                [status(thm)],
% 6.93/1.49                [c_10904,c_40,c_41,c_140,c_144,c_7438,c_7441,c_7662,
% 6.93/1.49                 c_7659,c_7839,c_8129]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_11308,plain,
% 6.93/1.49      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.49      | r1_tarski(sK9,sK9) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(renaming,[status(thm)],[c_11307]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_7013,plain,
% 6.93/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 6.93/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_11314,plain,
% 6.93/1.49      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.49      | v1_xboole_0(k2_relat_1(sK11)) = iProver_top ),
% 6.93/1.49      inference(forward_subsumption_resolution,
% 6.93/1.49                [status(thm)],
% 6.93/1.49                [c_11308,c_7013]) ).
% 6.93/1.49  
% 6.93/1.49  cnf(c_29,plain,
% 6.93/1.49      ( ~ sP0(X0,X1,X2)
% 6.93/1.49      | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0)
% 6.93/1.50      | ~ r2_hidden(X3,X2) ),
% 6.93/1.50      inference(cnf_transformation,[],[f83]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_6993,plain,
% 6.93/1.50      ( sP0(X0,X1,X2) != iProver_top
% 6.93/1.50      | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) = iProver_top
% 6.93/1.50      | r2_hidden(X3,X2) != iProver_top ),
% 6.93/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_8669,plain,
% 6.93/1.50      ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0) = iProver_top
% 6.93/1.50      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 6.93/1.50      inference(superposition,[status(thm)],[c_6987,c_6993]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_12715,plain,
% 6.93/1.50      ( r1_tarski(k2_relat_1(sK11),sK10) = iProver_top
% 6.93/1.50      | r2_hidden(sK11,k1_funct_2(sK9,sK10)) != iProver_top ),
% 6.93/1.50      inference(superposition,[status(thm)],[c_8339,c_8669]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_20065,plain,
% 6.93/1.50      ( r2_hidden(X0,sK9) != iProver_top ),
% 6.93/1.50      inference(global_propositional_subsumption,
% 6.93/1.50                [status(thm)],
% 6.93/1.50                [c_19763,c_40,c_41,c_140,c_144,c_7439,c_7438,c_7441,
% 6.93/1.50                 c_7598,c_7662,c_7659,c_7839,c_8129,c_11314,c_12715]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_20080,plain,
% 6.93/1.50      ( v1_xboole_0(sK9) = iProver_top ),
% 6.93/1.50      inference(superposition,[status(thm)],[c_8078,c_20065]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_19,plain,
% 6.93/1.50      ( v1_partfun1(X0,X1)
% 6.93/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.93/1.50      | ~ v1_xboole_0(X1) ),
% 6.93/1.50      inference(cnf_transformation,[],[f76]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_642,plain,
% 6.93/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.93/1.50      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.50      | ~ v1_funct_1(sK11)
% 6.93/1.50      | ~ v1_xboole_0(X1)
% 6.93/1.50      | sK9 != X1
% 6.93/1.50      | sK11 != X0 ),
% 6.93/1.50      inference(resolution_lifted,[status(thm)],[c_19,c_596]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_643,plain,
% 6.93/1.50      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,X0)))
% 6.93/1.50      | ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.50      | ~ v1_funct_1(sK11)
% 6.93/1.50      | ~ v1_xboole_0(sK9) ),
% 6.93/1.50      inference(unflattening,[status(thm)],[c_642]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_6139,plain,
% 6.93/1.50      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
% 6.93/1.50      | ~ v1_funct_1(sK11)
% 6.93/1.50      | ~ v1_xboole_0(sK9)
% 6.93/1.50      | sP0_iProver_split ),
% 6.93/1.50      inference(splitting,
% 6.93/1.50                [splitting(split),new_symbols(definition,[])],
% 6.93/1.50                [c_643]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_6982,plain,
% 6.93/1.50      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 6.93/1.50      | v1_funct_1(sK11) != iProver_top
% 6.93/1.50      | v1_xboole_0(sK9) != iProver_top
% 6.93/1.50      | sP0_iProver_split = iProver_top ),
% 6.93/1.50      inference(predicate_to_equality,[status(thm)],[c_6139]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_6138,plain,
% 6.93/1.50      ( ~ m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,X0)))
% 6.93/1.50      | ~ sP0_iProver_split ),
% 6.93/1.50      inference(splitting,
% 6.93/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 6.93/1.50                [c_643]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_6983,plain,
% 6.93/1.50      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,X0))) != iProver_top
% 6.93/1.50      | sP0_iProver_split != iProver_top ),
% 6.93/1.50      inference(predicate_to_equality,[status(thm)],[c_6138]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_7123,plain,
% 6.93/1.50      ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) != iProver_top
% 6.93/1.50      | v1_funct_1(sK11) != iProver_top
% 6.93/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 6.93/1.50      inference(forward_subsumption_resolution,
% 6.93/1.50                [status(thm)],
% 6.93/1.50                [c_6982,c_6983]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_10887,plain,
% 6.93/1.50      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.50      | r1_tarski(k1_relat_1(sK11),sK9) != iProver_top
% 6.93/1.50      | v1_funct_1(sK11) != iProver_top
% 6.93/1.50      | v1_relat_1(sK11) != iProver_top
% 6.93/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 6.93/1.50      inference(superposition,[status(thm)],[c_7001,c_7123]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_10894,plain,
% 6.93/1.50      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.50      | r1_tarski(sK9,sK9) != iProver_top
% 6.93/1.50      | v1_funct_1(sK11) != iProver_top
% 6.93/1.50      | v1_relat_1(sK11) != iProver_top
% 6.93/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 6.93/1.50      inference(light_normalisation,[status(thm)],[c_10887,c_8656]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_11317,plain,
% 6.93/1.50      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.50      | r1_tarski(sK9,sK9) != iProver_top
% 6.93/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 6.93/1.50      inference(global_propositional_subsumption,
% 6.93/1.50                [status(thm)],
% 6.93/1.50                [c_10894,c_40,c_41,c_140,c_144,c_7439,c_7438,c_7441,
% 6.93/1.50                 c_7598,c_7662,c_7659,c_7839,c_8129]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(c_11324,plain,
% 6.93/1.50      ( r1_tarski(k2_relat_1(sK11),sK10) != iProver_top
% 6.93/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 6.93/1.50      inference(forward_subsumption_resolution,
% 6.93/1.50                [status(thm)],
% 6.93/1.50                [c_11317,c_7013]) ).
% 6.93/1.50  
% 6.93/1.50  cnf(contradiction,plain,
% 6.93/1.50      ( $false ),
% 6.93/1.50      inference(minisat,[status(thm)],[c_20080,c_12715,c_11324,c_41]) ).
% 6.93/1.50  
% 6.93/1.50  
% 6.93/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.93/1.50  
% 6.93/1.50  ------                               Statistics
% 6.93/1.50  
% 6.93/1.50  ------ General
% 6.93/1.50  
% 6.93/1.50  abstr_ref_over_cycles:                  0
% 6.93/1.50  abstr_ref_under_cycles:                 0
% 6.93/1.50  gc_basic_clause_elim:                   0
% 6.93/1.50  forced_gc_time:                         0
% 6.93/1.50  parsing_time:                           0.013
% 6.93/1.50  unif_index_cands_time:                  0.
% 6.93/1.50  unif_index_add_time:                    0.
% 6.93/1.50  orderings_time:                         0.
% 6.93/1.50  out_proof_time:                         0.012
% 6.93/1.50  total_time:                             0.656
% 6.93/1.50  num_of_symbols:                         58
% 6.93/1.50  num_of_terms:                           14722
% 6.93/1.50  
% 6.93/1.50  ------ Preprocessing
% 6.93/1.50  
% 6.93/1.50  num_of_splits:                          1
% 6.93/1.50  num_of_split_atoms:                     1
% 6.93/1.50  num_of_reused_defs:                     0
% 6.93/1.50  num_eq_ax_congr_red:                    57
% 6.93/1.50  num_of_sem_filtered_clauses:            1
% 6.93/1.50  num_of_subtypes:                        0
% 6.93/1.50  monotx_restored_types:                  0
% 6.93/1.50  sat_num_of_epr_types:                   0
% 6.93/1.50  sat_num_of_non_cyclic_types:            0
% 6.93/1.50  sat_guarded_non_collapsed_types:        0
% 6.93/1.50  num_pure_diseq_elim:                    0
% 6.93/1.50  simp_replaced_by:                       0
% 6.93/1.50  res_preprocessed:                       177
% 6.93/1.50  prep_upred:                             0
% 6.93/1.50  prep_unflattend:                        206
% 6.93/1.50  smt_new_axioms:                         0
% 6.93/1.50  pred_elim_cands:                        7
% 6.93/1.50  pred_elim:                              2
% 6.93/1.50  pred_elim_cl:                           2
% 6.93/1.50  pred_elim_cycles:                       11
% 6.93/1.50  merged_defs:                            8
% 6.93/1.50  merged_defs_ncl:                        0
% 6.93/1.50  bin_hyper_res:                          8
% 6.93/1.50  prep_cycles:                            4
% 6.93/1.50  pred_elim_time:                         0.111
% 6.93/1.50  splitting_time:                         0.
% 6.93/1.50  sem_filter_time:                        0.
% 6.93/1.50  monotx_time:                            0.001
% 6.93/1.50  subtype_inf_time:                       0.
% 6.93/1.50  
% 6.93/1.50  ------ Problem properties
% 6.93/1.50  
% 6.93/1.50  clauses:                                36
% 6.93/1.50  conjectures:                            1
% 6.93/1.50  epr:                                    4
% 6.93/1.50  horn:                                   27
% 6.93/1.50  ground:                                 4
% 6.93/1.50  unary:                                  4
% 6.93/1.50  binary:                                 7
% 6.93/1.50  lits:                                   114
% 6.93/1.50  lits_eq:                                16
% 6.93/1.50  fd_pure:                                0
% 6.93/1.50  fd_pseudo:                              0
% 6.93/1.50  fd_cond:                                0
% 6.93/1.50  fd_pseudo_cond:                         5
% 6.93/1.50  ac_symbols:                             0
% 6.93/1.50  
% 6.93/1.50  ------ Propositional Solver
% 6.93/1.50  
% 6.93/1.50  prop_solver_calls:                      29
% 6.93/1.50  prop_fast_solver_calls:                 3038
% 6.93/1.50  smt_solver_calls:                       0
% 6.93/1.50  smt_fast_solver_calls:                  0
% 6.93/1.50  prop_num_of_clauses:                    6012
% 6.93/1.50  prop_preprocess_simplified:             13577
% 6.93/1.50  prop_fo_subsumed:                       123
% 6.93/1.50  prop_solver_time:                       0.
% 6.93/1.50  smt_solver_time:                        0.
% 6.93/1.50  smt_fast_solver_time:                   0.
% 6.93/1.50  prop_fast_solver_time:                  0.
% 6.93/1.50  prop_unsat_core_time:                   0.
% 6.93/1.50  
% 6.93/1.50  ------ QBF
% 6.93/1.50  
% 6.93/1.50  qbf_q_res:                              0
% 6.93/1.50  qbf_num_tautologies:                    0
% 6.93/1.50  qbf_prep_cycles:                        0
% 6.93/1.50  
% 6.93/1.50  ------ BMC1
% 6.93/1.50  
% 6.93/1.50  bmc1_current_bound:                     -1
% 6.93/1.50  bmc1_last_solved_bound:                 -1
% 6.93/1.50  bmc1_unsat_core_size:                   -1
% 6.93/1.50  bmc1_unsat_core_parents_size:           -1
% 6.93/1.50  bmc1_merge_next_fun:                    0
% 6.93/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.93/1.50  
% 6.93/1.50  ------ Instantiation
% 6.93/1.50  
% 6.93/1.50  inst_num_of_clauses:                    1480
% 6.93/1.50  inst_num_in_passive:                    252
% 6.93/1.50  inst_num_in_active:                     643
% 6.93/1.50  inst_num_in_unprocessed:                585
% 6.93/1.50  inst_num_of_loops:                      800
% 6.93/1.50  inst_num_of_learning_restarts:          0
% 6.93/1.50  inst_num_moves_active_passive:          153
% 6.93/1.50  inst_lit_activity:                      0
% 6.93/1.50  inst_lit_activity_moves:                0
% 6.93/1.50  inst_num_tautologies:                   0
% 6.93/1.50  inst_num_prop_implied:                  0
% 6.93/1.50  inst_num_existing_simplified:           0
% 6.93/1.50  inst_num_eq_res_simplified:             0
% 6.93/1.50  inst_num_child_elim:                    0
% 6.93/1.50  inst_num_of_dismatching_blockings:      851
% 6.93/1.50  inst_num_of_non_proper_insts:           1624
% 6.93/1.50  inst_num_of_duplicates:                 0
% 6.93/1.50  inst_inst_num_from_inst_to_res:         0
% 6.93/1.50  inst_dismatching_checking_time:         0.
% 6.93/1.50  
% 6.93/1.50  ------ Resolution
% 6.93/1.50  
% 6.93/1.50  res_num_of_clauses:                     0
% 6.93/1.50  res_num_in_passive:                     0
% 6.93/1.50  res_num_in_active:                      0
% 6.93/1.50  res_num_of_loops:                       181
% 6.93/1.50  res_forward_subset_subsumed:            82
% 6.93/1.50  res_backward_subset_subsumed:           0
% 6.93/1.50  res_forward_subsumed:                   0
% 6.93/1.50  res_backward_subsumed:                  0
% 6.93/1.50  res_forward_subsumption_resolution:     2
% 6.93/1.50  res_backward_subsumption_resolution:    0
% 6.93/1.50  res_clause_to_clause_subsumption:       971
% 6.93/1.50  res_orphan_elimination:                 0
% 6.93/1.50  res_tautology_del:                      79
% 6.93/1.50  res_num_eq_res_simplified:              0
% 6.93/1.50  res_num_sel_changes:                    0
% 6.93/1.50  res_moves_from_active_to_pass:          0
% 6.93/1.50  
% 6.93/1.50  ------ Superposition
% 6.93/1.50  
% 6.93/1.50  sup_time_total:                         0.
% 6.93/1.50  sup_time_generating:                    0.
% 6.93/1.50  sup_time_sim_full:                      0.
% 6.93/1.50  sup_time_sim_immed:                     0.
% 6.93/1.50  
% 6.93/1.50  sup_num_of_clauses:                     306
% 6.93/1.50  sup_num_in_active:                      152
% 6.93/1.50  sup_num_in_passive:                     154
% 6.93/1.50  sup_num_of_loops:                       159
% 6.93/1.50  sup_fw_superposition:                   166
% 6.93/1.50  sup_bw_superposition:                   226
% 6.93/1.50  sup_immediate_simplified:               76
% 6.93/1.50  sup_given_eliminated:                   0
% 6.93/1.50  comparisons_done:                       0
% 6.93/1.50  comparisons_avoided:                    24
% 6.93/1.50  
% 6.93/1.50  ------ Simplifications
% 6.93/1.50  
% 6.93/1.50  
% 6.93/1.50  sim_fw_subset_subsumed:                 28
% 6.93/1.50  sim_bw_subset_subsumed:                 9
% 6.93/1.50  sim_fw_subsumed:                        26
% 6.93/1.50  sim_bw_subsumed:                        0
% 6.93/1.50  sim_fw_subsumption_res:                 7
% 6.93/1.50  sim_bw_subsumption_res:                 0
% 6.93/1.50  sim_tautology_del:                      7
% 6.93/1.50  sim_eq_tautology_del:                   6
% 6.93/1.50  sim_eq_res_simp:                        2
% 6.93/1.50  sim_fw_demodulated:                     4
% 6.93/1.50  sim_bw_demodulated:                     14
% 6.93/1.50  sim_light_normalised:                   38
% 6.93/1.50  sim_joinable_taut:                      0
% 6.93/1.50  sim_joinable_simp:                      0
% 6.93/1.50  sim_ac_normalised:                      0
% 6.93/1.50  sim_smt_subsumption:                    0
% 6.93/1.50  
%------------------------------------------------------------------------------
