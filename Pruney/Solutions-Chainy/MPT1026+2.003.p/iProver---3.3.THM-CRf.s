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
% DateTime   : Thu Dec  3 12:08:12 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  212 (1253 expanded)
%              Number of clauses        :  121 ( 452 expanded)
%              Number of leaves         :   29 ( 302 expanded)
%              Depth                    :   17
%              Number of atoms          :  761 (6865 expanded)
%              Number of equality atoms :  231 (1937 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,
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

fof(f69,plain,
    ( ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      | ~ v1_funct_2(sK9,sK7,sK8)
      | ~ v1_funct_1(sK9) )
    & r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f43,f68])).

fof(f118,plain,(
    r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f69])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f19,f44])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f125,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f113])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f65,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X0)
          & k1_relat_1(X8) = X1
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0)
        & k1_relat_1(sK6(X0,X1,X6)) = X1
        & sK6(X0,X1,X6) = X6
        & v1_funct_1(sK6(X0,X1,X6))
        & v1_relat_1(sK6(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X0)
          & k1_relat_1(X5) = X1
          & X3 = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0)
        & k1_relat_1(sK5(X0,X1,X2)) = X1
        & sK5(X0,X1,X2) = X3
        & v1_funct_1(sK5(X0,X1,X2))
        & v1_relat_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
              | sK4(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X0)
              & k1_relat_1(X5) = X1
              & sK4(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X0)
                | k1_relat_1(X4) != X1
                | sK4(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0)
              & k1_relat_1(sK5(X0,X1,X2)) = X1
              & sK4(X0,X1,X2) = sK5(X0,X1,X2)
              & v1_funct_1(sK5(X0,X1,X2))
              & v1_relat_1(sK5(X0,X1,X2)) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X0)
                  | k1_relat_1(X7) != X1
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0)
                & k1_relat_1(sK6(X0,X1,X6)) = X1
                & sK6(X0,X1,X6) = X6
                & v1_funct_1(sK6(X0,X1,X6))
                & v1_relat_1(sK6(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f62,f65,f64,f63])).

fof(f103,plain,(
    ! [X6,X2,X0,X1] :
      ( sK6(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f105,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f104,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK6(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f117,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f121,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f102,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f101,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK6(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f69])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f57])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_49,negated_conjecture,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_4861,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_44,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_4863,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_40,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK6(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_4867,plain,
    ( sK6(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_7647,plain,
    ( sK6(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4863,c_4867])).

cnf(c_15140,plain,
    ( sK6(sK8,sK7,sK9) = sK9 ),
    inference(superposition,[status(thm)],[c_4861,c_7647])).

cnf(c_38,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_4869,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9137,plain,
    ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4863,c_4869])).

cnf(c_31757,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15140,c_9137])).

cnf(c_39,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK6(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_4868,plain,
    ( k1_relat_1(sK6(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_8513,plain,
    ( k1_relat_1(sK6(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4863,c_4868])).

cnf(c_18621,plain,
    ( k1_relat_1(sK6(sK8,sK7,sK9)) = sK7 ),
    inference(superposition,[status(thm)],[c_4861,c_8513])).

cnf(c_18633,plain,
    ( k1_relat_1(sK9) = sK7 ),
    inference(light_normalisation,[status(thm)],[c_18621,c_15140])).

cnf(c_45,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4862,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_18889,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_18633,c_4862])).

cnf(c_50,plain,
    ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_158,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_162,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_41,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK6(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_5306,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_funct_1(sK6(X0,X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_5471,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_funct_1(sK6(sK8,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_5306])).

cnf(c_5473,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
    | v1_funct_1(sK6(sK8,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5471])).

cnf(c_5472,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_5475,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5472])).

cnf(c_3923,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5645,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK6(sK8,sK7,sK9))
    | X0 != sK6(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_3923])).

cnf(c_5646,plain,
    ( X0 != sK6(sK8,sK7,sK9)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK6(sK8,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5645])).

cnf(c_5648,plain,
    ( sK9 != sK6(sK8,sK7,sK9)
    | v1_funct_1(sK6(sK8,sK7,sK9)) != iProver_top
    | v1_funct_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5646])).

cnf(c_42,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK6(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_5318,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK6(X0,X1,sK9)) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_5655,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | v1_relat_1(sK6(sK8,sK7,sK9)) ),
    inference(instantiation,[status(thm)],[c_5318])).

cnf(c_5657,plain,
    ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
    | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
    | v1_relat_1(sK6(sK8,sK7,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5655])).

cnf(c_5343,plain,
    ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK6(X0,X1,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_5654,plain,
    ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
    | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
    | sK6(sK8,sK7,sK9) = sK9 ),
    inference(instantiation,[status(thm)],[c_5343])).

cnf(c_3920,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_6300,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(sK6(sK8,sK7,sK9))
    | X0 != sK6(sK8,sK7,sK9) ),
    inference(instantiation,[status(thm)],[c_3920])).

cnf(c_6301,plain,
    ( X0 != sK6(sK8,sK7,sK9)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(sK6(sK8,sK7,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6300])).

cnf(c_6303,plain,
    ( sK9 != sK6(sK8,sK7,sK9)
    | v1_relat_1(sK6(sK8,sK7,sK9)) != iProver_top
    | v1_relat_1(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6301])).

cnf(c_3913,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6525,plain,
    ( X0 != X1
    | X0 = sK6(sK8,sK7,sK9)
    | sK6(sK8,sK7,sK9) != X1 ),
    inference(instantiation,[status(thm)],[c_3913])).

cnf(c_6526,plain,
    ( sK6(sK8,sK7,sK9) != sK9
    | sK9 = sK6(sK8,sK7,sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_6525])).

cnf(c_19545,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18889,c_49,c_50,c_158,c_162,c_5473,c_5472,c_5475,c_5648,c_5657,c_5654,c_6303,c_6526])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4877,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19553,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK9),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_19545,c_4877])).

cnf(c_46,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_48,negated_conjecture,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_729,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK8
    | k1_relat_1(X0) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_48])).

cnf(c_730,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | k2_relat_1(sK9) != sK8
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_742,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | k2_relat_1(sK9) != sK8
    | k1_relat_1(sK9) != sK7 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_730,c_22])).

cnf(c_4857,plain,
    ( k2_relat_1(sK9) != sK8
    | k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_18865,plain,
    ( k2_relat_1(sK9) != sK8
    | sK7 != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18633,c_4857])).

cnf(c_18866,plain,
    ( k2_relat_1(sK9) != sK8
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18865])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_692,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_46])).

cnf(c_693,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_697,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_45])).

cnf(c_26,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_716,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | sK8 != X2
    | sK7 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_48])).

cnf(c_717,plain,
    ( ~ v1_partfun1(sK9,sK7)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9) ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_780,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK7
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_697,c_717])).

cnf(c_781,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | v1_xboole_0(k2_relat_1(sK9))
    | k1_relat_1(sK9) != sK7 ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_782,plain,
    ( k1_relat_1(sK9) != sK7
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_4878,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_19554,plain,
    ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_19545,c_4878])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4893,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4895,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6117,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4893,c_4895])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4883,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_19,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_618,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_19])).

cnf(c_622,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_22])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_622])).

cnf(c_4858,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_5869,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4883,c_4858])).

cnf(c_13422,plain,
    ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6117,c_5869])).

cnf(c_14462,plain,
    ( r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13422,c_5869])).

cnf(c_18885,plain,
    ( r1_tarski(k1_relat_1(sK7),X0) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_18633,c_14462])).

cnf(c_4890,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19370,plain,
    ( k1_relat_1(sK7) = X0
    | r1_tarski(X0,k1_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_18885,c_4890])).

cnf(c_28,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_762,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | ~ v1_xboole_0(X1)
    | sK7 != X1
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_717])).

cnf(c_763,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | ~ v1_xboole_0(sK7) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_3910,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_1(sK9)
    | ~ v1_xboole_0(sK7)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_763])).

cnf(c_4855,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(sK7) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3910])).

cnf(c_3909,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_763])).

cnf(c_4856,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3909])).

cnf(c_5055,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4855,c_4856])).

cnf(c_5870,plain,
    ( r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) != iProver_top
    | v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4883,c_5055])).

cnf(c_6372,plain,
    ( v1_funct_1(sK9) != iProver_top
    | v1_xboole_0(sK7) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6117,c_5870])).

cnf(c_14,plain,
    ( m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4884,plain,
    ( m1_subset_1(sK3(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4885,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6577,plain,
    ( r2_hidden(sK3(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4884,c_4885])).

cnf(c_18887,plain,
    ( r1_tarski(sK7,X0) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_18633,c_13422])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_386,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_387,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_462,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_17,c_387])).

cnf(c_4859,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_19316,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_18887,c_4859])).

cnf(c_24132,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6577,c_19316])).

cnf(c_24190,plain,
    ( v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24132])).

cnf(c_24211,plain,
    ( v1_xboole_0(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19370,c_49,c_50,c_158,c_162,c_5473,c_5472,c_5475,c_5648,c_5654,c_6372,c_6526,c_24190])).

cnf(c_26059,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18866,c_49,c_50,c_158,c_162,c_782,c_5473,c_5472,c_5475,c_5648,c_5657,c_5654,c_6303,c_6372,c_6526,c_18633,c_19554,c_24190])).

cnf(c_26066,plain,
    ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_19553,c_26059])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31757,c_26066,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:20:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.26/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/1.49  
% 7.26/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.49  
% 7.26/1.49  ------  iProver source info
% 7.26/1.49  
% 7.26/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.49  git: non_committed_changes: false
% 7.26/1.49  git: last_make_outside_of_git: false
% 7.26/1.49  
% 7.26/1.49  ------ 
% 7.26/1.49  
% 7.26/1.49  ------ Input Options
% 7.26/1.49  
% 7.26/1.49  --out_options                           all
% 7.26/1.49  --tptp_safe_out                         true
% 7.26/1.49  --problem_path                          ""
% 7.26/1.49  --include_path                          ""
% 7.26/1.49  --clausifier                            res/vclausify_rel
% 7.26/1.49  --clausifier_options                    --mode clausify
% 7.26/1.49  --stdin                                 false
% 7.26/1.49  --stats_out                             all
% 7.26/1.49  
% 7.26/1.49  ------ General Options
% 7.26/1.49  
% 7.26/1.49  --fof                                   false
% 7.26/1.49  --time_out_real                         305.
% 7.26/1.49  --time_out_virtual                      -1.
% 7.26/1.49  --symbol_type_check                     false
% 7.26/1.49  --clausify_out                          false
% 7.26/1.49  --sig_cnt_out                           false
% 7.26/1.49  --trig_cnt_out                          false
% 7.26/1.49  --trig_cnt_out_tolerance                1.
% 7.26/1.49  --trig_cnt_out_sk_spl                   false
% 7.26/1.49  --abstr_cl_out                          false
% 7.26/1.49  
% 7.26/1.49  ------ Global Options
% 7.26/1.49  
% 7.26/1.49  --schedule                              default
% 7.26/1.49  --add_important_lit                     false
% 7.26/1.49  --prop_solver_per_cl                    1000
% 7.26/1.49  --min_unsat_core                        false
% 7.26/1.49  --soft_assumptions                      false
% 7.26/1.49  --soft_lemma_size                       3
% 7.26/1.49  --prop_impl_unit_size                   0
% 7.26/1.49  --prop_impl_unit                        []
% 7.26/1.49  --share_sel_clauses                     true
% 7.26/1.49  --reset_solvers                         false
% 7.26/1.49  --bc_imp_inh                            [conj_cone]
% 7.26/1.49  --conj_cone_tolerance                   3.
% 7.26/1.49  --extra_neg_conj                        none
% 7.26/1.49  --large_theory_mode                     true
% 7.26/1.49  --prolific_symb_bound                   200
% 7.26/1.49  --lt_threshold                          2000
% 7.26/1.49  --clause_weak_htbl                      true
% 7.26/1.49  --gc_record_bc_elim                     false
% 7.26/1.49  
% 7.26/1.49  ------ Preprocessing Options
% 7.26/1.49  
% 7.26/1.49  --preprocessing_flag                    true
% 7.26/1.49  --time_out_prep_mult                    0.1
% 7.26/1.49  --splitting_mode                        input
% 7.26/1.49  --splitting_grd                         true
% 7.26/1.49  --splitting_cvd                         false
% 7.26/1.49  --splitting_cvd_svl                     false
% 7.26/1.49  --splitting_nvd                         32
% 7.26/1.49  --sub_typing                            true
% 7.26/1.49  --prep_gs_sim                           true
% 7.26/1.49  --prep_unflatten                        true
% 7.26/1.49  --prep_res_sim                          true
% 7.26/1.49  --prep_upred                            true
% 7.26/1.49  --prep_sem_filter                       exhaustive
% 7.26/1.49  --prep_sem_filter_out                   false
% 7.26/1.49  --pred_elim                             true
% 7.26/1.49  --res_sim_input                         true
% 7.26/1.49  --eq_ax_congr_red                       true
% 7.26/1.49  --pure_diseq_elim                       true
% 7.26/1.49  --brand_transform                       false
% 7.26/1.49  --non_eq_to_eq                          false
% 7.26/1.49  --prep_def_merge                        true
% 7.26/1.49  --prep_def_merge_prop_impl              false
% 7.26/1.49  --prep_def_merge_mbd                    true
% 7.26/1.49  --prep_def_merge_tr_red                 false
% 7.26/1.49  --prep_def_merge_tr_cl                  false
% 7.26/1.49  --smt_preprocessing                     true
% 7.26/1.49  --smt_ac_axioms                         fast
% 7.26/1.49  --preprocessed_out                      false
% 7.26/1.49  --preprocessed_stats                    false
% 7.26/1.49  
% 7.26/1.49  ------ Abstraction refinement Options
% 7.26/1.49  
% 7.26/1.49  --abstr_ref                             []
% 7.26/1.49  --abstr_ref_prep                        false
% 7.26/1.49  --abstr_ref_until_sat                   false
% 7.26/1.49  --abstr_ref_sig_restrict                funpre
% 7.26/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.49  --abstr_ref_under                       []
% 7.26/1.49  
% 7.26/1.49  ------ SAT Options
% 7.26/1.49  
% 7.26/1.49  --sat_mode                              false
% 7.26/1.49  --sat_fm_restart_options                ""
% 7.26/1.49  --sat_gr_def                            false
% 7.26/1.49  --sat_epr_types                         true
% 7.26/1.49  --sat_non_cyclic_types                  false
% 7.26/1.49  --sat_finite_models                     false
% 7.26/1.49  --sat_fm_lemmas                         false
% 7.26/1.49  --sat_fm_prep                           false
% 7.26/1.49  --sat_fm_uc_incr                        true
% 7.26/1.49  --sat_out_model                         small
% 7.26/1.49  --sat_out_clauses                       false
% 7.26/1.49  
% 7.26/1.49  ------ QBF Options
% 7.26/1.49  
% 7.26/1.49  --qbf_mode                              false
% 7.26/1.49  --qbf_elim_univ                         false
% 7.26/1.49  --qbf_dom_inst                          none
% 7.26/1.49  --qbf_dom_pre_inst                      false
% 7.26/1.49  --qbf_sk_in                             false
% 7.26/1.49  --qbf_pred_elim                         true
% 7.26/1.49  --qbf_split                             512
% 7.26/1.49  
% 7.26/1.49  ------ BMC1 Options
% 7.26/1.49  
% 7.26/1.49  --bmc1_incremental                      false
% 7.26/1.49  --bmc1_axioms                           reachable_all
% 7.26/1.49  --bmc1_min_bound                        0
% 7.26/1.49  --bmc1_max_bound                        -1
% 7.26/1.49  --bmc1_max_bound_default                -1
% 7.26/1.49  --bmc1_symbol_reachability              true
% 7.26/1.49  --bmc1_property_lemmas                  false
% 7.26/1.49  --bmc1_k_induction                      false
% 7.26/1.49  --bmc1_non_equiv_states                 false
% 7.26/1.49  --bmc1_deadlock                         false
% 7.26/1.49  --bmc1_ucm                              false
% 7.26/1.49  --bmc1_add_unsat_core                   none
% 7.26/1.49  --bmc1_unsat_core_children              false
% 7.26/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.49  --bmc1_out_stat                         full
% 7.26/1.49  --bmc1_ground_init                      false
% 7.26/1.49  --bmc1_pre_inst_next_state              false
% 7.26/1.49  --bmc1_pre_inst_state                   false
% 7.26/1.49  --bmc1_pre_inst_reach_state             false
% 7.26/1.49  --bmc1_out_unsat_core                   false
% 7.26/1.49  --bmc1_aig_witness_out                  false
% 7.26/1.49  --bmc1_verbose                          false
% 7.26/1.49  --bmc1_dump_clauses_tptp                false
% 7.26/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.49  --bmc1_dump_file                        -
% 7.26/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.49  --bmc1_ucm_extend_mode                  1
% 7.26/1.49  --bmc1_ucm_init_mode                    2
% 7.26/1.49  --bmc1_ucm_cone_mode                    none
% 7.26/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.49  --bmc1_ucm_relax_model                  4
% 7.26/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.49  --bmc1_ucm_layered_model                none
% 7.26/1.49  --bmc1_ucm_max_lemma_size               10
% 7.26/1.49  
% 7.26/1.49  ------ AIG Options
% 7.26/1.49  
% 7.26/1.49  --aig_mode                              false
% 7.26/1.49  
% 7.26/1.49  ------ Instantiation Options
% 7.26/1.49  
% 7.26/1.49  --instantiation_flag                    true
% 7.26/1.49  --inst_sos_flag                         false
% 7.26/1.49  --inst_sos_phase                        true
% 7.26/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.49  --inst_lit_sel_side                     num_symb
% 7.26/1.49  --inst_solver_per_active                1400
% 7.26/1.49  --inst_solver_calls_frac                1.
% 7.26/1.49  --inst_passive_queue_type               priority_queues
% 7.26/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.49  --inst_passive_queues_freq              [25;2]
% 7.26/1.49  --inst_dismatching                      true
% 7.26/1.49  --inst_eager_unprocessed_to_passive     true
% 7.26/1.49  --inst_prop_sim_given                   true
% 7.26/1.49  --inst_prop_sim_new                     false
% 7.26/1.49  --inst_subs_new                         false
% 7.26/1.49  --inst_eq_res_simp                      false
% 7.26/1.49  --inst_subs_given                       false
% 7.26/1.49  --inst_orphan_elimination               true
% 7.26/1.49  --inst_learning_loop_flag               true
% 7.26/1.49  --inst_learning_start                   3000
% 7.26/1.49  --inst_learning_factor                  2
% 7.26/1.49  --inst_start_prop_sim_after_learn       3
% 7.26/1.49  --inst_sel_renew                        solver
% 7.26/1.49  --inst_lit_activity_flag                true
% 7.26/1.49  --inst_restr_to_given                   false
% 7.26/1.49  --inst_activity_threshold               500
% 7.26/1.49  --inst_out_proof                        true
% 7.26/1.49  
% 7.26/1.49  ------ Resolution Options
% 7.26/1.49  
% 7.26/1.49  --resolution_flag                       true
% 7.26/1.49  --res_lit_sel                           adaptive
% 7.26/1.49  --res_lit_sel_side                      none
% 7.26/1.49  --res_ordering                          kbo
% 7.26/1.49  --res_to_prop_solver                    active
% 7.26/1.49  --res_prop_simpl_new                    false
% 7.26/1.49  --res_prop_simpl_given                  true
% 7.26/1.49  --res_passive_queue_type                priority_queues
% 7.26/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.49  --res_passive_queues_freq               [15;5]
% 7.26/1.49  --res_forward_subs                      full
% 7.26/1.49  --res_backward_subs                     full
% 7.26/1.49  --res_forward_subs_resolution           true
% 7.26/1.49  --res_backward_subs_resolution          true
% 7.26/1.49  --res_orphan_elimination                true
% 7.26/1.49  --res_time_limit                        2.
% 7.26/1.49  --res_out_proof                         true
% 7.26/1.49  
% 7.26/1.49  ------ Superposition Options
% 7.26/1.49  
% 7.26/1.49  --superposition_flag                    true
% 7.26/1.49  --sup_passive_queue_type                priority_queues
% 7.26/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.49  --demod_completeness_check              fast
% 7.26/1.49  --demod_use_ground                      true
% 7.26/1.49  --sup_to_prop_solver                    passive
% 7.26/1.49  --sup_prop_simpl_new                    true
% 7.26/1.49  --sup_prop_simpl_given                  true
% 7.26/1.49  --sup_fun_splitting                     false
% 7.26/1.49  --sup_smt_interval                      50000
% 7.26/1.49  
% 7.26/1.49  ------ Superposition Simplification Setup
% 7.26/1.49  
% 7.26/1.49  --sup_indices_passive                   []
% 7.26/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.49  --sup_full_bw                           [BwDemod]
% 7.26/1.49  --sup_immed_triv                        [TrivRules]
% 7.26/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.49  --sup_immed_bw_main                     []
% 7.26/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.49  
% 7.26/1.49  ------ Combination Options
% 7.26/1.49  
% 7.26/1.49  --comb_res_mult                         3
% 7.26/1.49  --comb_sup_mult                         2
% 7.26/1.49  --comb_inst_mult                        10
% 7.26/1.49  
% 7.26/1.49  ------ Debug Options
% 7.26/1.49  
% 7.26/1.49  --dbg_backtrace                         false
% 7.26/1.49  --dbg_dump_prop_clauses                 false
% 7.26/1.49  --dbg_dump_prop_clauses_file            -
% 7.26/1.49  --dbg_out_stat                          false
% 7.26/1.49  ------ Parsing...
% 7.26/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.49  
% 7.26/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.26/1.49  
% 7.26/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.49  
% 7.26/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.49  ------ Proving...
% 7.26/1.49  ------ Problem Properties 
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  clauses                                 43
% 7.26/1.49  conjectures                             1
% 7.26/1.49  EPR                                     11
% 7.26/1.49  Horn                                    35
% 7.26/1.49  unary                                   5
% 7.26/1.49  binary                                  12
% 7.26/1.49  lits                                    117
% 7.26/1.49  lits eq                                 11
% 7.26/1.49  fd_pure                                 0
% 7.26/1.49  fd_pseudo                               0
% 7.26/1.49  fd_cond                                 1
% 7.26/1.49  fd_pseudo_cond                          2
% 7.26/1.49  AC symbols                              0
% 7.26/1.49  
% 7.26/1.49  ------ Schedule dynamic 5 is on 
% 7.26/1.49  
% 7.26/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  ------ 
% 7.26/1.49  Current options:
% 7.26/1.49  ------ 
% 7.26/1.49  
% 7.26/1.49  ------ Input Options
% 7.26/1.49  
% 7.26/1.49  --out_options                           all
% 7.26/1.49  --tptp_safe_out                         true
% 7.26/1.49  --problem_path                          ""
% 7.26/1.49  --include_path                          ""
% 7.26/1.49  --clausifier                            res/vclausify_rel
% 7.26/1.49  --clausifier_options                    --mode clausify
% 7.26/1.49  --stdin                                 false
% 7.26/1.49  --stats_out                             all
% 7.26/1.49  
% 7.26/1.49  ------ General Options
% 7.26/1.49  
% 7.26/1.49  --fof                                   false
% 7.26/1.49  --time_out_real                         305.
% 7.26/1.49  --time_out_virtual                      -1.
% 7.26/1.49  --symbol_type_check                     false
% 7.26/1.49  --clausify_out                          false
% 7.26/1.49  --sig_cnt_out                           false
% 7.26/1.49  --trig_cnt_out                          false
% 7.26/1.49  --trig_cnt_out_tolerance                1.
% 7.26/1.49  --trig_cnt_out_sk_spl                   false
% 7.26/1.49  --abstr_cl_out                          false
% 7.26/1.49  
% 7.26/1.49  ------ Global Options
% 7.26/1.49  
% 7.26/1.49  --schedule                              default
% 7.26/1.49  --add_important_lit                     false
% 7.26/1.49  --prop_solver_per_cl                    1000
% 7.26/1.49  --min_unsat_core                        false
% 7.26/1.49  --soft_assumptions                      false
% 7.26/1.49  --soft_lemma_size                       3
% 7.26/1.49  --prop_impl_unit_size                   0
% 7.26/1.49  --prop_impl_unit                        []
% 7.26/1.49  --share_sel_clauses                     true
% 7.26/1.49  --reset_solvers                         false
% 7.26/1.49  --bc_imp_inh                            [conj_cone]
% 7.26/1.49  --conj_cone_tolerance                   3.
% 7.26/1.49  --extra_neg_conj                        none
% 7.26/1.49  --large_theory_mode                     true
% 7.26/1.49  --prolific_symb_bound                   200
% 7.26/1.49  --lt_threshold                          2000
% 7.26/1.49  --clause_weak_htbl                      true
% 7.26/1.49  --gc_record_bc_elim                     false
% 7.26/1.49  
% 7.26/1.49  ------ Preprocessing Options
% 7.26/1.49  
% 7.26/1.49  --preprocessing_flag                    true
% 7.26/1.49  --time_out_prep_mult                    0.1
% 7.26/1.49  --splitting_mode                        input
% 7.26/1.49  --splitting_grd                         true
% 7.26/1.49  --splitting_cvd                         false
% 7.26/1.49  --splitting_cvd_svl                     false
% 7.26/1.49  --splitting_nvd                         32
% 7.26/1.49  --sub_typing                            true
% 7.26/1.49  --prep_gs_sim                           true
% 7.26/1.49  --prep_unflatten                        true
% 7.26/1.49  --prep_res_sim                          true
% 7.26/1.49  --prep_upred                            true
% 7.26/1.49  --prep_sem_filter                       exhaustive
% 7.26/1.49  --prep_sem_filter_out                   false
% 7.26/1.49  --pred_elim                             true
% 7.26/1.49  --res_sim_input                         true
% 7.26/1.49  --eq_ax_congr_red                       true
% 7.26/1.49  --pure_diseq_elim                       true
% 7.26/1.49  --brand_transform                       false
% 7.26/1.49  --non_eq_to_eq                          false
% 7.26/1.49  --prep_def_merge                        true
% 7.26/1.49  --prep_def_merge_prop_impl              false
% 7.26/1.49  --prep_def_merge_mbd                    true
% 7.26/1.49  --prep_def_merge_tr_red                 false
% 7.26/1.49  --prep_def_merge_tr_cl                  false
% 7.26/1.49  --smt_preprocessing                     true
% 7.26/1.49  --smt_ac_axioms                         fast
% 7.26/1.49  --preprocessed_out                      false
% 7.26/1.49  --preprocessed_stats                    false
% 7.26/1.49  
% 7.26/1.49  ------ Abstraction refinement Options
% 7.26/1.49  
% 7.26/1.49  --abstr_ref                             []
% 7.26/1.49  --abstr_ref_prep                        false
% 7.26/1.49  --abstr_ref_until_sat                   false
% 7.26/1.49  --abstr_ref_sig_restrict                funpre
% 7.26/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.49  --abstr_ref_under                       []
% 7.26/1.49  
% 7.26/1.49  ------ SAT Options
% 7.26/1.49  
% 7.26/1.49  --sat_mode                              false
% 7.26/1.49  --sat_fm_restart_options                ""
% 7.26/1.49  --sat_gr_def                            false
% 7.26/1.49  --sat_epr_types                         true
% 7.26/1.49  --sat_non_cyclic_types                  false
% 7.26/1.49  --sat_finite_models                     false
% 7.26/1.49  --sat_fm_lemmas                         false
% 7.26/1.49  --sat_fm_prep                           false
% 7.26/1.49  --sat_fm_uc_incr                        true
% 7.26/1.49  --sat_out_model                         small
% 7.26/1.49  --sat_out_clauses                       false
% 7.26/1.49  
% 7.26/1.49  ------ QBF Options
% 7.26/1.49  
% 7.26/1.49  --qbf_mode                              false
% 7.26/1.49  --qbf_elim_univ                         false
% 7.26/1.49  --qbf_dom_inst                          none
% 7.26/1.49  --qbf_dom_pre_inst                      false
% 7.26/1.49  --qbf_sk_in                             false
% 7.26/1.49  --qbf_pred_elim                         true
% 7.26/1.49  --qbf_split                             512
% 7.26/1.49  
% 7.26/1.49  ------ BMC1 Options
% 7.26/1.49  
% 7.26/1.49  --bmc1_incremental                      false
% 7.26/1.49  --bmc1_axioms                           reachable_all
% 7.26/1.49  --bmc1_min_bound                        0
% 7.26/1.49  --bmc1_max_bound                        -1
% 7.26/1.49  --bmc1_max_bound_default                -1
% 7.26/1.49  --bmc1_symbol_reachability              true
% 7.26/1.49  --bmc1_property_lemmas                  false
% 7.26/1.49  --bmc1_k_induction                      false
% 7.26/1.49  --bmc1_non_equiv_states                 false
% 7.26/1.49  --bmc1_deadlock                         false
% 7.26/1.49  --bmc1_ucm                              false
% 7.26/1.49  --bmc1_add_unsat_core                   none
% 7.26/1.49  --bmc1_unsat_core_children              false
% 7.26/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.49  --bmc1_out_stat                         full
% 7.26/1.49  --bmc1_ground_init                      false
% 7.26/1.49  --bmc1_pre_inst_next_state              false
% 7.26/1.49  --bmc1_pre_inst_state                   false
% 7.26/1.49  --bmc1_pre_inst_reach_state             false
% 7.26/1.49  --bmc1_out_unsat_core                   false
% 7.26/1.49  --bmc1_aig_witness_out                  false
% 7.26/1.49  --bmc1_verbose                          false
% 7.26/1.49  --bmc1_dump_clauses_tptp                false
% 7.26/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.49  --bmc1_dump_file                        -
% 7.26/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.49  --bmc1_ucm_extend_mode                  1
% 7.26/1.49  --bmc1_ucm_init_mode                    2
% 7.26/1.49  --bmc1_ucm_cone_mode                    none
% 7.26/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.49  --bmc1_ucm_relax_model                  4
% 7.26/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.49  --bmc1_ucm_layered_model                none
% 7.26/1.49  --bmc1_ucm_max_lemma_size               10
% 7.26/1.49  
% 7.26/1.49  ------ AIG Options
% 7.26/1.49  
% 7.26/1.49  --aig_mode                              false
% 7.26/1.49  
% 7.26/1.49  ------ Instantiation Options
% 7.26/1.49  
% 7.26/1.49  --instantiation_flag                    true
% 7.26/1.49  --inst_sos_flag                         false
% 7.26/1.49  --inst_sos_phase                        true
% 7.26/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.49  --inst_lit_sel_side                     none
% 7.26/1.49  --inst_solver_per_active                1400
% 7.26/1.49  --inst_solver_calls_frac                1.
% 7.26/1.49  --inst_passive_queue_type               priority_queues
% 7.26/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.49  --inst_passive_queues_freq              [25;2]
% 7.26/1.49  --inst_dismatching                      true
% 7.26/1.49  --inst_eager_unprocessed_to_passive     true
% 7.26/1.49  --inst_prop_sim_given                   true
% 7.26/1.49  --inst_prop_sim_new                     false
% 7.26/1.49  --inst_subs_new                         false
% 7.26/1.49  --inst_eq_res_simp                      false
% 7.26/1.49  --inst_subs_given                       false
% 7.26/1.49  --inst_orphan_elimination               true
% 7.26/1.49  --inst_learning_loop_flag               true
% 7.26/1.49  --inst_learning_start                   3000
% 7.26/1.49  --inst_learning_factor                  2
% 7.26/1.49  --inst_start_prop_sim_after_learn       3
% 7.26/1.49  --inst_sel_renew                        solver
% 7.26/1.49  --inst_lit_activity_flag                true
% 7.26/1.49  --inst_restr_to_given                   false
% 7.26/1.49  --inst_activity_threshold               500
% 7.26/1.49  --inst_out_proof                        true
% 7.26/1.49  
% 7.26/1.49  ------ Resolution Options
% 7.26/1.49  
% 7.26/1.49  --resolution_flag                       false
% 7.26/1.49  --res_lit_sel                           adaptive
% 7.26/1.49  --res_lit_sel_side                      none
% 7.26/1.49  --res_ordering                          kbo
% 7.26/1.49  --res_to_prop_solver                    active
% 7.26/1.49  --res_prop_simpl_new                    false
% 7.26/1.49  --res_prop_simpl_given                  true
% 7.26/1.49  --res_passive_queue_type                priority_queues
% 7.26/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.49  --res_passive_queues_freq               [15;5]
% 7.26/1.49  --res_forward_subs                      full
% 7.26/1.49  --res_backward_subs                     full
% 7.26/1.49  --res_forward_subs_resolution           true
% 7.26/1.49  --res_backward_subs_resolution          true
% 7.26/1.49  --res_orphan_elimination                true
% 7.26/1.49  --res_time_limit                        2.
% 7.26/1.49  --res_out_proof                         true
% 7.26/1.49  
% 7.26/1.49  ------ Superposition Options
% 7.26/1.49  
% 7.26/1.49  --superposition_flag                    true
% 7.26/1.49  --sup_passive_queue_type                priority_queues
% 7.26/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.49  --demod_completeness_check              fast
% 7.26/1.49  --demod_use_ground                      true
% 7.26/1.49  --sup_to_prop_solver                    passive
% 7.26/1.49  --sup_prop_simpl_new                    true
% 7.26/1.49  --sup_prop_simpl_given                  true
% 7.26/1.49  --sup_fun_splitting                     false
% 7.26/1.49  --sup_smt_interval                      50000
% 7.26/1.49  
% 7.26/1.49  ------ Superposition Simplification Setup
% 7.26/1.49  
% 7.26/1.49  --sup_indices_passive                   []
% 7.26/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.49  --sup_full_bw                           [BwDemod]
% 7.26/1.49  --sup_immed_triv                        [TrivRules]
% 7.26/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.49  --sup_immed_bw_main                     []
% 7.26/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.49  
% 7.26/1.49  ------ Combination Options
% 7.26/1.49  
% 7.26/1.49  --comb_res_mult                         3
% 7.26/1.49  --comb_sup_mult                         2
% 7.26/1.49  --comb_inst_mult                        10
% 7.26/1.49  
% 7.26/1.49  ------ Debug Options
% 7.26/1.49  
% 7.26/1.49  --dbg_backtrace                         false
% 7.26/1.49  --dbg_dump_prop_clauses                 false
% 7.26/1.49  --dbg_dump_prop_clauses_file            -
% 7.26/1.49  --dbg_out_stat                          false
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  ------ Proving...
% 7.26/1.49  
% 7.26/1.49  
% 7.26/1.49  % SZS status Theorem for theBenchmark.p
% 7.26/1.49  
% 7.26/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.49  
% 7.26/1.49  fof(f21,conjecture,(
% 7.26/1.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f22,negated_conjecture,(
% 7.26/1.49    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.26/1.49    inference(negated_conjecture,[],[f21])).
% 7.26/1.49  
% 7.26/1.49  fof(f43,plain,(
% 7.26/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 7.26/1.49    inference(ennf_transformation,[],[f22])).
% 7.26/1.49  
% 7.26/1.49  fof(f68,plain,(
% 7.26/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8)))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f69,plain,(
% 7.26/1.49    (~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)) & r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f43,f68])).
% 7.26/1.49  
% 7.26/1.49  fof(f118,plain,(
% 7.26/1.49    r2_hidden(sK9,k1_funct_2(sK7,sK8))),
% 7.26/1.49    inference(cnf_transformation,[],[f69])).
% 7.26/1.49  
% 7.26/1.49  fof(f19,axiom,(
% 7.26/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f44,plain,(
% 7.26/1.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.26/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.26/1.49  
% 7.26/1.49  fof(f45,plain,(
% 7.26/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 7.26/1.49    inference(definition_folding,[],[f19,f44])).
% 7.26/1.49  
% 7.26/1.49  fof(f67,plain,(
% 7.26/1.49    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 7.26/1.49    inference(nnf_transformation,[],[f45])).
% 7.26/1.49  
% 7.26/1.49  fof(f113,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 7.26/1.49    inference(cnf_transformation,[],[f67])).
% 7.26/1.49  
% 7.26/1.49  fof(f125,plain,(
% 7.26/1.49    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 7.26/1.49    inference(equality_resolution,[],[f113])).
% 7.26/1.49  
% 7.26/1.49  fof(f61,plain,(
% 7.26/1.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 7.26/1.49    inference(nnf_transformation,[],[f44])).
% 7.26/1.49  
% 7.26/1.49  fof(f62,plain,(
% 7.26/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.26/1.49    inference(rectify,[],[f61])).
% 7.26/1.49  
% 7.26/1.49  fof(f65,plain,(
% 7.26/1.49    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0) & k1_relat_1(sK6(X0,X1,X6)) = X1 & sK6(X0,X1,X6) = X6 & v1_funct_1(sK6(X0,X1,X6)) & v1_relat_1(sK6(X0,X1,X6))))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f64,plain,(
% 7.26/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) & k1_relat_1(sK5(X0,X1,X2)) = X1 & sK5(X0,X1,X2) = X3 & v1_funct_1(sK5(X0,X1,X2)) & v1_relat_1(sK5(X0,X1,X2))))) )),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f63,plain,(
% 7.26/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK4(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK4(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f66,plain,(
% 7.26/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK4(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK5(X0,X1,X2)),X0) & k1_relat_1(sK5(X0,X1,X2)) = X1 & sK4(X0,X1,X2) = sK5(X0,X1,X2) & v1_funct_1(sK5(X0,X1,X2)) & v1_relat_1(sK5(X0,X1,X2))) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0) & k1_relat_1(sK6(X0,X1,X6)) = X1 & sK6(X0,X1,X6) = X6 & v1_funct_1(sK6(X0,X1,X6)) & v1_relat_1(sK6(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f62,f65,f64,f63])).
% 7.26/1.49  
% 7.26/1.49  fof(f103,plain,(
% 7.26/1.49    ( ! [X6,X2,X0,X1] : (sK6(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f66])).
% 7.26/1.49  
% 7.26/1.49  fof(f105,plain,(
% 7.26/1.49    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK6(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f66])).
% 7.26/1.49  
% 7.26/1.49  fof(f104,plain,(
% 7.26/1.49    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK6(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f66])).
% 7.26/1.49  
% 7.26/1.49  fof(f20,axiom,(
% 7.26/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f41,plain,(
% 7.26/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f20])).
% 7.26/1.49  
% 7.26/1.49  fof(f42,plain,(
% 7.26/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.26/1.49    inference(flattening,[],[f41])).
% 7.26/1.49  
% 7.26/1.49  fof(f117,plain,(
% 7.26/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f42])).
% 7.26/1.49  
% 7.26/1.49  fof(f4,axiom,(
% 7.26/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f54,plain,(
% 7.26/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.49    inference(nnf_transformation,[],[f4])).
% 7.26/1.49  
% 7.26/1.49  fof(f55,plain,(
% 7.26/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.26/1.49    inference(flattening,[],[f54])).
% 7.26/1.49  
% 7.26/1.49  fof(f76,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.26/1.49    inference(cnf_transformation,[],[f55])).
% 7.26/1.49  
% 7.26/1.49  fof(f121,plain,(
% 7.26/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.26/1.49    inference(equality_resolution,[],[f76])).
% 7.26/1.49  
% 7.26/1.49  fof(f78,plain,(
% 7.26/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f55])).
% 7.26/1.49  
% 7.26/1.49  fof(f102,plain,(
% 7.26/1.49    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK6(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f66])).
% 7.26/1.49  
% 7.26/1.49  fof(f101,plain,(
% 7.26/1.49    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK6(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f66])).
% 7.26/1.49  
% 7.26/1.49  fof(f15,axiom,(
% 7.26/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f34,plain,(
% 7.26/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.26/1.49    inference(ennf_transformation,[],[f15])).
% 7.26/1.49  
% 7.26/1.49  fof(f35,plain,(
% 7.26/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.26/1.49    inference(flattening,[],[f34])).
% 7.26/1.49  
% 7.26/1.49  fof(f95,plain,(
% 7.26/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 7.26/1.49    inference(cnf_transformation,[],[f35])).
% 7.26/1.49  
% 7.26/1.49  fof(f116,plain,(
% 7.26/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f42])).
% 7.26/1.49  
% 7.26/1.49  fof(f119,plain,(
% 7.26/1.49    ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9)),
% 7.26/1.49    inference(cnf_transformation,[],[f69])).
% 7.26/1.49  
% 7.26/1.49  fof(f12,axiom,(
% 7.26/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f31,plain,(
% 7.26/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.49    inference(ennf_transformation,[],[f12])).
% 7.26/1.49  
% 7.26/1.49  fof(f92,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.49    inference(cnf_transformation,[],[f31])).
% 7.26/1.49  
% 7.26/1.49  fof(f18,axiom,(
% 7.26/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f39,plain,(
% 7.26/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.26/1.49    inference(ennf_transformation,[],[f18])).
% 7.26/1.49  
% 7.26/1.49  fof(f40,plain,(
% 7.26/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.26/1.49    inference(flattening,[],[f39])).
% 7.26/1.49  
% 7.26/1.49  fof(f100,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f40])).
% 7.26/1.49  
% 7.26/1.49  fof(f16,axiom,(
% 7.26/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f36,plain,(
% 7.26/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.49    inference(ennf_transformation,[],[f16])).
% 7.26/1.49  
% 7.26/1.49  fof(f37,plain,(
% 7.26/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.49    inference(flattening,[],[f36])).
% 7.26/1.49  
% 7.26/1.49  fof(f97,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.49    inference(cnf_transformation,[],[f37])).
% 7.26/1.49  
% 7.26/1.49  fof(f14,axiom,(
% 7.26/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f33,plain,(
% 7.26/1.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 7.26/1.49    inference(ennf_transformation,[],[f14])).
% 7.26/1.49  
% 7.26/1.49  fof(f94,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f33])).
% 7.26/1.49  
% 7.26/1.49  fof(f2,axiom,(
% 7.26/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f24,plain,(
% 7.26/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f2])).
% 7.26/1.49  
% 7.26/1.49  fof(f50,plain,(
% 7.26/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.49    inference(nnf_transformation,[],[f24])).
% 7.26/1.49  
% 7.26/1.49  fof(f51,plain,(
% 7.26/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.49    inference(rectify,[],[f50])).
% 7.26/1.49  
% 7.26/1.49  fof(f52,plain,(
% 7.26/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f53,plain,(
% 7.26/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 7.26/1.49  
% 7.26/1.49  fof(f73,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f53])).
% 7.26/1.49  
% 7.26/1.49  fof(f1,axiom,(
% 7.26/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f46,plain,(
% 7.26/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.49    inference(nnf_transformation,[],[f1])).
% 7.26/1.49  
% 7.26/1.49  fof(f47,plain,(
% 7.26/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.49    inference(rectify,[],[f46])).
% 7.26/1.49  
% 7.26/1.49  fof(f48,plain,(
% 7.26/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f49,plain,(
% 7.26/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 7.26/1.49  
% 7.26/1.49  fof(f70,plain,(
% 7.26/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f49])).
% 7.26/1.49  
% 7.26/1.49  fof(f8,axiom,(
% 7.26/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f59,plain,(
% 7.26/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.26/1.49    inference(nnf_transformation,[],[f8])).
% 7.26/1.49  
% 7.26/1.49  fof(f86,plain,(
% 7.26/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f59])).
% 7.26/1.49  
% 7.26/1.49  fof(f13,axiom,(
% 7.26/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f23,plain,(
% 7.26/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.26/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.26/1.49  
% 7.26/1.49  fof(f32,plain,(
% 7.26/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.26/1.49    inference(ennf_transformation,[],[f23])).
% 7.26/1.49  
% 7.26/1.49  fof(f93,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.26/1.49    inference(cnf_transformation,[],[f32])).
% 7.26/1.49  
% 7.26/1.49  fof(f10,axiom,(
% 7.26/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f28,plain,(
% 7.26/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.26/1.49    inference(ennf_transformation,[],[f10])).
% 7.26/1.49  
% 7.26/1.49  fof(f60,plain,(
% 7.26/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.26/1.49    inference(nnf_transformation,[],[f28])).
% 7.26/1.49  
% 7.26/1.49  fof(f88,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f60])).
% 7.26/1.49  
% 7.26/1.49  fof(f17,axiom,(
% 7.26/1.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f38,plain,(
% 7.26/1.49    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 7.26/1.49    inference(ennf_transformation,[],[f17])).
% 7.26/1.49  
% 7.26/1.49  fof(f98,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f38])).
% 7.26/1.49  
% 7.26/1.49  fof(f7,axiom,(
% 7.26/1.49    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f57,plain,(
% 7.26/1.49    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 7.26/1.49    introduced(choice_axiom,[])).
% 7.26/1.49  
% 7.26/1.49  fof(f58,plain,(
% 7.26/1.49    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 7.26/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f57])).
% 7.26/1.49  
% 7.26/1.49  fof(f84,plain,(
% 7.26/1.49    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f58])).
% 7.26/1.49  
% 7.26/1.49  fof(f6,axiom,(
% 7.26/1.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f26,plain,(
% 7.26/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.26/1.49    inference(ennf_transformation,[],[f6])).
% 7.26/1.49  
% 7.26/1.49  fof(f56,plain,(
% 7.26/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.26/1.49    inference(nnf_transformation,[],[f26])).
% 7.26/1.49  
% 7.26/1.49  fof(f80,plain,(
% 7.26/1.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f56])).
% 7.26/1.49  
% 7.26/1.49  fof(f9,axiom,(
% 7.26/1.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.26/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.49  
% 7.26/1.49  fof(f27,plain,(
% 7.26/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.26/1.49    inference(ennf_transformation,[],[f9])).
% 7.26/1.49  
% 7.26/1.49  fof(f87,plain,(
% 7.26/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.26/1.49    inference(cnf_transformation,[],[f27])).
% 7.26/1.49  
% 7.26/1.49  cnf(c_49,negated_conjecture,
% 7.26/1.49      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) ),
% 7.26/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_4861,plain,
% 7.26/1.49      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_44,plain,
% 7.26/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 7.26/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_4863,plain,
% 7.26/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_40,plain,
% 7.26/1.49      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK6(X0,X1,X3) = X3 ),
% 7.26/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_4867,plain,
% 7.26/1.49      ( sK6(X0,X1,X2) = X2
% 7.26/1.49      | sP0(X0,X1,X3) != iProver_top
% 7.26/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_7647,plain,
% 7.26/1.49      ( sK6(X0,X1,X2) = X2
% 7.26/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_4863,c_4867]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_15140,plain,
% 7.26/1.49      ( sK6(sK8,sK7,sK9) = sK9 ),
% 7.26/1.49      inference(superposition,[status(thm)],[c_4861,c_7647]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_38,plain,
% 7.26/1.49      ( ~ sP0(X0,X1,X2)
% 7.26/1.49      | r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X0)
% 7.26/1.49      | ~ r2_hidden(X3,X2) ),
% 7.26/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_4869,plain,
% 7.26/1.49      ( sP0(X0,X1,X2) != iProver_top
% 7.26/1.49      | r1_tarski(k2_relat_1(sK6(X0,X1,X3)),X0) = iProver_top
% 7.26/1.49      | r2_hidden(X3,X2) != iProver_top ),
% 7.26/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.26/1.49  
% 7.26/1.49  cnf(c_9137,plain,
% 7.26/1.49      ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X0) = iProver_top
% 7.26/1.50      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4863,c_4869]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_31757,plain,
% 7.26/1.50      ( r1_tarski(k2_relat_1(sK9),sK8) = iProver_top
% 7.26/1.50      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_15140,c_9137]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_39,plain,
% 7.26/1.50      ( ~ sP0(X0,X1,X2)
% 7.26/1.50      | ~ r2_hidden(X3,X2)
% 7.26/1.50      | k1_relat_1(sK6(X0,X1,X3)) = X1 ),
% 7.26/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4868,plain,
% 7.26/1.50      ( k1_relat_1(sK6(X0,X1,X2)) = X1
% 7.26/1.50      | sP0(X0,X1,X3) != iProver_top
% 7.26/1.50      | r2_hidden(X2,X3) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_8513,plain,
% 7.26/1.50      ( k1_relat_1(sK6(X0,X1,X2)) = X1
% 7.26/1.50      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4863,c_4868]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18621,plain,
% 7.26/1.50      ( k1_relat_1(sK6(sK8,sK7,sK9)) = sK7 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4861,c_8513]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18633,plain,
% 7.26/1.50      ( k1_relat_1(sK9) = sK7 ),
% 7.26/1.50      inference(light_normalisation,[status(thm)],[c_18621,c_15140]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_45,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_relat_1(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4862,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.26/1.50      | v1_funct_1(X0) != iProver_top
% 7.26/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18889,plain,
% 7.26/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top
% 7.26/1.50      | v1_relat_1(sK9) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_18633,c_4862]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_50,plain,
% 7.26/1.50      ( r2_hidden(sK9,k1_funct_2(sK7,sK8)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_8,plain,
% 7.26/1.50      ( r1_tarski(X0,X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f121]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_158,plain,
% 7.26/1.50      ( r1_tarski(sK9,sK9) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6,plain,
% 7.26/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.26/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_162,plain,
% 7.26/1.50      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_41,plain,
% 7.26/1.50      ( ~ sP0(X0,X1,X2)
% 7.26/1.50      | ~ r2_hidden(X3,X2)
% 7.26/1.50      | v1_funct_1(sK6(X0,X1,X3)) ),
% 7.26/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5306,plain,
% 7.26/1.50      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 7.26/1.50      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 7.26/1.50      | v1_funct_1(sK6(X0,X1,sK9)) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_41]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5471,plain,
% 7.26/1.50      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 7.26/1.50      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 7.26/1.50      | v1_funct_1(sK6(sK8,sK7,sK9)) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_5306]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5473,plain,
% 7.26/1.50      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
% 7.26/1.50      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
% 7.26/1.50      | v1_funct_1(sK6(sK8,sK7,sK9)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_5471]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5472,plain,
% 7.26/1.50      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_44]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5475,plain,
% 7.26/1.50      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_5472]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3923,plain,
% 7.26/1.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.26/1.50      theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5645,plain,
% 7.26/1.50      ( v1_funct_1(X0)
% 7.26/1.50      | ~ v1_funct_1(sK6(sK8,sK7,sK9))
% 7.26/1.50      | X0 != sK6(sK8,sK7,sK9) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_3923]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5646,plain,
% 7.26/1.50      ( X0 != sK6(sK8,sK7,sK9)
% 7.26/1.50      | v1_funct_1(X0) = iProver_top
% 7.26/1.50      | v1_funct_1(sK6(sK8,sK7,sK9)) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_5645]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5648,plain,
% 7.26/1.50      ( sK9 != sK6(sK8,sK7,sK9)
% 7.26/1.50      | v1_funct_1(sK6(sK8,sK7,sK9)) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) = iProver_top ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_5646]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_42,plain,
% 7.26/1.50      ( ~ sP0(X0,X1,X2)
% 7.26/1.50      | ~ r2_hidden(X3,X2)
% 7.26/1.50      | v1_relat_1(sK6(X0,X1,X3)) ),
% 7.26/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5318,plain,
% 7.26/1.50      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 7.26/1.50      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 7.26/1.50      | v1_relat_1(sK6(X0,X1,sK9)) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_42]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5655,plain,
% 7.26/1.50      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 7.26/1.50      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 7.26/1.50      | v1_relat_1(sK6(sK8,sK7,sK9)) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_5318]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5657,plain,
% 7.26/1.50      ( sP0(sK8,sK7,k1_funct_2(sK7,sK8)) != iProver_top
% 7.26/1.50      | r2_hidden(sK9,k1_funct_2(sK7,sK8)) != iProver_top
% 7.26/1.50      | v1_relat_1(sK6(sK8,sK7,sK9)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_5655]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5343,plain,
% 7.26/1.50      ( ~ sP0(X0,X1,k1_funct_2(sK7,sK8))
% 7.26/1.50      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 7.26/1.50      | sK6(X0,X1,sK9) = sK9 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_40]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5654,plain,
% 7.26/1.50      ( ~ sP0(sK8,sK7,k1_funct_2(sK7,sK8))
% 7.26/1.50      | ~ r2_hidden(sK9,k1_funct_2(sK7,sK8))
% 7.26/1.50      | sK6(sK8,sK7,sK9) = sK9 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_5343]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3920,plain,
% 7.26/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.26/1.50      theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6300,plain,
% 7.26/1.50      ( v1_relat_1(X0)
% 7.26/1.50      | ~ v1_relat_1(sK6(sK8,sK7,sK9))
% 7.26/1.50      | X0 != sK6(sK8,sK7,sK9) ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_3920]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6301,plain,
% 7.26/1.50      ( X0 != sK6(sK8,sK7,sK9)
% 7.26/1.50      | v1_relat_1(X0) = iProver_top
% 7.26/1.50      | v1_relat_1(sK6(sK8,sK7,sK9)) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_6300]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6303,plain,
% 7.26/1.50      ( sK9 != sK6(sK8,sK7,sK9)
% 7.26/1.50      | v1_relat_1(sK6(sK8,sK7,sK9)) != iProver_top
% 7.26/1.50      | v1_relat_1(sK9) = iProver_top ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_6301]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3913,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6525,plain,
% 7.26/1.50      ( X0 != X1 | X0 = sK6(sK8,sK7,sK9) | sK6(sK8,sK7,sK9) != X1 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_3913]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6526,plain,
% 7.26/1.50      ( sK6(sK8,sK7,sK9) != sK9 | sK9 = sK6(sK8,sK7,sK9) | sK9 != sK9 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_6525]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_19545,plain,
% 7.26/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,k2_relat_1(sK9)))) = iProver_top ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_18889,c_49,c_50,c_158,c_162,c_5473,c_5472,c_5475,
% 7.26/1.50                 c_5648,c_5657,c_5654,c_6303,c_6526]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_25,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.26/1.50      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 7.26/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4877,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.26/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 7.26/1.50      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_19553,plain,
% 7.26/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) = iProver_top
% 7.26/1.50      | r1_tarski(k2_relat_1(sK9),X0) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_19545,c_4877]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_46,plain,
% 7.26/1.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_relat_1(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_48,negated_conjecture,
% 7.26/1.50      ( ~ v1_funct_2(sK9,sK7,sK8)
% 7.26/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9) ),
% 7.26/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_729,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | ~ v1_relat_1(X0)
% 7.26/1.50      | k2_relat_1(X0) != sK8
% 7.26/1.50      | k1_relat_1(X0) != sK7
% 7.26/1.50      | sK9 != X0 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_46,c_48]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_730,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | ~ v1_relat_1(sK9)
% 7.26/1.50      | k2_relat_1(sK9) != sK8
% 7.26/1.50      | k1_relat_1(sK9) != sK7 ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_729]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_22,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | v1_relat_1(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_742,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | k2_relat_1(sK9) != sK8
% 7.26/1.50      | k1_relat_1(sK9) != sK7 ),
% 7.26/1.50      inference(forward_subsumption_resolution,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_730,c_22]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4857,plain,
% 7.26/1.50      ( k2_relat_1(sK9) != sK8
% 7.26/1.50      | k1_relat_1(sK9) != sK7
% 7.26/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18865,plain,
% 7.26/1.50      ( k2_relat_1(sK9) != sK8
% 7.26/1.50      | sK7 != sK7
% 7.26/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_18633,c_4857]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18866,plain,
% 7.26/1.50      ( k2_relat_1(sK9) != sK8
% 7.26/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top ),
% 7.26/1.50      inference(equality_resolution_simp,[status(thm)],[c_18865]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_29,plain,
% 7.26/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.26/1.50      | v1_partfun1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | v1_xboole_0(X2) ),
% 7.26/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_692,plain,
% 7.26/1.50      ( v1_partfun1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_funct_1(X3)
% 7.26/1.50      | ~ v1_relat_1(X3)
% 7.26/1.50      | v1_xboole_0(X2)
% 7.26/1.50      | X3 != X0
% 7.26/1.50      | k2_relat_1(X3) != X2
% 7.26/1.50      | k1_relat_1(X3) != X1 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_29,c_46]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_693,plain,
% 7.26/1.50      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_relat_1(X0)
% 7.26/1.50      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_692]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_697,plain,
% 7.26/1.50      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_relat_1(X0)
% 7.26/1.50      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_693,c_45]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_26,plain,
% 7.26/1.50      ( v1_funct_2(X0,X1,X2)
% 7.26/1.50      | ~ v1_partfun1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | ~ v1_funct_1(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_716,plain,
% 7.26/1.50      ( ~ v1_partfun1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | sK8 != X2
% 7.26/1.50      | sK7 != X1
% 7.26/1.50      | sK9 != X0 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_48]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_717,plain,
% 7.26/1.50      ( ~ v1_partfun1(sK9,sK7)
% 7.26/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9) ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_716]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_780,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(X0)
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | ~ v1_relat_1(X0)
% 7.26/1.50      | v1_xboole_0(k2_relat_1(X0))
% 7.26/1.50      | k1_relat_1(X0) != sK7
% 7.26/1.50      | sK9 != X0 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_697,c_717]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_781,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | ~ v1_relat_1(sK9)
% 7.26/1.50      | v1_xboole_0(k2_relat_1(sK9))
% 7.26/1.50      | k1_relat_1(sK9) != sK7 ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_780]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_782,plain,
% 7.26/1.50      ( k1_relat_1(sK9) != sK7
% 7.26/1.50      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top
% 7.26/1.50      | v1_relat_1(sK9) != iProver_top
% 7.26/1.50      | v1_xboole_0(k2_relat_1(sK9)) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_24,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | ~ v1_xboole_0(X2)
% 7.26/1.50      | v1_xboole_0(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4878,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.26/1.50      | v1_xboole_0(X2) != iProver_top
% 7.26/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_19554,plain,
% 7.26/1.50      ( v1_xboole_0(k2_relat_1(sK9)) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_19545,c_4878]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3,plain,
% 7.26/1.50      ( r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4893,plain,
% 7.26/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.26/1.50      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1,plain,
% 7.26/1.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4895,plain,
% 7.26/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.26/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6117,plain,
% 7.26/1.50      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4893,c_4895]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_15,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4883,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.26/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_23,plain,
% 7.26/1.50      ( v4_relat_1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.26/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_19,plain,
% 7.26/1.50      ( ~ v4_relat_1(X0,X1)
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.26/1.50      | ~ v1_relat_1(X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_618,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1)
% 7.26/1.50      | ~ v1_relat_1(X0) ),
% 7.26/1.50      inference(resolution,[status(thm)],[c_23,c_19]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_622,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(X0),X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_618,c_22]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_623,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.26/1.50      inference(renaming,[status(thm)],[c_622]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4858,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5869,plain,
% 7.26/1.50      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.26/1.50      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4883,c_4858]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_13422,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.26/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_6117,c_5869]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_14462,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(k1_relat_1(X0)),X1) = iProver_top
% 7.26/1.50      | v1_xboole_0(X0) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_13422,c_5869]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18885,plain,
% 7.26/1.50      ( r1_tarski(k1_relat_1(sK7),X0) = iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_18633,c_14462]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4890,plain,
% 7.26/1.50      ( X0 = X1
% 7.26/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.26/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_19370,plain,
% 7.26/1.50      ( k1_relat_1(sK7) = X0
% 7.26/1.50      | r1_tarski(X0,k1_relat_1(sK7)) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_18885,c_4890]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_28,plain,
% 7.26/1.50      ( v1_partfun1(X0,X1)
% 7.26/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | ~ v1_xboole_0(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_762,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.26/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | ~ v1_xboole_0(X1)
% 7.26/1.50      | sK7 != X1
% 7.26/1.50      | sK9 != X0 ),
% 7.26/1.50      inference(resolution_lifted,[status(thm)],[c_28,c_717]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_763,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0)))
% 7.26/1.50      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | ~ v1_xboole_0(sK7) ),
% 7.26/1.50      inference(unflattening,[status(thm)],[c_762]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3910,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 7.26/1.50      | ~ v1_funct_1(sK9)
% 7.26/1.50      | ~ v1_xboole_0(sK7)
% 7.26/1.50      | sP0_iProver_split ),
% 7.26/1.50      inference(splitting,
% 7.26/1.50                [splitting(split),new_symbols(definition,[])],
% 7.26/1.50                [c_763]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4855,plain,
% 7.26/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK7) != iProver_top
% 7.26/1.50      | sP0_iProver_split = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_3910]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3909,plain,
% 7.26/1.50      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0)))
% 7.26/1.50      | ~ sP0_iProver_split ),
% 7.26/1.50      inference(splitting,
% 7.26/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.26/1.50                [c_763]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4856,plain,
% 7.26/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,X0))) != iProver_top
% 7.26/1.50      | sP0_iProver_split != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_3909]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5055,plain,
% 7.26/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK7) != iProver_top ),
% 7.26/1.50      inference(forward_subsumption_resolution,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_4855,c_4856]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5870,plain,
% 7.26/1.50      ( r1_tarski(sK9,k2_zfmisc_1(sK7,sK8)) != iProver_top
% 7.26/1.50      | v1_funct_1(sK9) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK7) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4883,c_5055]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6372,plain,
% 7.26/1.50      ( v1_funct_1(sK9) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK7) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_6117,c_5870]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_14,plain,
% 7.26/1.50      ( m1_subset_1(sK3(X0),X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4884,plain,
% 7.26/1.50      ( m1_subset_1(sK3(X0),X0) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_13,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4885,plain,
% 7.26/1.50      ( m1_subset_1(X0,X1) != iProver_top
% 7.26/1.50      | r2_hidden(X0,X1) = iProver_top
% 7.26/1.50      | v1_xboole_0(X1) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6577,plain,
% 7.26/1.50      ( r2_hidden(sK3(X0),X0) = iProver_top
% 7.26/1.50      | v1_xboole_0(X0) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4884,c_4885]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_18887,plain,
% 7.26/1.50      ( r1_tarski(sK7,X0) = iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_18633,c_13422]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_17,plain,
% 7.26/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.26/1.50      | ~ r2_hidden(X2,X0)
% 7.26/1.50      | ~ v1_xboole_0(X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_386,plain,
% 7.26/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.26/1.50      inference(prop_impl,[status(thm)],[c_15]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_387,plain,
% 7.26/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.26/1.50      inference(renaming,[status(thm)],[c_386]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_462,plain,
% 7.26/1.50      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 7.26/1.50      inference(bin_hyper_res,[status(thm)],[c_17,c_387]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4859,plain,
% 7.26/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.26/1.50      | r2_hidden(X2,X0) != iProver_top
% 7.26/1.50      | v1_xboole_0(X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_19316,plain,
% 7.26/1.50      ( r2_hidden(X0,sK7) != iProver_top
% 7.26/1.50      | v1_xboole_0(X1) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_18887,c_4859]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_24132,plain,
% 7.26/1.50      ( v1_xboole_0(X0) != iProver_top
% 7.26/1.50      | v1_xboole_0(sK7) = iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_6577,c_19316]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_24190,plain,
% 7.26/1.50      ( v1_xboole_0(sK7) = iProver_top
% 7.26/1.50      | v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_24132]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_24211,plain,
% 7.26/1.50      ( v1_xboole_0(sK9) != iProver_top ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_19370,c_49,c_50,c_158,c_162,c_5473,c_5472,c_5475,
% 7.26/1.50                 c_5648,c_5654,c_6372,c_6526,c_24190]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_26059,plain,
% 7.26/1.50      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top ),
% 7.26/1.50      inference(global_propositional_subsumption,
% 7.26/1.50                [status(thm)],
% 7.26/1.50                [c_18866,c_49,c_50,c_158,c_162,c_782,c_5473,c_5472,
% 7.26/1.50                 c_5475,c_5648,c_5657,c_5654,c_6303,c_6372,c_6526,
% 7.26/1.50                 c_18633,c_19554,c_24190]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_26066,plain,
% 7.26/1.50      ( r1_tarski(k2_relat_1(sK9),sK8) != iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_19553,c_26059]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(contradiction,plain,
% 7.26/1.50      ( $false ),
% 7.26/1.50      inference(minisat,[status(thm)],[c_31757,c_26066,c_50]) ).
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  ------                               Statistics
% 7.26/1.50  
% 7.26/1.50  ------ General
% 7.26/1.50  
% 7.26/1.50  abstr_ref_over_cycles:                  0
% 7.26/1.50  abstr_ref_under_cycles:                 0
% 7.26/1.50  gc_basic_clause_elim:                   0
% 7.26/1.50  forced_gc_time:                         0
% 7.26/1.50  parsing_time:                           0.01
% 7.26/1.50  unif_index_cands_time:                  0.
% 7.26/1.50  unif_index_add_time:                    0.
% 7.26/1.50  orderings_time:                         0.
% 7.26/1.50  out_proof_time:                         0.014
% 7.26/1.50  total_time:                             0.694
% 7.26/1.50  num_of_symbols:                         57
% 7.26/1.50  num_of_terms:                           27029
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing
% 7.26/1.50  
% 7.26/1.50  num_of_splits:                          1
% 7.26/1.50  num_of_split_atoms:                     1
% 7.26/1.50  num_of_reused_defs:                     0
% 7.26/1.50  num_eq_ax_congr_red:                    43
% 7.26/1.50  num_of_sem_filtered_clauses:            1
% 7.26/1.50  num_of_subtypes:                        0
% 7.26/1.50  monotx_restored_types:                  0
% 7.26/1.50  sat_num_of_epr_types:                   0
% 7.26/1.50  sat_num_of_non_cyclic_types:            0
% 7.26/1.50  sat_guarded_non_collapsed_types:        0
% 7.26/1.50  num_pure_diseq_elim:                    0
% 7.26/1.50  simp_replaced_by:                       0
% 7.26/1.50  res_preprocessed:                       205
% 7.26/1.50  prep_upred:                             0
% 7.26/1.50  prep_unflattend:                        130
% 7.26/1.50  smt_new_axioms:                         0
% 7.26/1.50  pred_elim_cands:                        7
% 7.26/1.50  pred_elim:                              3
% 7.26/1.50  pred_elim_cl:                           4
% 7.26/1.50  pred_elim_cycles:                       8
% 7.26/1.50  merged_defs:                            8
% 7.26/1.50  merged_defs_ncl:                        0
% 7.26/1.50  bin_hyper_res:                          9
% 7.26/1.50  prep_cycles:                            4
% 7.26/1.50  pred_elim_time:                         0.049
% 7.26/1.50  splitting_time:                         0.
% 7.26/1.50  sem_filter_time:                        0.
% 7.26/1.50  monotx_time:                            0.001
% 7.26/1.50  subtype_inf_time:                       0.
% 7.26/1.50  
% 7.26/1.50  ------ Problem properties
% 7.26/1.50  
% 7.26/1.50  clauses:                                43
% 7.26/1.50  conjectures:                            1
% 7.26/1.50  epr:                                    11
% 7.26/1.50  horn:                                   35
% 7.26/1.50  ground:                                 5
% 7.26/1.50  unary:                                  5
% 7.26/1.50  binary:                                 12
% 7.26/1.50  lits:                                   117
% 7.26/1.50  lits_eq:                                11
% 7.26/1.50  fd_pure:                                0
% 7.26/1.50  fd_pseudo:                              0
% 7.26/1.50  fd_cond:                                1
% 7.26/1.50  fd_pseudo_cond:                         2
% 7.26/1.50  ac_symbols:                             0
% 7.26/1.50  
% 7.26/1.50  ------ Propositional Solver
% 7.26/1.50  
% 7.26/1.50  prop_solver_calls:                      29
% 7.26/1.50  prop_fast_solver_calls:                 2437
% 7.26/1.50  smt_solver_calls:                       0
% 7.26/1.50  smt_fast_solver_calls:                  0
% 7.26/1.50  prop_num_of_clauses:                    10907
% 7.26/1.50  prop_preprocess_simplified:             22351
% 7.26/1.50  prop_fo_subsumed:                       56
% 7.26/1.50  prop_solver_time:                       0.
% 7.26/1.50  smt_solver_time:                        0.
% 7.26/1.50  smt_fast_solver_time:                   0.
% 7.26/1.50  prop_fast_solver_time:                  0.
% 7.26/1.50  prop_unsat_core_time:                   0.001
% 7.26/1.50  
% 7.26/1.50  ------ QBF
% 7.26/1.50  
% 7.26/1.50  qbf_q_res:                              0
% 7.26/1.50  qbf_num_tautologies:                    0
% 7.26/1.50  qbf_prep_cycles:                        0
% 7.26/1.50  
% 7.26/1.50  ------ BMC1
% 7.26/1.50  
% 7.26/1.50  bmc1_current_bound:                     -1
% 7.26/1.50  bmc1_last_solved_bound:                 -1
% 7.26/1.50  bmc1_unsat_core_size:                   -1
% 7.26/1.50  bmc1_unsat_core_parents_size:           -1
% 7.26/1.50  bmc1_merge_next_fun:                    0
% 7.26/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.26/1.50  
% 7.26/1.50  ------ Instantiation
% 7.26/1.50  
% 7.26/1.50  inst_num_of_clauses:                    2308
% 7.26/1.50  inst_num_in_passive:                    1012
% 7.26/1.50  inst_num_in_active:                     945
% 7.26/1.50  inst_num_in_unprocessed:                351
% 7.26/1.50  inst_num_of_loops:                      1270
% 7.26/1.50  inst_num_of_learning_restarts:          0
% 7.26/1.50  inst_num_moves_active_passive:          323
% 7.26/1.50  inst_lit_activity:                      0
% 7.26/1.50  inst_lit_activity_moves:                0
% 7.26/1.50  inst_num_tautologies:                   0
% 7.26/1.50  inst_num_prop_implied:                  0
% 7.26/1.50  inst_num_existing_simplified:           0
% 7.26/1.50  inst_num_eq_res_simplified:             0
% 7.26/1.50  inst_num_child_elim:                    0
% 7.26/1.50  inst_num_of_dismatching_blockings:      1752
% 7.26/1.50  inst_num_of_non_proper_insts:           2462
% 7.26/1.50  inst_num_of_duplicates:                 0
% 7.26/1.50  inst_inst_num_from_inst_to_res:         0
% 7.26/1.50  inst_dismatching_checking_time:         0.
% 7.26/1.50  
% 7.26/1.50  ------ Resolution
% 7.26/1.50  
% 7.26/1.50  res_num_of_clauses:                     0
% 7.26/1.50  res_num_in_passive:                     0
% 7.26/1.50  res_num_in_active:                      0
% 7.26/1.50  res_num_of_loops:                       209
% 7.26/1.50  res_forward_subset_subsumed:            155
% 7.26/1.50  res_backward_subset_subsumed:           0
% 7.26/1.50  res_forward_subsumed:                   0
% 7.26/1.50  res_backward_subsumed:                  0
% 7.26/1.50  res_forward_subsumption_resolution:     4
% 7.26/1.50  res_backward_subsumption_resolution:    0
% 7.26/1.50  res_clause_to_clause_subsumption:       3963
% 7.26/1.50  res_orphan_elimination:                 0
% 7.26/1.50  res_tautology_del:                      141
% 7.26/1.50  res_num_eq_res_simplified:              0
% 7.26/1.50  res_num_sel_changes:                    0
% 7.26/1.50  res_moves_from_active_to_pass:          0
% 7.26/1.50  
% 7.26/1.50  ------ Superposition
% 7.26/1.50  
% 7.26/1.50  sup_time_total:                         0.
% 7.26/1.50  sup_time_generating:                    0.
% 7.26/1.50  sup_time_sim_full:                      0.
% 7.26/1.50  sup_time_sim_immed:                     0.
% 7.26/1.50  
% 7.26/1.50  sup_num_of_clauses:                     946
% 7.26/1.50  sup_num_in_active:                      243
% 7.26/1.50  sup_num_in_passive:                     703
% 7.26/1.50  sup_num_of_loops:                       252
% 7.26/1.50  sup_fw_superposition:                   744
% 7.26/1.50  sup_bw_superposition:                   660
% 7.26/1.50  sup_immediate_simplified:               330
% 7.26/1.50  sup_given_eliminated:                   0
% 7.26/1.50  comparisons_done:                       0
% 7.26/1.50  comparisons_avoided:                    6
% 7.26/1.50  
% 7.26/1.50  ------ Simplifications
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  sim_fw_subset_subsumed:                 98
% 7.26/1.50  sim_bw_subset_subsumed:                 15
% 7.26/1.50  sim_fw_subsumed:                        97
% 7.26/1.50  sim_bw_subsumed:                        2
% 7.26/1.50  sim_fw_subsumption_res:                 8
% 7.26/1.50  sim_bw_subsumption_res:                 1
% 7.26/1.50  sim_tautology_del:                      36
% 7.26/1.50  sim_eq_tautology_del:                   59
% 7.26/1.50  sim_eq_res_simp:                        2
% 7.26/1.50  sim_fw_demodulated:                     8
% 7.26/1.50  sim_bw_demodulated:                     5
% 7.26/1.50  sim_light_normalised:                   143
% 7.26/1.50  sim_joinable_taut:                      0
% 7.26/1.50  sim_joinable_simp:                      0
% 7.26/1.50  sim_ac_normalised:                      0
% 7.26/1.50  sim_smt_subsumption:                    0
% 7.26/1.50  
%------------------------------------------------------------------------------
