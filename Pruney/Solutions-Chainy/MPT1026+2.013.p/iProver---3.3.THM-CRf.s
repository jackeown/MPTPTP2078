%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:14 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  262 (4671 expanded)
%              Number of clauses        :  169 (1484 expanded)
%              Number of leaves         :   23 (1203 expanded)
%              Depth                    :   25
%              Number of atoms          : 1016 (29253 expanded)
%              Number of equality atoms :  428 (8615 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
        | ~ v1_funct_2(sK12,sK10,sK11)
        | ~ v1_funct_1(sK12) )
      & r2_hidden(sK12,k1_funct_2(sK10,sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
      | ~ v1_funct_2(sK12,sK10,sK11)
      | ~ v1_funct_1(sK12) )
    & r2_hidden(sK12,k1_funct_2(sK10,sK11)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f43,f72])).

fof(f125,plain,(
    r2_hidden(sK12,k1_funct_2(sK10,sK11)) ),
    inference(cnf_transformation,[],[f73])).

fof(f17,axiom,(
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
    inference(definition_folding,[],[f17,f44])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f134,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_funct_2(X0,X1)) ),
    inference(equality_resolution,[],[f114])).

fof(f63,plain,(
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

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f67,plain,(
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

fof(f66,plain,(
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

fof(f65,plain,(
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

fof(f68,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f64,f67,f66,f65])).

fof(f104,plain,(
    ! [X6,X2,X0,X1] :
      ( sK8(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f130,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK8(X0,X1,X6)) = X1
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f70])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f135,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f124])).

fof(f102,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f103,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK8(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK9(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f136,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f123])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f137,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f122])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f126,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_funct_2(sK12,sK10,sK11)
    | ~ v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f73])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK9(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f138,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f121])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f128,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f23])).

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

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f117,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_52,negated_conjecture,
    ( r2_hidden(sK12,k1_funct_2(sK10,sK11)) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_6469,plain,
    ( r2_hidden(sK12,k1_funct_2(sK10,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_41,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_6473,plain,
    ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_37,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | sK8(X0,X1,X3) = X3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_6477,plain,
    ( sK8(X0,X1,X2) = X2
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9198,plain,
    ( sK8(X0,X1,X2) = X2
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6477])).

cnf(c_9537,plain,
    ( sK8(sK11,sK10,sK12) = sK12 ),
    inference(superposition,[status(thm)],[c_6469,c_9198])).

cnf(c_35,plain,
    ( ~ sP0(X0,X1,X2)
    | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0)
    | ~ r2_hidden(X3,X2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6479,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) = iProver_top
    | r2_hidden(X3,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11288,plain,
    ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0) = iProver_top
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6479])).

cnf(c_30897,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) = iProver_top
    | r2_hidden(sK12,k1_funct_2(sK10,sK11)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9537,c_11288])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_15])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_615,plain,
    ( r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_611,c_16])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_615])).

cnf(c_6468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_7658,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X1),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_6468])).

cnf(c_36,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | k1_relat_1(sK8(X0,X1,X3)) = X1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_6478,plain,
    ( k1_relat_1(sK8(X0,X1,X2)) = X1
    | sP0(X0,X1,X3) != iProver_top
    | r2_hidden(X2,X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10028,plain,
    ( k1_relat_1(sK8(X0,X1,X2)) = X1
    | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6478])).

cnf(c_10861,plain,
    ( k1_relat_1(sK8(sK11,sK10,sK12)) = sK10 ),
    inference(superposition,[status(thm)],[c_6469,c_10028])).

cnf(c_10863,plain,
    ( k1_relat_1(sK12) = sK10 ),
    inference(light_normalisation,[status(thm)],[c_10861,c_9537])).

cnf(c_45,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_6471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_10971,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK12),X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_10863,c_6471])).

cnf(c_10987,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10971,c_10863])).

cnf(c_39,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_relat_1(sK8(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6475,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_relat_1(sK8(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_9378,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_relat_1(sK8(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6475])).

cnf(c_10433,plain,
    ( v1_relat_1(sK8(sK11,sK10,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6469,c_9378])).

cnf(c_10435,plain,
    ( v1_relat_1(sK12) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10433,c_9537])).

cnf(c_38,plain,
    ( ~ sP0(X0,X1,X2)
    | ~ r2_hidden(X3,X2)
    | v1_funct_1(sK8(X0,X1,X3)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_6476,plain,
    ( sP0(X0,X1,X2) != iProver_top
    | r2_hidden(X3,X2) != iProver_top
    | v1_funct_1(sK8(X0,X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_9925,plain,
    ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
    | v1_funct_1(sK8(X2,X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6473,c_6476])).

cnf(c_10665,plain,
    ( v1_funct_1(sK8(sK11,sK10,sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6469,c_9925])).

cnf(c_10667,plain,
    ( v1_funct_1(sK12) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10665,c_9537])).

cnf(c_11961,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
    | r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10987,c_10435,c_10667])).

cnf(c_16075,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK9(sK10,X0,sK12),k1_relat_1(sK12)) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_7658,c_11961])).

cnf(c_16110,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK9(sK10,X0,sK12),sK10) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16075,c_10863])).

cnf(c_46,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_6470,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_10972,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK12),X0))) = iProver_top
    | r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_10863,c_6470])).

cnf(c_10978,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
    | r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10972,c_10863])).

cnf(c_12045,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
    | r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10978,c_10435,c_10667])).

cnf(c_16827,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16110,c_10435,c_10667,c_10978])).

cnf(c_16842,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_16827,c_6468])).

cnf(c_16869,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16842,c_10863])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_47,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_714,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k1_funct_1(X3,sK9(k1_relat_1(X3),X4,X3)),X4)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | X4 != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_47])).

cnf(c_715,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_717,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_715,c_45])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_731,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_717,c_1])).

cnf(c_24,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_51,negated_conjecture,
    ( ~ v1_funct_2(sK12,sK10,sK11)
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_739,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK12)
    | sK11 != X2
    | sK10 != X1
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_51])).

cnf(c_740,plain,
    ( ~ v1_partfun1(sK12,sK10)
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_funct_1(sK12) ),
    inference(unflattening,[status(thm)],[c_739])).

cnf(c_844,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK12)
    | k1_relat_1(X0) != sK10
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_731,c_740])).

cnf(c_845,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0)
    | ~ v1_relat_1(sK12)
    | ~ v1_funct_1(sK12)
    | k1_relat_1(sK12) != sK10 ),
    inference(unflattening,[status(thm)],[c_844])).

cnf(c_859,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0)
    | ~ v1_funct_1(sK12)
    | k1_relat_1(sK12) != sK10 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_845,c_16])).

cnf(c_5468,plain,
    ( ~ r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_859])).

cnf(c_6465,plain,
    ( r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5468])).

cnf(c_10906,plain,
    ( r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_10863,c_6465])).

cnf(c_16076,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK9(sK10,X0,sK12),k1_relat_1(sK12)) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_7658,c_10906])).

cnf(c_16101,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK9(sK10,X0,sK12),sK10) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16076,c_10863])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_167,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( r2_hidden(sK1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_6504,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_12058,plain,
    ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
    | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_12045,c_6468])).

cnf(c_12063,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12058,c_10863])).

cnf(c_12183,plain,
    ( r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
    | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12063,c_10667])).

cnf(c_12184,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_12183])).

cnf(c_6503,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12192,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12184,c_6503])).

cnf(c_14290,plain,
    ( r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_6504,c_12192])).

cnf(c_14375,plain,
    ( r2_hidden(sK9(sK10,k1_xboole_0,sK12),sK10) = iProver_top
    | v1_xboole_0(sK10) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14290])).

cnf(c_48,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_771,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK12)
    | k1_relat_1(X0) != sK10
    | sK11 != X1
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_51])).

cnf(c_772,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | r2_hidden(sK9(k1_relat_1(sK12),sK11,sK12),k1_relat_1(sK12))
    | ~ v1_relat_1(sK12)
    | ~ v1_funct_1(sK12)
    | k1_relat_1(sK12) != sK10 ),
    inference(unflattening,[status(thm)],[c_771])).

cnf(c_784,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | r2_hidden(sK9(k1_relat_1(sK12),sK11,sK12),k1_relat_1(sK12))
    | ~ v1_funct_1(sK12)
    | k1_relat_1(sK12) != sK10 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_772,c_16])).

cnf(c_6466,plain,
    ( k1_relat_1(sK12) != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | r2_hidden(sK9(k1_relat_1(sK12),sK11,sK12),k1_relat_1(sK12)) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_10907,plain,
    ( sK10 != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10863,c_6466])).

cnf(c_10916,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10907])).

cnf(c_14647,plain,
    ( r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10916,c_10667])).

cnf(c_14648,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top ),
    inference(renaming,[status(thm)],[c_14647])).

cnf(c_14653,plain,
    ( r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14648,c_12045])).

cnf(c_14655,plain,
    ( v1_xboole_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_14653,c_6503])).

cnf(c_16183,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK9(sK10,k1_xboole_0,sK12),sK10) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_16101])).

cnf(c_16682,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16101,c_167,c_10667,c_14375,c_14655,c_16183])).

cnf(c_5469,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_funct_1(sK12)
    | sP1_iProver_split
    | k1_relat_1(sK12) != sK10 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_859])).

cnf(c_6464,plain,
    ( k1_relat_1(sK12) != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5469])).

cnf(c_10904,plain,
    ( sK10 != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_10863,c_6464])).

cnf(c_10934,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10904])).

cnf(c_5510,plain,
    ( k1_relat_1(sK12) != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5469])).

cnf(c_13908,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10934,c_5510,c_10667,c_10863])).

cnf(c_16845,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_16827,c_13908])).

cnf(c_16921,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16869,c_16682,c_16845])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_6497,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_6501,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7730,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6501,c_6503])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6491,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_14672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_6491])).

cnf(c_15237,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK12),k1_xboole_0) != iProver_top
    | r1_tarski(sK10,X0) != iProver_top
    | v1_relat_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_10863,c_14672])).

cnf(c_15634,plain,
    ( r1_tarski(sK10,X0) != iProver_top
    | r1_tarski(k2_relat_1(sK12),k1_xboole_0) != iProver_top
    | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15237,c_10435])).

cnf(c_15635,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK12),k1_xboole_0) != iProver_top
    | r1_tarski(sK10,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15634])).

cnf(c_15643,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK10,X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7730,c_15635])).

cnf(c_15754,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6497,c_15643])).

cnf(c_43,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_667,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | k2_relat_1(X3) != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_43])).

cnf(c_668,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_42,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_672,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_42])).

cnf(c_889,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK12)
    | v1_xboole_0(k2_relat_1(X0))
    | k1_relat_1(X0) != sK10
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_672,c_740])).

cnf(c_890,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_relat_1(sK12)
    | ~ v1_funct_1(sK12)
    | v1_xboole_0(k2_relat_1(sK12))
    | k1_relat_1(sK12) != sK10 ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_902,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_funct_1(sK12)
    | v1_xboole_0(k2_relat_1(sK12))
    | k1_relat_1(sK12) != sK10 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_890,c_16])).

cnf(c_6461,plain,
    ( k1_relat_1(sK12) != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_10903,plain,
    ( sK10 != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10863,c_6461])).

cnf(c_10941,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10903])).

cnf(c_891,plain,
    ( k1_relat_1(sK12) != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_14268,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10941,c_891,c_10435,c_10667,c_10863])).

cnf(c_14682,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6491,c_14268])).

cnf(c_14707,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14682,c_10863])).

cnf(c_691,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK9(k1_relat_1(X3),X4,X3),k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | X4 != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_48])).

cnf(c_692,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_694,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_46])).

cnf(c_867,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK12)
    | v1_xboole_0(X1)
    | k1_relat_1(X0) != sK10
    | sK12 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_694,c_740])).

cnf(c_868,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12))
    | ~ v1_relat_1(sK12)
    | ~ v1_funct_1(sK12)
    | v1_xboole_0(X0)
    | k1_relat_1(sK12) != sK10 ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_882,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12))
    | ~ v1_funct_1(sK12)
    | v1_xboole_0(X0)
    | k1_relat_1(sK12) != sK10 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_868,c_16])).

cnf(c_5466,plain,
    ( r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12))
    | v1_xboole_0(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_882])).

cnf(c_6463,plain,
    ( r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5466])).

cnf(c_10902,plain,
    ( r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_10863,c_6463])).

cnf(c_6472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_10970,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,k2_relat_1(sK12)))) = iProver_top
    | v1_relat_1(sK12) != iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_10863,c_6472])).

cnf(c_11802,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,k2_relat_1(sK12)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10970,c_10435,c_10667])).

cnf(c_11811,plain,
    ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(superposition,[status(thm)],[c_11802,c_6468])).

cnf(c_11815,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top
    | v1_funct_1(sK12) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11811,c_10863])).

cnf(c_11932,plain,
    ( r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top
    | r2_hidden(X0,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11815,c_10667])).

cnf(c_11933,plain,
    ( r2_hidden(X0,sK10) != iProver_top
    | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11932])).

cnf(c_11942,plain,
    ( r2_hidden(sK9(sK10,k2_relat_1(sK12),sK12),sK10) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_11933,c_10906])).

cnf(c_12876,plain,
    ( v1_xboole_0(k2_relat_1(sK12)) = iProver_top
    | sP1_iProver_split != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_10902,c_11942])).

cnf(c_5467,plain,
    ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    | ~ v1_funct_1(sK12)
    | sP0_iProver_split
    | k1_relat_1(sK12) != sK10 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_882])).

cnf(c_6462,plain,
    ( k1_relat_1(sK12) != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5467])).

cnf(c_10905,plain,
    ( sK10 != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_10863,c_6462])).

cnf(c_10927,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10905])).

cnf(c_5508,plain,
    ( k1_relat_1(sK12) != sK10
    | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | v1_funct_1(sK12) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5467])).

cnf(c_13183,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10927,c_5508,c_10667,c_10863])).

cnf(c_14684,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_6491,c_13183])).

cnf(c_14689,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14684,c_10863])).

cnf(c_15548,plain,
    ( r1_tarski(sK10,sK10) != iProver_top
    | r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14689,c_10435])).

cnf(c_15549,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_15548])).

cnf(c_15555,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15549,c_6497])).

cnf(c_14683,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_6491,c_13908])).

cnf(c_14698,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | v1_relat_1(sK12) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14683,c_10863])).

cnf(c_15588,plain,
    ( r1_tarski(sK10,sK10) != iProver_top
    | r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14698,c_10435])).

cnf(c_15589,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | r1_tarski(sK10,sK10) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_15588])).

cnf(c_15595,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15589,c_6497])).

cnf(c_15625,plain,
    ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
    | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14707,c_12876,c_15555,c_15595])).

cnf(c_53,plain,
    ( r2_hidden(sK12,k1_funct_2(sK10,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30897,c_16921,c_15754,c_15625,c_53])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.62/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.49  
% 7.62/1.49  ------  iProver source info
% 7.62/1.49  
% 7.62/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.49  git: non_committed_changes: false
% 7.62/1.49  git: last_make_outside_of_git: false
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options
% 7.62/1.49  
% 7.62/1.49  --out_options                           all
% 7.62/1.49  --tptp_safe_out                         true
% 7.62/1.49  --problem_path                          ""
% 7.62/1.49  --include_path                          ""
% 7.62/1.49  --clausifier                            res/vclausify_rel
% 7.62/1.49  --clausifier_options                    --mode clausify
% 7.62/1.49  --stdin                                 false
% 7.62/1.49  --stats_out                             all
% 7.62/1.49  
% 7.62/1.49  ------ General Options
% 7.62/1.49  
% 7.62/1.49  --fof                                   false
% 7.62/1.49  --time_out_real                         305.
% 7.62/1.49  --time_out_virtual                      -1.
% 7.62/1.49  --symbol_type_check                     false
% 7.62/1.49  --clausify_out                          false
% 7.62/1.49  --sig_cnt_out                           false
% 7.62/1.49  --trig_cnt_out                          false
% 7.62/1.49  --trig_cnt_out_tolerance                1.
% 7.62/1.49  --trig_cnt_out_sk_spl                   false
% 7.62/1.49  --abstr_cl_out                          false
% 7.62/1.49  
% 7.62/1.49  ------ Global Options
% 7.62/1.49  
% 7.62/1.49  --schedule                              default
% 7.62/1.49  --add_important_lit                     false
% 7.62/1.49  --prop_solver_per_cl                    1000
% 7.62/1.49  --min_unsat_core                        false
% 7.62/1.49  --soft_assumptions                      false
% 7.62/1.49  --soft_lemma_size                       3
% 7.62/1.49  --prop_impl_unit_size                   0
% 7.62/1.49  --prop_impl_unit                        []
% 7.62/1.49  --share_sel_clauses                     true
% 7.62/1.49  --reset_solvers                         false
% 7.62/1.49  --bc_imp_inh                            [conj_cone]
% 7.62/1.49  --conj_cone_tolerance                   3.
% 7.62/1.49  --extra_neg_conj                        none
% 7.62/1.49  --large_theory_mode                     true
% 7.62/1.49  --prolific_symb_bound                   200
% 7.62/1.49  --lt_threshold                          2000
% 7.62/1.49  --clause_weak_htbl                      true
% 7.62/1.49  --gc_record_bc_elim                     false
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing Options
% 7.62/1.49  
% 7.62/1.49  --preprocessing_flag                    true
% 7.62/1.49  --time_out_prep_mult                    0.1
% 7.62/1.49  --splitting_mode                        input
% 7.62/1.49  --splitting_grd                         true
% 7.62/1.49  --splitting_cvd                         false
% 7.62/1.49  --splitting_cvd_svl                     false
% 7.62/1.49  --splitting_nvd                         32
% 7.62/1.49  --sub_typing                            true
% 7.62/1.49  --prep_gs_sim                           true
% 7.62/1.49  --prep_unflatten                        true
% 7.62/1.49  --prep_res_sim                          true
% 7.62/1.49  --prep_upred                            true
% 7.62/1.49  --prep_sem_filter                       exhaustive
% 7.62/1.49  --prep_sem_filter_out                   false
% 7.62/1.49  --pred_elim                             true
% 7.62/1.49  --res_sim_input                         true
% 7.62/1.49  --eq_ax_congr_red                       true
% 7.62/1.49  --pure_diseq_elim                       true
% 7.62/1.49  --brand_transform                       false
% 7.62/1.49  --non_eq_to_eq                          false
% 7.62/1.49  --prep_def_merge                        true
% 7.62/1.49  --prep_def_merge_prop_impl              false
% 7.62/1.49  --prep_def_merge_mbd                    true
% 7.62/1.49  --prep_def_merge_tr_red                 false
% 7.62/1.49  --prep_def_merge_tr_cl                  false
% 7.62/1.49  --smt_preprocessing                     true
% 7.62/1.49  --smt_ac_axioms                         fast
% 7.62/1.49  --preprocessed_out                      false
% 7.62/1.49  --preprocessed_stats                    false
% 7.62/1.49  
% 7.62/1.49  ------ Abstraction refinement Options
% 7.62/1.49  
% 7.62/1.49  --abstr_ref                             []
% 7.62/1.49  --abstr_ref_prep                        false
% 7.62/1.49  --abstr_ref_until_sat                   false
% 7.62/1.49  --abstr_ref_sig_restrict                funpre
% 7.62/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.49  --abstr_ref_under                       []
% 7.62/1.49  
% 7.62/1.49  ------ SAT Options
% 7.62/1.49  
% 7.62/1.49  --sat_mode                              false
% 7.62/1.49  --sat_fm_restart_options                ""
% 7.62/1.49  --sat_gr_def                            false
% 7.62/1.49  --sat_epr_types                         true
% 7.62/1.49  --sat_non_cyclic_types                  false
% 7.62/1.49  --sat_finite_models                     false
% 7.62/1.49  --sat_fm_lemmas                         false
% 7.62/1.49  --sat_fm_prep                           false
% 7.62/1.49  --sat_fm_uc_incr                        true
% 7.62/1.49  --sat_out_model                         small
% 7.62/1.49  --sat_out_clauses                       false
% 7.62/1.49  
% 7.62/1.49  ------ QBF Options
% 7.62/1.49  
% 7.62/1.49  --qbf_mode                              false
% 7.62/1.49  --qbf_elim_univ                         false
% 7.62/1.49  --qbf_dom_inst                          none
% 7.62/1.49  --qbf_dom_pre_inst                      false
% 7.62/1.49  --qbf_sk_in                             false
% 7.62/1.49  --qbf_pred_elim                         true
% 7.62/1.49  --qbf_split                             512
% 7.62/1.49  
% 7.62/1.49  ------ BMC1 Options
% 7.62/1.49  
% 7.62/1.49  --bmc1_incremental                      false
% 7.62/1.49  --bmc1_axioms                           reachable_all
% 7.62/1.49  --bmc1_min_bound                        0
% 7.62/1.49  --bmc1_max_bound                        -1
% 7.62/1.49  --bmc1_max_bound_default                -1
% 7.62/1.49  --bmc1_symbol_reachability              true
% 7.62/1.49  --bmc1_property_lemmas                  false
% 7.62/1.49  --bmc1_k_induction                      false
% 7.62/1.49  --bmc1_non_equiv_states                 false
% 7.62/1.49  --bmc1_deadlock                         false
% 7.62/1.49  --bmc1_ucm                              false
% 7.62/1.49  --bmc1_add_unsat_core                   none
% 7.62/1.49  --bmc1_unsat_core_children              false
% 7.62/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.49  --bmc1_out_stat                         full
% 7.62/1.49  --bmc1_ground_init                      false
% 7.62/1.49  --bmc1_pre_inst_next_state              false
% 7.62/1.49  --bmc1_pre_inst_state                   false
% 7.62/1.49  --bmc1_pre_inst_reach_state             false
% 7.62/1.49  --bmc1_out_unsat_core                   false
% 7.62/1.49  --bmc1_aig_witness_out                  false
% 7.62/1.49  --bmc1_verbose                          false
% 7.62/1.49  --bmc1_dump_clauses_tptp                false
% 7.62/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.49  --bmc1_dump_file                        -
% 7.62/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.49  --bmc1_ucm_extend_mode                  1
% 7.62/1.49  --bmc1_ucm_init_mode                    2
% 7.62/1.49  --bmc1_ucm_cone_mode                    none
% 7.62/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.49  --bmc1_ucm_relax_model                  4
% 7.62/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.49  --bmc1_ucm_layered_model                none
% 7.62/1.49  --bmc1_ucm_max_lemma_size               10
% 7.62/1.49  
% 7.62/1.49  ------ AIG Options
% 7.62/1.49  
% 7.62/1.49  --aig_mode                              false
% 7.62/1.49  
% 7.62/1.49  ------ Instantiation Options
% 7.62/1.49  
% 7.62/1.49  --instantiation_flag                    true
% 7.62/1.49  --inst_sos_flag                         false
% 7.62/1.49  --inst_sos_phase                        true
% 7.62/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel_side                     num_symb
% 7.62/1.49  --inst_solver_per_active                1400
% 7.62/1.49  --inst_solver_calls_frac                1.
% 7.62/1.49  --inst_passive_queue_type               priority_queues
% 7.62/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.49  --inst_passive_queues_freq              [25;2]
% 7.62/1.49  --inst_dismatching                      true
% 7.62/1.49  --inst_eager_unprocessed_to_passive     true
% 7.62/1.49  --inst_prop_sim_given                   true
% 7.62/1.49  --inst_prop_sim_new                     false
% 7.62/1.49  --inst_subs_new                         false
% 7.62/1.49  --inst_eq_res_simp                      false
% 7.62/1.49  --inst_subs_given                       false
% 7.62/1.49  --inst_orphan_elimination               true
% 7.62/1.49  --inst_learning_loop_flag               true
% 7.62/1.49  --inst_learning_start                   3000
% 7.62/1.49  --inst_learning_factor                  2
% 7.62/1.49  --inst_start_prop_sim_after_learn       3
% 7.62/1.49  --inst_sel_renew                        solver
% 7.62/1.49  --inst_lit_activity_flag                true
% 7.62/1.49  --inst_restr_to_given                   false
% 7.62/1.49  --inst_activity_threshold               500
% 7.62/1.49  --inst_out_proof                        true
% 7.62/1.49  
% 7.62/1.49  ------ Resolution Options
% 7.62/1.49  
% 7.62/1.49  --resolution_flag                       true
% 7.62/1.49  --res_lit_sel                           adaptive
% 7.62/1.49  --res_lit_sel_side                      none
% 7.62/1.49  --res_ordering                          kbo
% 7.62/1.49  --res_to_prop_solver                    active
% 7.62/1.49  --res_prop_simpl_new                    false
% 7.62/1.49  --res_prop_simpl_given                  true
% 7.62/1.49  --res_passive_queue_type                priority_queues
% 7.62/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.49  --res_passive_queues_freq               [15;5]
% 7.62/1.49  --res_forward_subs                      full
% 7.62/1.49  --res_backward_subs                     full
% 7.62/1.49  --res_forward_subs_resolution           true
% 7.62/1.49  --res_backward_subs_resolution          true
% 7.62/1.49  --res_orphan_elimination                true
% 7.62/1.49  --res_time_limit                        2.
% 7.62/1.49  --res_out_proof                         true
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Options
% 7.62/1.49  
% 7.62/1.49  --superposition_flag                    true
% 7.62/1.49  --sup_passive_queue_type                priority_queues
% 7.62/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.49  --demod_completeness_check              fast
% 7.62/1.49  --demod_use_ground                      true
% 7.62/1.49  --sup_to_prop_solver                    passive
% 7.62/1.49  --sup_prop_simpl_new                    true
% 7.62/1.49  --sup_prop_simpl_given                  true
% 7.62/1.49  --sup_fun_splitting                     false
% 7.62/1.49  --sup_smt_interval                      50000
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Simplification Setup
% 7.62/1.49  
% 7.62/1.49  --sup_indices_passive                   []
% 7.62/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_full_bw                           [BwDemod]
% 7.62/1.49  --sup_immed_triv                        [TrivRules]
% 7.62/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_immed_bw_main                     []
% 7.62/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  
% 7.62/1.49  ------ Combination Options
% 7.62/1.49  
% 7.62/1.49  --comb_res_mult                         3
% 7.62/1.49  --comb_sup_mult                         2
% 7.62/1.49  --comb_inst_mult                        10
% 7.62/1.49  
% 7.62/1.49  ------ Debug Options
% 7.62/1.49  
% 7.62/1.49  --dbg_backtrace                         false
% 7.62/1.49  --dbg_dump_prop_clauses                 false
% 7.62/1.49  --dbg_dump_prop_clauses_file            -
% 7.62/1.49  --dbg_out_stat                          false
% 7.62/1.49  ------ Parsing...
% 7.62/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  ------ Proving...
% 7.62/1.49  ------ Problem Properties 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  clauses                                 47
% 7.62/1.49  conjectures                             1
% 7.62/1.49  EPR                                     5
% 7.62/1.49  Horn                                    37
% 7.62/1.49  unary                                   7
% 7.62/1.49  binary                                  9
% 7.62/1.49  lits                                    132
% 7.62/1.49  lits eq                                 19
% 7.62/1.49  fd_pure                                 0
% 7.62/1.49  fd_pseudo                               0
% 7.62/1.49  fd_cond                                 1
% 7.62/1.49  fd_pseudo_cond                          2
% 7.62/1.49  AC symbols                              0
% 7.62/1.49  
% 7.62/1.49  ------ Schedule dynamic 5 is on 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  Current options:
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  ------ Input Options
% 7.62/1.49  
% 7.62/1.49  --out_options                           all
% 7.62/1.49  --tptp_safe_out                         true
% 7.62/1.49  --problem_path                          ""
% 7.62/1.49  --include_path                          ""
% 7.62/1.49  --clausifier                            res/vclausify_rel
% 7.62/1.49  --clausifier_options                    --mode clausify
% 7.62/1.49  --stdin                                 false
% 7.62/1.49  --stats_out                             all
% 7.62/1.49  
% 7.62/1.49  ------ General Options
% 7.62/1.49  
% 7.62/1.49  --fof                                   false
% 7.62/1.49  --time_out_real                         305.
% 7.62/1.49  --time_out_virtual                      -1.
% 7.62/1.49  --symbol_type_check                     false
% 7.62/1.49  --clausify_out                          false
% 7.62/1.49  --sig_cnt_out                           false
% 7.62/1.49  --trig_cnt_out                          false
% 7.62/1.49  --trig_cnt_out_tolerance                1.
% 7.62/1.49  --trig_cnt_out_sk_spl                   false
% 7.62/1.49  --abstr_cl_out                          false
% 7.62/1.49  
% 7.62/1.49  ------ Global Options
% 7.62/1.49  
% 7.62/1.49  --schedule                              default
% 7.62/1.49  --add_important_lit                     false
% 7.62/1.49  --prop_solver_per_cl                    1000
% 7.62/1.49  --min_unsat_core                        false
% 7.62/1.49  --soft_assumptions                      false
% 7.62/1.49  --soft_lemma_size                       3
% 7.62/1.49  --prop_impl_unit_size                   0
% 7.62/1.49  --prop_impl_unit                        []
% 7.62/1.49  --share_sel_clauses                     true
% 7.62/1.49  --reset_solvers                         false
% 7.62/1.49  --bc_imp_inh                            [conj_cone]
% 7.62/1.49  --conj_cone_tolerance                   3.
% 7.62/1.49  --extra_neg_conj                        none
% 7.62/1.49  --large_theory_mode                     true
% 7.62/1.49  --prolific_symb_bound                   200
% 7.62/1.49  --lt_threshold                          2000
% 7.62/1.49  --clause_weak_htbl                      true
% 7.62/1.49  --gc_record_bc_elim                     false
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing Options
% 7.62/1.49  
% 7.62/1.49  --preprocessing_flag                    true
% 7.62/1.49  --time_out_prep_mult                    0.1
% 7.62/1.49  --splitting_mode                        input
% 7.62/1.49  --splitting_grd                         true
% 7.62/1.49  --splitting_cvd                         false
% 7.62/1.49  --splitting_cvd_svl                     false
% 7.62/1.49  --splitting_nvd                         32
% 7.62/1.49  --sub_typing                            true
% 7.62/1.49  --prep_gs_sim                           true
% 7.62/1.49  --prep_unflatten                        true
% 7.62/1.49  --prep_res_sim                          true
% 7.62/1.49  --prep_upred                            true
% 7.62/1.49  --prep_sem_filter                       exhaustive
% 7.62/1.49  --prep_sem_filter_out                   false
% 7.62/1.49  --pred_elim                             true
% 7.62/1.49  --res_sim_input                         true
% 7.62/1.49  --eq_ax_congr_red                       true
% 7.62/1.49  --pure_diseq_elim                       true
% 7.62/1.49  --brand_transform                       false
% 7.62/1.49  --non_eq_to_eq                          false
% 7.62/1.49  --prep_def_merge                        true
% 7.62/1.49  --prep_def_merge_prop_impl              false
% 7.62/1.49  --prep_def_merge_mbd                    true
% 7.62/1.49  --prep_def_merge_tr_red                 false
% 7.62/1.49  --prep_def_merge_tr_cl                  false
% 7.62/1.49  --smt_preprocessing                     true
% 7.62/1.49  --smt_ac_axioms                         fast
% 7.62/1.49  --preprocessed_out                      false
% 7.62/1.49  --preprocessed_stats                    false
% 7.62/1.49  
% 7.62/1.49  ------ Abstraction refinement Options
% 7.62/1.49  
% 7.62/1.49  --abstr_ref                             []
% 7.62/1.49  --abstr_ref_prep                        false
% 7.62/1.49  --abstr_ref_until_sat                   false
% 7.62/1.49  --abstr_ref_sig_restrict                funpre
% 7.62/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.62/1.49  --abstr_ref_under                       []
% 7.62/1.49  
% 7.62/1.49  ------ SAT Options
% 7.62/1.49  
% 7.62/1.49  --sat_mode                              false
% 7.62/1.49  --sat_fm_restart_options                ""
% 7.62/1.49  --sat_gr_def                            false
% 7.62/1.49  --sat_epr_types                         true
% 7.62/1.49  --sat_non_cyclic_types                  false
% 7.62/1.49  --sat_finite_models                     false
% 7.62/1.49  --sat_fm_lemmas                         false
% 7.62/1.49  --sat_fm_prep                           false
% 7.62/1.49  --sat_fm_uc_incr                        true
% 7.62/1.49  --sat_out_model                         small
% 7.62/1.49  --sat_out_clauses                       false
% 7.62/1.49  
% 7.62/1.49  ------ QBF Options
% 7.62/1.49  
% 7.62/1.49  --qbf_mode                              false
% 7.62/1.49  --qbf_elim_univ                         false
% 7.62/1.49  --qbf_dom_inst                          none
% 7.62/1.49  --qbf_dom_pre_inst                      false
% 7.62/1.49  --qbf_sk_in                             false
% 7.62/1.49  --qbf_pred_elim                         true
% 7.62/1.49  --qbf_split                             512
% 7.62/1.49  
% 7.62/1.49  ------ BMC1 Options
% 7.62/1.49  
% 7.62/1.49  --bmc1_incremental                      false
% 7.62/1.49  --bmc1_axioms                           reachable_all
% 7.62/1.49  --bmc1_min_bound                        0
% 7.62/1.49  --bmc1_max_bound                        -1
% 7.62/1.49  --bmc1_max_bound_default                -1
% 7.62/1.49  --bmc1_symbol_reachability              true
% 7.62/1.49  --bmc1_property_lemmas                  false
% 7.62/1.49  --bmc1_k_induction                      false
% 7.62/1.49  --bmc1_non_equiv_states                 false
% 7.62/1.49  --bmc1_deadlock                         false
% 7.62/1.49  --bmc1_ucm                              false
% 7.62/1.49  --bmc1_add_unsat_core                   none
% 7.62/1.49  --bmc1_unsat_core_children              false
% 7.62/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.62/1.49  --bmc1_out_stat                         full
% 7.62/1.49  --bmc1_ground_init                      false
% 7.62/1.49  --bmc1_pre_inst_next_state              false
% 7.62/1.49  --bmc1_pre_inst_state                   false
% 7.62/1.49  --bmc1_pre_inst_reach_state             false
% 7.62/1.49  --bmc1_out_unsat_core                   false
% 7.62/1.49  --bmc1_aig_witness_out                  false
% 7.62/1.49  --bmc1_verbose                          false
% 7.62/1.49  --bmc1_dump_clauses_tptp                false
% 7.62/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.62/1.49  --bmc1_dump_file                        -
% 7.62/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.62/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.62/1.49  --bmc1_ucm_extend_mode                  1
% 7.62/1.49  --bmc1_ucm_init_mode                    2
% 7.62/1.49  --bmc1_ucm_cone_mode                    none
% 7.62/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.62/1.49  --bmc1_ucm_relax_model                  4
% 7.62/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.62/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.62/1.49  --bmc1_ucm_layered_model                none
% 7.62/1.49  --bmc1_ucm_max_lemma_size               10
% 7.62/1.49  
% 7.62/1.49  ------ AIG Options
% 7.62/1.49  
% 7.62/1.49  --aig_mode                              false
% 7.62/1.49  
% 7.62/1.49  ------ Instantiation Options
% 7.62/1.49  
% 7.62/1.49  --instantiation_flag                    true
% 7.62/1.49  --inst_sos_flag                         false
% 7.62/1.49  --inst_sos_phase                        true
% 7.62/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.62/1.49  --inst_lit_sel_side                     none
% 7.62/1.49  --inst_solver_per_active                1400
% 7.62/1.49  --inst_solver_calls_frac                1.
% 7.62/1.49  --inst_passive_queue_type               priority_queues
% 7.62/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.62/1.49  --inst_passive_queues_freq              [25;2]
% 7.62/1.49  --inst_dismatching                      true
% 7.62/1.49  --inst_eager_unprocessed_to_passive     true
% 7.62/1.49  --inst_prop_sim_given                   true
% 7.62/1.49  --inst_prop_sim_new                     false
% 7.62/1.49  --inst_subs_new                         false
% 7.62/1.49  --inst_eq_res_simp                      false
% 7.62/1.49  --inst_subs_given                       false
% 7.62/1.49  --inst_orphan_elimination               true
% 7.62/1.49  --inst_learning_loop_flag               true
% 7.62/1.49  --inst_learning_start                   3000
% 7.62/1.49  --inst_learning_factor                  2
% 7.62/1.49  --inst_start_prop_sim_after_learn       3
% 7.62/1.49  --inst_sel_renew                        solver
% 7.62/1.49  --inst_lit_activity_flag                true
% 7.62/1.49  --inst_restr_to_given                   false
% 7.62/1.49  --inst_activity_threshold               500
% 7.62/1.49  --inst_out_proof                        true
% 7.62/1.49  
% 7.62/1.49  ------ Resolution Options
% 7.62/1.49  
% 7.62/1.49  --resolution_flag                       false
% 7.62/1.49  --res_lit_sel                           adaptive
% 7.62/1.49  --res_lit_sel_side                      none
% 7.62/1.49  --res_ordering                          kbo
% 7.62/1.49  --res_to_prop_solver                    active
% 7.62/1.49  --res_prop_simpl_new                    false
% 7.62/1.49  --res_prop_simpl_given                  true
% 7.62/1.49  --res_passive_queue_type                priority_queues
% 7.62/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.62/1.49  --res_passive_queues_freq               [15;5]
% 7.62/1.49  --res_forward_subs                      full
% 7.62/1.49  --res_backward_subs                     full
% 7.62/1.49  --res_forward_subs_resolution           true
% 7.62/1.49  --res_backward_subs_resolution          true
% 7.62/1.49  --res_orphan_elimination                true
% 7.62/1.49  --res_time_limit                        2.
% 7.62/1.49  --res_out_proof                         true
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Options
% 7.62/1.49  
% 7.62/1.49  --superposition_flag                    true
% 7.62/1.49  --sup_passive_queue_type                priority_queues
% 7.62/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.62/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.62/1.49  --demod_completeness_check              fast
% 7.62/1.49  --demod_use_ground                      true
% 7.62/1.49  --sup_to_prop_solver                    passive
% 7.62/1.49  --sup_prop_simpl_new                    true
% 7.62/1.49  --sup_prop_simpl_given                  true
% 7.62/1.49  --sup_fun_splitting                     false
% 7.62/1.49  --sup_smt_interval                      50000
% 7.62/1.49  
% 7.62/1.49  ------ Superposition Simplification Setup
% 7.62/1.49  
% 7.62/1.49  --sup_indices_passive                   []
% 7.62/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.62/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.62/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_full_bw                           [BwDemod]
% 7.62/1.49  --sup_immed_triv                        [TrivRules]
% 7.62/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.62/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_immed_bw_main                     []
% 7.62/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.62/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.62/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.62/1.49  
% 7.62/1.49  ------ Combination Options
% 7.62/1.49  
% 7.62/1.49  --comb_res_mult                         3
% 7.62/1.49  --comb_sup_mult                         2
% 7.62/1.49  --comb_inst_mult                        10
% 7.62/1.49  
% 7.62/1.49  ------ Debug Options
% 7.62/1.49  
% 7.62/1.49  --dbg_backtrace                         false
% 7.62/1.49  --dbg_dump_prop_clauses                 false
% 7.62/1.49  --dbg_dump_prop_clauses_file            -
% 7.62/1.49  --dbg_out_stat                          false
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS status Theorem for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  fof(f20,conjecture,(
% 7.62/1.49    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f21,negated_conjecture,(
% 7.62/1.49    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.62/1.49    inference(negated_conjecture,[],[f20])).
% 7.62/1.49  
% 7.62/1.49  fof(f43,plain,(
% 7.62/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 7.62/1.49    inference(ennf_transformation,[],[f21])).
% 7.62/1.49  
% 7.62/1.49  fof(f72,plain,(
% 7.62/1.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) | ~v1_funct_2(sK12,sK10,sK11) | ~v1_funct_1(sK12)) & r2_hidden(sK12,k1_funct_2(sK10,sK11)))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f73,plain,(
% 7.62/1.49    (~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) | ~v1_funct_2(sK12,sK10,sK11) | ~v1_funct_1(sK12)) & r2_hidden(sK12,k1_funct_2(sK10,sK11))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f43,f72])).
% 7.62/1.49  
% 7.62/1.49  fof(f125,plain,(
% 7.62/1.49    r2_hidden(sK12,k1_funct_2(sK10,sK11))),
% 7.62/1.49    inference(cnf_transformation,[],[f73])).
% 7.62/1.49  
% 7.62/1.49  fof(f17,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f44,plain,(
% 7.62/1.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 7.62/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.62/1.49  
% 7.62/1.49  fof(f45,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 7.62/1.49    inference(definition_folding,[],[f17,f44])).
% 7.62/1.49  
% 7.62/1.49  fof(f69,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2))),
% 7.62/1.49    inference(nnf_transformation,[],[f45])).
% 7.62/1.49  
% 7.62/1.49  fof(f114,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_funct_2(X0,X1) != X2) )),
% 7.62/1.49    inference(cnf_transformation,[],[f69])).
% 7.62/1.49  
% 7.62/1.49  fof(f134,plain,(
% 7.62/1.49    ( ! [X0,X1] : (sP0(X1,X0,k1_funct_2(X0,X1))) )),
% 7.62/1.49    inference(equality_resolution,[],[f114])).
% 7.62/1.49  
% 7.62/1.49  fof(f63,plain,(
% 7.62/1.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 7.62/1.49    inference(nnf_transformation,[],[f44])).
% 7.62/1.49  
% 7.62/1.49  fof(f64,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.62/1.49    inference(rectify,[],[f63])).
% 7.62/1.49  
% 7.62/1.49  fof(f67,plain,(
% 7.62/1.49    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X0) & k1_relat_1(X8) = X1 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) & k1_relat_1(sK8(X0,X1,X6)) = X1 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f66,plain,(
% 7.62/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK7(X0,X1,X2) = X3 & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))))) )),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f65,plain,(
% 7.62/1.49    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X0) & k1_relat_1(X5) = X1 & sK6(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f68,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X0) | k1_relat_1(X4) != X1 | sK6(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X2)),X0) & k1_relat_1(sK7(X0,X1,X2)) = X1 & sK6(X0,X1,X2) = sK7(X0,X1,X2) & v1_funct_1(sK7(X0,X1,X2)) & v1_relat_1(sK7(X0,X1,X2))) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X0) | k1_relat_1(X7) != X1 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) & k1_relat_1(sK8(X0,X1,X6)) = X1 & sK8(X0,X1,X6) = X6 & v1_funct_1(sK8(X0,X1,X6)) & v1_relat_1(sK8(X0,X1,X6))) | ~r2_hidden(X6,X2))) | ~sP0(X0,X1,X2)))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f64,f67,f66,f65])).
% 7.62/1.49  
% 7.62/1.49  fof(f104,plain,(
% 7.62/1.49    ( ! [X6,X2,X0,X1] : (sK8(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f68])).
% 7.62/1.49  
% 7.62/1.49  fof(f106,plain,(
% 7.62/1.49    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK8(X0,X1,X6)),X0) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f68])).
% 7.62/1.49  
% 7.62/1.49  fof(f5,axiom,(
% 7.62/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f56,plain,(
% 7.62/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.62/1.49    inference(nnf_transformation,[],[f5])).
% 7.62/1.49  
% 7.62/1.49  fof(f57,plain,(
% 7.62/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.62/1.49    inference(flattening,[],[f56])).
% 7.62/1.49  
% 7.62/1.49  fof(f84,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.62/1.49    inference(cnf_transformation,[],[f57])).
% 7.62/1.49  
% 7.62/1.49  fof(f130,plain,(
% 7.62/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.62/1.49    inference(equality_resolution,[],[f84])).
% 7.62/1.49  
% 7.62/1.49  fof(f10,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f22,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.62/1.49    inference(pure_predicate_removal,[],[f10])).
% 7.62/1.49  
% 7.62/1.49  fof(f27,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f22])).
% 7.62/1.49  
% 7.62/1.49  fof(f91,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f27])).
% 7.62/1.49  
% 7.62/1.49  fof(f8,axiom,(
% 7.62/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f24,plain,(
% 7.62/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.62/1.49    inference(ennf_transformation,[],[f8])).
% 7.62/1.49  
% 7.62/1.49  fof(f25,plain,(
% 7.62/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.62/1.49    inference(flattening,[],[f24])).
% 7.62/1.49  
% 7.62/1.49  fof(f89,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f25])).
% 7.62/1.49  
% 7.62/1.49  fof(f9,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f26,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f9])).
% 7.62/1.49  
% 7.62/1.49  fof(f90,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f26])).
% 7.62/1.49  
% 7.62/1.49  fof(f105,plain,(
% 7.62/1.49    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK8(X0,X1,X6)) = X1 | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f68])).
% 7.62/1.49  
% 7.62/1.49  fof(f19,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f41,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.62/1.49    inference(ennf_transformation,[],[f19])).
% 7.62/1.49  
% 7.62/1.49  fof(f42,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.62/1.49    inference(flattening,[],[f41])).
% 7.62/1.49  
% 7.62/1.49  fof(f70,plain,(
% 7.62/1.49    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) & r2_hidden(sK9(X0,X1,X2),X0)))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f71,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f70])).
% 7.62/1.49  
% 7.62/1.49  fof(f124,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f71])).
% 7.62/1.49  
% 7.62/1.49  fof(f135,plain,(
% 7.62/1.49    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(equality_resolution,[],[f124])).
% 7.62/1.49  
% 7.62/1.49  fof(f102,plain,(
% 7.62/1.49    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f68])).
% 7.62/1.49  
% 7.62/1.49  fof(f103,plain,(
% 7.62/1.49    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK8(X0,X1,X6)) | ~r2_hidden(X6,X2) | ~sP0(X0,X1,X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f68])).
% 7.62/1.49  
% 7.62/1.49  fof(f123,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK9(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f71])).
% 7.62/1.49  
% 7.62/1.49  fof(f136,plain,(
% 7.62/1.49    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(equality_resolution,[],[f123])).
% 7.62/1.49  
% 7.62/1.49  fof(f16,axiom,(
% 7.62/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f37,plain,(
% 7.62/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.62/1.49    inference(ennf_transformation,[],[f16])).
% 7.62/1.49  
% 7.62/1.49  fof(f38,plain,(
% 7.62/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.62/1.49    inference(flattening,[],[f37])).
% 7.62/1.49  
% 7.62/1.49  fof(f101,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f38])).
% 7.62/1.49  
% 7.62/1.49  fof(f122,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f71])).
% 7.62/1.49  
% 7.62/1.49  fof(f137,plain,(
% 7.62/1.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(equality_resolution,[],[f122])).
% 7.62/1.49  
% 7.62/1.49  fof(f1,axiom,(
% 7.62/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f46,plain,(
% 7.62/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.62/1.49    inference(nnf_transformation,[],[f1])).
% 7.62/1.49  
% 7.62/1.49  fof(f47,plain,(
% 7.62/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.62/1.49    inference(rectify,[],[f46])).
% 7.62/1.49  
% 7.62/1.49  fof(f48,plain,(
% 7.62/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f49,plain,(
% 7.62/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 7.62/1.49  
% 7.62/1.49  fof(f74,plain,(
% 7.62/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f49])).
% 7.62/1.49  
% 7.62/1.49  fof(f15,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f35,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(ennf_transformation,[],[f15])).
% 7.62/1.49  
% 7.62/1.49  fof(f36,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.62/1.49    inference(flattening,[],[f35])).
% 7.62/1.49  
% 7.62/1.49  fof(f99,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f36])).
% 7.62/1.49  
% 7.62/1.49  fof(f126,plain,(
% 7.62/1.49    ~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) | ~v1_funct_2(sK12,sK10,sK11) | ~v1_funct_1(sK12)),
% 7.62/1.49    inference(cnf_transformation,[],[f73])).
% 7.62/1.49  
% 7.62/1.49  fof(f3,axiom,(
% 7.62/1.49    v1_xboole_0(k1_xboole_0)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f79,plain,(
% 7.62/1.49    v1_xboole_0(k1_xboole_0)),
% 7.62/1.49    inference(cnf_transformation,[],[f3])).
% 7.62/1.49  
% 7.62/1.49  fof(f75,plain,(
% 7.62/1.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f49])).
% 7.62/1.49  
% 7.62/1.49  fof(f121,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK9(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f71])).
% 7.62/1.49  
% 7.62/1.49  fof(f138,plain,(
% 7.62/1.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(equality_resolution,[],[f121])).
% 7.62/1.49  
% 7.62/1.49  fof(f4,axiom,(
% 7.62/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f54,plain,(
% 7.62/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.62/1.49    inference(nnf_transformation,[],[f4])).
% 7.62/1.49  
% 7.62/1.49  fof(f55,plain,(
% 7.62/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.62/1.49    inference(flattening,[],[f54])).
% 7.62/1.49  
% 7.62/1.49  fof(f80,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.62/1.49    inference(cnf_transformation,[],[f55])).
% 7.62/1.49  
% 7.62/1.49  fof(f128,plain,(
% 7.62/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.62/1.49    inference(equality_resolution,[],[f80])).
% 7.62/1.49  
% 7.62/1.49  fof(f2,axiom,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f23,plain,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.62/1.49    inference(ennf_transformation,[],[f2])).
% 7.62/1.49  
% 7.62/1.49  fof(f50,plain,(
% 7.62/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.62/1.49    inference(nnf_transformation,[],[f23])).
% 7.62/1.49  
% 7.62/1.49  fof(f51,plain,(
% 7.62/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.62/1.49    inference(rectify,[],[f50])).
% 7.62/1.49  
% 7.62/1.49  fof(f52,plain,(
% 7.62/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f53,plain,(
% 7.62/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f51,f52])).
% 7.62/1.49  
% 7.62/1.49  fof(f77,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f53])).
% 7.62/1.49  
% 7.62/1.49  fof(f85,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.62/1.49    inference(cnf_transformation,[],[f57])).
% 7.62/1.49  
% 7.62/1.49  fof(f129,plain,(
% 7.62/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.62/1.49    inference(equality_resolution,[],[f85])).
% 7.62/1.49  
% 7.62/1.49  fof(f12,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f29,plain,(
% 7.62/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.62/1.49    inference(ennf_transformation,[],[f12])).
% 7.62/1.49  
% 7.62/1.49  fof(f30,plain,(
% 7.62/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.62/1.49    inference(flattening,[],[f29])).
% 7.62/1.49  
% 7.62/1.49  fof(f93,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f30])).
% 7.62/1.49  
% 7.62/1.49  fof(f18,axiom,(
% 7.62/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f39,plain,(
% 7.62/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.62/1.49    inference(ennf_transformation,[],[f18])).
% 7.62/1.49  
% 7.62/1.49  fof(f40,plain,(
% 7.62/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.62/1.49    inference(flattening,[],[f39])).
% 7.62/1.49  
% 7.62/1.49  fof(f117,plain,(
% 7.62/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f40])).
% 7.62/1.49  
% 7.62/1.49  fof(f118,plain,(
% 7.62/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f40])).
% 7.62/1.49  
% 7.62/1.49  cnf(c_52,negated_conjecture,
% 7.62/1.49      ( r2_hidden(sK12,k1_funct_2(sK10,sK11)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6469,plain,
% 7.62/1.49      ( r2_hidden(sK12,k1_funct_2(sK10,sK11)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_41,plain,
% 7.62/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f134]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6473,plain,
% 7.62/1.49      ( sP0(X0,X1,k1_funct_2(X1,X0)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_37,plain,
% 7.62/1.49      ( ~ sP0(X0,X1,X2) | ~ r2_hidden(X3,X2) | sK8(X0,X1,X3) = X3 ),
% 7.62/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6477,plain,
% 7.62/1.49      ( sK8(X0,X1,X2) = X2
% 7.62/1.49      | sP0(X0,X1,X3) != iProver_top
% 7.62/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9198,plain,
% 7.62/1.49      ( sK8(X0,X1,X2) = X2
% 7.62/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6473,c_6477]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9537,plain,
% 7.62/1.49      ( sK8(sK11,sK10,sK12) = sK12 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6469,c_9198]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_35,plain,
% 7.62/1.49      ( ~ sP0(X0,X1,X2)
% 7.62/1.49      | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0)
% 7.62/1.49      | ~ r2_hidden(X3,X2) ),
% 7.62/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6479,plain,
% 7.62/1.49      ( sP0(X0,X1,X2) != iProver_top
% 7.62/1.49      | r1_tarski(k2_relat_1(sK8(X0,X1,X3)),X0) = iProver_top
% 7.62/1.49      | r2_hidden(X3,X2) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11288,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK8(X0,X1,X2)),X0) = iProver_top
% 7.62/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6473,c_6479]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_30897,plain,
% 7.62/1.49      ( r1_tarski(k2_relat_1(sK12),sK11) = iProver_top
% 7.62/1.49      | r2_hidden(sK12,k1_funct_2(sK10,sK11)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_9537,c_11288]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10,plain,
% 7.62/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f130]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_17,plain,
% 7.62/1.49      ( v5_relat_1(X0,X1)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.62/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15,plain,
% 7.62/1.49      ( ~ v5_relat_1(X0,X1)
% 7.62/1.49      | ~ r2_hidden(X2,k1_relat_1(X0))
% 7.62/1.49      | r2_hidden(k1_funct_1(X0,X2),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_611,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.62/1.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(resolution,[status(thm)],[c_17,c_15]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | v1_relat_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_615,plain,
% 7.62/1.49      ( r2_hidden(k1_funct_1(X0,X3),X2)
% 7.62/1.49      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_611,c_16]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_616,plain,
% 7.62/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ r2_hidden(X3,k1_relat_1(X0))
% 7.62/1.49      | r2_hidden(k1_funct_1(X0,X3),X2)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_615]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6468,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.62/1.49      | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(X0,X3),X2) = iProver_top
% 7.62/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_7658,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(X0,X1),X2) = iProver_top
% 7.62/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10,c_6468]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_36,plain,
% 7.62/1.49      ( ~ sP0(X0,X1,X2)
% 7.62/1.49      | ~ r2_hidden(X3,X2)
% 7.62/1.49      | k1_relat_1(sK8(X0,X1,X3)) = X1 ),
% 7.62/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6478,plain,
% 7.62/1.49      ( k1_relat_1(sK8(X0,X1,X2)) = X1
% 7.62/1.49      | sP0(X0,X1,X3) != iProver_top
% 7.62/1.49      | r2_hidden(X2,X3) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10028,plain,
% 7.62/1.49      ( k1_relat_1(sK8(X0,X1,X2)) = X1
% 7.62/1.49      | r2_hidden(X2,k1_funct_2(X1,X0)) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6473,c_6478]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10861,plain,
% 7.62/1.49      ( k1_relat_1(sK8(sK11,sK10,sK12)) = sK10 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6469,c_10028]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10863,plain,
% 7.62/1.49      ( k1_relat_1(sK12) = sK10 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_10861,c_9537]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_45,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f135]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6471,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1) != iProver_top
% 7.62/1.49      | v1_relat_1(X0) != iProver_top
% 7.62/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10971,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK12),X0))) = iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top
% 7.62/1.49      | v1_relat_1(sK12) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10863,c_6471]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10987,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top
% 7.62/1.49      | v1_relat_1(sK12) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_10971,c_10863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_39,plain,
% 7.62/1.49      ( ~ sP0(X0,X1,X2)
% 7.62/1.49      | ~ r2_hidden(X3,X2)
% 7.62/1.49      | v1_relat_1(sK8(X0,X1,X3)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6475,plain,
% 7.62/1.49      ( sP0(X0,X1,X2) != iProver_top
% 7.62/1.49      | r2_hidden(X3,X2) != iProver_top
% 7.62/1.49      | v1_relat_1(sK8(X0,X1,X3)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9378,plain,
% 7.62/1.49      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 7.62/1.49      | v1_relat_1(sK8(X2,X1,X0)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6473,c_6475]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10433,plain,
% 7.62/1.49      ( v1_relat_1(sK8(sK11,sK10,sK12)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6469,c_9378]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10435,plain,
% 7.62/1.49      ( v1_relat_1(sK12) = iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_10433,c_9537]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_38,plain,
% 7.62/1.49      ( ~ sP0(X0,X1,X2)
% 7.62/1.49      | ~ r2_hidden(X3,X2)
% 7.62/1.49      | v1_funct_1(sK8(X0,X1,X3)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6476,plain,
% 7.62/1.49      ( sP0(X0,X1,X2) != iProver_top
% 7.62/1.49      | r2_hidden(X3,X2) != iProver_top
% 7.62/1.49      | v1_funct_1(sK8(X0,X1,X3)) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9925,plain,
% 7.62/1.49      ( r2_hidden(X0,k1_funct_2(X1,X2)) != iProver_top
% 7.62/1.49      | v1_funct_1(sK8(X2,X1,X0)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6473,c_6476]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10665,plain,
% 7.62/1.49      ( v1_funct_1(sK8(sK11,sK10,sK12)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6469,c_9925]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10667,plain,
% 7.62/1.49      ( v1_funct_1(sK12) = iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_10665,c_9537]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11961,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10987,c_10435,c_10667]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16075,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X0,sK12),k1_relat_1(sK12)) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_7658,c_11961]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16110,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X0,sK12),sK10) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_16075,c_10863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_46,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.62/1.49      | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f136]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6470,plain,
% 7.62/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 7.62/1.49      | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0)) = iProver_top
% 7.62/1.49      | v1_relat_1(X0) != iProver_top
% 7.62/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10972,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK12),X0))) = iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
% 7.62/1.49      | v1_relat_1(sK12) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10863,c_6470]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10978,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
% 7.62/1.49      | v1_relat_1(sK12) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_10972,c_10863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12045,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10978,c_10435,c_10667]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16827,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,X0))) = iProver_top
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_16110,c_10435,c_10667,c_10978]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16842,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_16827,c_6468]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16869,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(X0,sK10) != iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_16842,c_10863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_26,plain,
% 7.62/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.62/1.49      | v1_partfun1(X0,X1)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | v1_xboole_0(X2) ),
% 7.62/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_47,plain,
% 7.62/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f137]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_714,plain,
% 7.62/1.49      ( v1_partfun1(X0,X1)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(X3,sK9(k1_relat_1(X3),X4,X3)),X4)
% 7.62/1.49      | ~ v1_relat_1(X3)
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X3)
% 7.62/1.49      | v1_xboole_0(X2)
% 7.62/1.49      | X3 != X0
% 7.62/1.49      | X4 != X2
% 7.62/1.49      | k1_relat_1(X3) != X1 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_47]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_715,plain,
% 7.62/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | v1_xboole_0(X1) ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_714]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_717,plain,
% 7.62/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | v1_xboole_0(X1) ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_715,c_45]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1,plain,
% 7.62/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_731,plain,
% 7.62/1.49      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_717,c_1]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_24,plain,
% 7.62/1.49      ( v1_funct_2(X0,X1,X2)
% 7.62/1.49      | ~ v1_partfun1(X0,X1)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_51,negated_conjecture,
% 7.62/1.49      ( ~ v1_funct_2(sK12,sK10,sK11)
% 7.62/1.49      | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | ~ v1_funct_1(sK12) ),
% 7.62/1.49      inference(cnf_transformation,[],[f126]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_739,plain,
% 7.62/1.49      ( ~ v1_partfun1(X0,X1)
% 7.62/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.49      | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | sK11 != X2
% 7.62/1.49      | sK10 != X1
% 7.62/1.49      | sK12 != X0 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_51]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_740,plain,
% 7.62/1.49      ( ~ v1_partfun1(sK12,sK10)
% 7.62/1.49      | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | ~ v1_funct_1(sK12) ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_739]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_844,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(X0,sK9(k1_relat_1(X0),X1,X0)),X1)
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | k1_relat_1(X0) != sK10
% 7.62/1.49      | sK12 != X0 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_731,c_740]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_845,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0)
% 7.62/1.49      | ~ v1_relat_1(sK12)
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_844]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_859,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | ~ r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0)
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.49      inference(forward_subsumption_resolution,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_845,c_16]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5468,plain,
% 7.62/1.49      ( ~ r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0)
% 7.62/1.49      | ~ sP1_iProver_split ),
% 7.62/1.49      inference(splitting,
% 7.62/1.49                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 7.62/1.49                [c_859]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6465,plain,
% 7.62/1.49      ( r2_hidden(k1_funct_1(sK12,sK9(k1_relat_1(sK12),X0,sK12)),X0) != iProver_top
% 7.62/1.49      | sP1_iProver_split != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_5468]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10906,plain,
% 7.62/1.49      ( r2_hidden(k1_funct_1(sK12,sK9(sK10,X0,sK12)),X0) != iProver_top
% 7.62/1.49      | sP1_iProver_split != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_10863,c_6465]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16076,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X0,sK12),k1_relat_1(sK12)) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top
% 7.62/1.49      | sP1_iProver_split != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_7658,c_10906]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16101,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X0,sK12),sK10) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top
% 7.62/1.49      | sP1_iProver_split != iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_16076,c_10863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5,plain,
% 7.62/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_167,plain,
% 7.62/1.49      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_0,plain,
% 7.62/1.49      ( r2_hidden(sK1(X0),X0) | v1_xboole_0(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6504,plain,
% 7.62/1.49      ( r2_hidden(sK1(X0),X0) = iProver_top
% 7.62/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12058,plain,
% 7.62/1.49      ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_12045,c_6468]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12063,plain,
% 7.62/1.49      ( r2_hidden(X0,sK10) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_12058,c_10863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12183,plain,
% 7.62/1.49      ( r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
% 7.62/1.49      | r2_hidden(X0,sK10) != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_12063,c_10667]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12184,plain,
% 7.62/1.49      ( r2_hidden(X0,sK10) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
% 7.62/1.49      | r2_hidden(k1_funct_1(sK12,X0),X1) = iProver_top ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_12183]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6503,plain,
% 7.62/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.62/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12192,plain,
% 7.62/1.49      ( r2_hidden(X0,sK10) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,X1,sK12),sK10) = iProver_top
% 7.62/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_12184,c_6503]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14290,plain,
% 7.62/1.49      ( r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
% 7.62/1.49      | v1_xboole_0(X0) != iProver_top
% 7.62/1.49      | v1_xboole_0(sK10) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6504,c_12192]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14375,plain,
% 7.62/1.49      ( r2_hidden(sK9(sK10,k1_xboole_0,sK12),sK10) = iProver_top
% 7.62/1.49      | v1_xboole_0(sK10) = iProver_top
% 7.62/1.49      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_14290]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_48,plain,
% 7.62/1.49      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 7.62/1.49      | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f138]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_771,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.62/1.49      | ~ v1_relat_1(X0)
% 7.62/1.49      | ~ v1_funct_1(X0)
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | k1_relat_1(X0) != sK10
% 7.62/1.49      | sK11 != X1
% 7.62/1.49      | sK12 != X0 ),
% 7.62/1.49      inference(resolution_lifted,[status(thm)],[c_48,c_51]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_772,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | r2_hidden(sK9(k1_relat_1(sK12),sK11,sK12),k1_relat_1(sK12))
% 7.62/1.49      | ~ v1_relat_1(sK12)
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.49      inference(unflattening,[status(thm)],[c_771]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_784,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | r2_hidden(sK9(k1_relat_1(sK12),sK11,sK12),k1_relat_1(sK12))
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.49      inference(forward_subsumption_resolution,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_772,c_16]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6466,plain,
% 7.62/1.49      ( k1_relat_1(sK12) != sK10
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(k1_relat_1(sK12),sK11,sK12),k1_relat_1(sK12)) = iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10907,plain,
% 7.62/1.49      ( sK10 != sK10
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_10863,c_6466]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10916,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.49      inference(equality_resolution_simp,[status(thm)],[c_10907]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14647,plain,
% 7.62/1.49      ( r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10916,c_10667]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14648,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top ),
% 7.62/1.49      inference(renaming,[status(thm)],[c_14647]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14653,plain,
% 7.62/1.49      ( r2_hidden(sK9(sK10,sK11,sK12),sK10) = iProver_top ),
% 7.62/1.49      inference(forward_subsumption_resolution,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_14648,c_12045]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14655,plain,
% 7.62/1.49      ( v1_xboole_0(sK10) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_14653,c_6503]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16183,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | r2_hidden(sK9(sK10,k1_xboole_0,sK12),sK10) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top
% 7.62/1.49      | sP1_iProver_split != iProver_top ),
% 7.62/1.49      inference(instantiation,[status(thm)],[c_16101]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16682,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | sP1_iProver_split != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_16101,c_167,c_10667,c_14375,c_14655,c_16183]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5469,plain,
% 7.62/1.49      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.49      | ~ v1_funct_1(sK12)
% 7.62/1.49      | sP1_iProver_split
% 7.62/1.49      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.49      inference(splitting,
% 7.62/1.49                [splitting(split),new_symbols(definition,[])],
% 7.62/1.49                [c_859]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6464,plain,
% 7.62/1.49      ( k1_relat_1(sK12) != sK10
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top
% 7.62/1.49      | sP1_iProver_split = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_5469]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10904,plain,
% 7.62/1.49      ( sK10 != sK10
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top
% 7.62/1.49      | sP1_iProver_split = iProver_top ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_10863,c_6464]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10934,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top
% 7.62/1.49      | sP1_iProver_split = iProver_top ),
% 7.62/1.49      inference(equality_resolution_simp,[status(thm)],[c_10904]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5510,plain,
% 7.62/1.49      ( k1_relat_1(sK12) != sK10
% 7.62/1.49      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | v1_funct_1(sK12) != iProver_top
% 7.62/1.49      | sP1_iProver_split = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_5469]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_13908,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.49      | sP1_iProver_split = iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_10934,c_5510,c_10667,c_10863]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16845,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.62/1.49      | sP1_iProver_split = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_16827,c_13908]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16921,plain,
% 7.62/1.49      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.62/1.49      inference(global_propositional_subsumption,
% 7.62/1.49                [status(thm)],
% 7.62/1.49                [c_16869,c_16682,c_16845]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8,plain,
% 7.62/1.49      ( r1_tarski(X0,X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f128]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6497,plain,
% 7.62/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3,plain,
% 7.62/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6501,plain,
% 7.62/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.62/1.49      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_7730,plain,
% 7.62/1.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_6501,c_6503]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9,plain,
% 7.62/1.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.62/1.50      inference(cnf_transformation,[],[f129]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_19,plain,
% 7.62/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.62/1.50      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.62/1.50      | ~ v1_relat_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_6491,plain,
% 7.62/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.62/1.50      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.62/1.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.62/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14672,plain,
% 7.62/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.62/1.50      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 7.62/1.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.62/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_9,c_6491]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15237,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.62/1.50      | r1_tarski(k2_relat_1(sK12),k1_xboole_0) != iProver_top
% 7.62/1.50      | r1_tarski(sK10,X0) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_10863,c_14672]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15634,plain,
% 7.62/1.50      ( r1_tarski(sK10,X0) != iProver_top
% 7.62/1.50      | r1_tarski(k2_relat_1(sK12),k1_xboole_0) != iProver_top
% 7.62/1.50      | m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_15237,c_10435]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15635,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.62/1.50      | r1_tarski(k2_relat_1(sK12),k1_xboole_0) != iProver_top
% 7.62/1.50      | r1_tarski(sK10,X0) != iProver_top ),
% 7.62/1.50      inference(renaming,[status(thm)],[c_15634]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15643,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.62/1.50      | r1_tarski(sK10,X0) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_7730,c_15635]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15754,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_6497,c_15643]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_43,plain,
% 7.62/1.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_667,plain,
% 7.62/1.50      ( v1_partfun1(X0,X1)
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | ~ v1_relat_1(X3)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X3)
% 7.62/1.50      | v1_xboole_0(X2)
% 7.62/1.50      | X3 != X0
% 7.62/1.50      | k2_relat_1(X3) != X2
% 7.62/1.50      | k1_relat_1(X3) != X1 ),
% 7.62/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_43]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_668,plain,
% 7.62/1.50      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.62/1.50      inference(unflattening,[status(thm)],[c_667]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_42,plain,
% 7.62/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0) ),
% 7.62/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_672,plain,
% 7.62/1.50      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | v1_xboole_0(k2_relat_1(X0)) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_668,c_42]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_889,plain,
% 7.62/1.50      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(sK12)
% 7.62/1.50      | v1_xboole_0(k2_relat_1(X0))
% 7.62/1.50      | k1_relat_1(X0) != sK10
% 7.62/1.50      | sK12 != X0 ),
% 7.62/1.50      inference(resolution_lifted,[status(thm)],[c_672,c_740]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_890,plain,
% 7.62/1.50      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.50      | ~ v1_relat_1(sK12)
% 7.62/1.50      | ~ v1_funct_1(sK12)
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12))
% 7.62/1.50      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.50      inference(unflattening,[status(thm)],[c_889]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_902,plain,
% 7.62/1.50      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.50      | ~ v1_funct_1(sK12)
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12))
% 7.62/1.50      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.50      inference(forward_subsumption_resolution,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_890,c_16]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_6461,plain,
% 7.62/1.50      ( k1_relat_1(sK12) != sK10
% 7.62/1.50      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_10903,plain,
% 7.62/1.50      ( sK10 != sK10
% 7.62/1.50      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(demodulation,[status(thm)],[c_10863,c_6461]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_10941,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(equality_resolution_simp,[status(thm)],[c_10903]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_891,plain,
% 7.62/1.50      ( k1_relat_1(sK12) != sK10
% 7.62/1.50      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14268,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_10941,c_891,c_10435,c_10667,c_10863]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14682,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_6491,c_14268]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14707,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(sK10,sK10) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_14682,c_10863]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_691,plain,
% 7.62/1.50      ( v1_partfun1(X0,X1)
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.62/1.50      | r2_hidden(sK9(k1_relat_1(X3),X4,X3),k1_relat_1(X3))
% 7.62/1.50      | ~ v1_relat_1(X3)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X3)
% 7.62/1.50      | v1_xboole_0(X2)
% 7.62/1.50      | X3 != X0
% 7.62/1.50      | X4 != X2
% 7.62/1.50      | k1_relat_1(X3) != X1 ),
% 7.62/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_48]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_692,plain,
% 7.62/1.50      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.62/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 7.62/1.50      | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | v1_xboole_0(X1) ),
% 7.62/1.50      inference(unflattening,[status(thm)],[c_691]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_694,plain,
% 7.62/1.50      ( v1_partfun1(X0,k1_relat_1(X0))
% 7.62/1.50      | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | v1_xboole_0(X1) ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_692,c_46]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_867,plain,
% 7.62/1.50      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.50      | r2_hidden(sK9(k1_relat_1(X0),X1,X0),k1_relat_1(X0))
% 7.62/1.50      | ~ v1_relat_1(X0)
% 7.62/1.50      | ~ v1_funct_1(X0)
% 7.62/1.50      | ~ v1_funct_1(sK12)
% 7.62/1.50      | v1_xboole_0(X1)
% 7.62/1.50      | k1_relat_1(X0) != sK10
% 7.62/1.50      | sK12 != X0 ),
% 7.62/1.50      inference(resolution_lifted,[status(thm)],[c_694,c_740]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_868,plain,
% 7.62/1.50      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.50      | r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12))
% 7.62/1.50      | ~ v1_relat_1(sK12)
% 7.62/1.50      | ~ v1_funct_1(sK12)
% 7.62/1.50      | v1_xboole_0(X0)
% 7.62/1.50      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.50      inference(unflattening,[status(thm)],[c_867]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_882,plain,
% 7.62/1.50      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.50      | r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12))
% 7.62/1.50      | ~ v1_funct_1(sK12)
% 7.62/1.50      | v1_xboole_0(X0)
% 7.62/1.50      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.50      inference(forward_subsumption_resolution,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_868,c_16]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_5466,plain,
% 7.62/1.50      ( r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12))
% 7.62/1.50      | v1_xboole_0(X0)
% 7.62/1.50      | ~ sP0_iProver_split ),
% 7.62/1.50      inference(splitting,
% 7.62/1.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 7.62/1.50                [c_882]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_6463,plain,
% 7.62/1.50      ( r2_hidden(sK9(k1_relat_1(sK12),X0,sK12),k1_relat_1(sK12)) = iProver_top
% 7.62/1.50      | v1_xboole_0(X0) = iProver_top
% 7.62/1.50      | sP0_iProver_split != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_5466]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_10902,plain,
% 7.62/1.50      ( r2_hidden(sK9(sK10,X0,sK12),sK10) = iProver_top
% 7.62/1.50      | v1_xboole_0(X0) = iProver_top
% 7.62/1.50      | sP0_iProver_split != iProver_top ),
% 7.62/1.50      inference(demodulation,[status(thm)],[c_10863,c_6463]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_6472,plain,
% 7.62/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.62/1.50      | v1_relat_1(X0) != iProver_top
% 7.62/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_10970,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,k2_relat_1(sK12)))) = iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_10863,c_6472]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_11802,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,k2_relat_1(sK12)))) = iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_10970,c_10435,c_10667]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_11811,plain,
% 7.62/1.50      ( r2_hidden(X0,k1_relat_1(sK12)) != iProver_top
% 7.62/1.50      | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_11802,c_6468]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_11815,plain,
% 7.62/1.50      ( r2_hidden(X0,sK10) != iProver_top
% 7.62/1.50      | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_11811,c_10863]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_11932,plain,
% 7.62/1.50      ( r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top
% 7.62/1.50      | r2_hidden(X0,sK10) != iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_11815,c_10667]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_11933,plain,
% 7.62/1.50      ( r2_hidden(X0,sK10) != iProver_top
% 7.62/1.50      | r2_hidden(k1_funct_1(sK12,X0),k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(renaming,[status(thm)],[c_11932]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_11942,plain,
% 7.62/1.50      ( r2_hidden(sK9(sK10,k2_relat_1(sK12),sK12),sK10) != iProver_top
% 7.62/1.50      | sP1_iProver_split != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_11933,c_10906]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_12876,plain,
% 7.62/1.50      ( v1_xboole_0(k2_relat_1(sK12)) = iProver_top
% 7.62/1.50      | sP1_iProver_split != iProver_top
% 7.62/1.50      | sP0_iProver_split != iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_10902,c_11942]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_5467,plain,
% 7.62/1.50      ( ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
% 7.62/1.50      | ~ v1_funct_1(sK12)
% 7.62/1.50      | sP0_iProver_split
% 7.62/1.50      | k1_relat_1(sK12) != sK10 ),
% 7.62/1.50      inference(splitting,
% 7.62/1.50                [splitting(split),new_symbols(definition,[])],
% 7.62/1.50                [c_882]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_6462,plain,
% 7.62/1.50      ( k1_relat_1(sK12) != sK10
% 7.62/1.50      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_5467]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_10905,plain,
% 7.62/1.50      ( sK10 != sK10
% 7.62/1.50      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(demodulation,[status(thm)],[c_10863,c_6462]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_10927,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(equality_resolution_simp,[status(thm)],[c_10905]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_5508,plain,
% 7.62/1.50      ( k1_relat_1(sK12) != sK10
% 7.62/1.50      | m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | v1_funct_1(sK12) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_5467]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_13183,plain,
% 7.62/1.50      ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_10927,c_5508,c_10667,c_10863]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14684,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_6491,c_13183]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14689,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(sK10,sK10) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_14684,c_10863]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15548,plain,
% 7.62/1.50      ( r1_tarski(sK10,sK10) != iProver_top
% 7.62/1.50      | r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_14689,c_10435]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15549,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(sK10,sK10) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(renaming,[status(thm)],[c_15548]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15555,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | sP0_iProver_split = iProver_top ),
% 7.62/1.50      inference(forward_subsumption_resolution,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_15549,c_6497]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14683,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(k1_relat_1(sK12),sK10) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | sP1_iProver_split = iProver_top ),
% 7.62/1.50      inference(superposition,[status(thm)],[c_6491,c_13908]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_14698,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(sK10,sK10) != iProver_top
% 7.62/1.50      | v1_relat_1(sK12) != iProver_top
% 7.62/1.50      | sP1_iProver_split = iProver_top ),
% 7.62/1.50      inference(light_normalisation,[status(thm)],[c_14683,c_10863]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15588,plain,
% 7.62/1.50      ( r1_tarski(sK10,sK10) != iProver_top
% 7.62/1.50      | r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | sP1_iProver_split = iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_14698,c_10435]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15589,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | r1_tarski(sK10,sK10) != iProver_top
% 7.62/1.50      | sP1_iProver_split = iProver_top ),
% 7.62/1.50      inference(renaming,[status(thm)],[c_15588]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15595,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | sP1_iProver_split = iProver_top ),
% 7.62/1.50      inference(forward_subsumption_resolution,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_15589,c_6497]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_15625,plain,
% 7.62/1.50      ( r1_tarski(k2_relat_1(sK12),sK11) != iProver_top
% 7.62/1.50      | v1_xboole_0(k2_relat_1(sK12)) = iProver_top ),
% 7.62/1.50      inference(global_propositional_subsumption,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_14707,c_12876,c_15555,c_15595]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(c_53,plain,
% 7.62/1.50      ( r2_hidden(sK12,k1_funct_2(sK10,sK11)) = iProver_top ),
% 7.62/1.50      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 7.62/1.50  
% 7.62/1.50  cnf(contradiction,plain,
% 7.62/1.50      ( $false ),
% 7.62/1.50      inference(minisat,
% 7.62/1.50                [status(thm)],
% 7.62/1.50                [c_30897,c_16921,c_15754,c_15625,c_53]) ).
% 7.62/1.50  
% 7.62/1.50  
% 7.62/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.50  
% 7.62/1.50  ------                               Statistics
% 7.62/1.50  
% 7.62/1.50  ------ General
% 7.62/1.50  
% 7.62/1.50  abstr_ref_over_cycles:                  0
% 7.62/1.50  abstr_ref_under_cycles:                 0
% 7.62/1.50  gc_basic_clause_elim:                   0
% 7.62/1.50  forced_gc_time:                         0
% 7.62/1.50  parsing_time:                           0.011
% 7.62/1.50  unif_index_cands_time:                  0.
% 7.62/1.50  unif_index_add_time:                    0.
% 7.62/1.50  orderings_time:                         0.
% 7.62/1.50  out_proof_time:                         0.019
% 7.62/1.50  total_time:                             0.9
% 7.62/1.50  num_of_symbols:                         63
% 7.62/1.50  num_of_terms:                           24603
% 7.62/1.50  
% 7.62/1.50  ------ Preprocessing
% 7.62/1.50  
% 7.62/1.50  num_of_splits:                          2
% 7.62/1.50  num_of_split_atoms:                     2
% 7.62/1.50  num_of_reused_defs:                     0
% 7.62/1.50  num_eq_ax_congr_red:                    67
% 7.62/1.50  num_of_sem_filtered_clauses:            1
% 7.62/1.50  num_of_subtypes:                        0
% 7.62/1.50  monotx_restored_types:                  0
% 7.62/1.50  sat_num_of_epr_types:                   0
% 7.62/1.50  sat_num_of_non_cyclic_types:            0
% 7.62/1.50  sat_guarded_non_collapsed_types:        0
% 7.62/1.50  num_pure_diseq_elim:                    0
% 7.62/1.50  simp_replaced_by:                       0
% 7.62/1.50  res_preprocessed:                       223
% 7.62/1.50  prep_upred:                             0
% 7.62/1.50  prep_unflattend:                        180
% 7.62/1.50  smt_new_axioms:                         0
% 7.62/1.50  pred_elim_cands:                        7
% 7.62/1.50  pred_elim:                              3
% 7.62/1.50  pred_elim_cl:                           2
% 7.62/1.50  pred_elim_cycles:                       10
% 7.62/1.50  merged_defs:                            8
% 7.62/1.50  merged_defs_ncl:                        0
% 7.62/1.50  bin_hyper_res:                          8
% 7.62/1.50  prep_cycles:                            4
% 7.62/1.50  pred_elim_time:                         0.1
% 7.62/1.50  splitting_time:                         0.
% 7.62/1.50  sem_filter_time:                        0.
% 7.62/1.50  monotx_time:                            0.
% 7.62/1.50  subtype_inf_time:                       0.
% 7.62/1.50  
% 7.62/1.50  ------ Problem properties
% 7.62/1.50  
% 7.62/1.50  clauses:                                47
% 7.62/1.50  conjectures:                            1
% 7.62/1.50  epr:                                    5
% 7.62/1.50  horn:                                   37
% 7.62/1.50  ground:                                 7
% 7.62/1.50  unary:                                  7
% 7.62/1.50  binary:                                 9
% 7.62/1.50  lits:                                   132
% 7.62/1.50  lits_eq:                                19
% 7.62/1.50  fd_pure:                                0
% 7.62/1.50  fd_pseudo:                              0
% 7.62/1.50  fd_cond:                                1
% 7.62/1.50  fd_pseudo_cond:                         2
% 7.62/1.50  ac_symbols:                             0
% 7.62/1.50  
% 7.62/1.50  ------ Propositional Solver
% 7.62/1.50  
% 7.62/1.50  prop_solver_calls:                      28
% 7.62/1.50  prop_fast_solver_calls:                 3092
% 7.62/1.50  smt_solver_calls:                       0
% 7.62/1.50  smt_fast_solver_calls:                  0
% 7.62/1.50  prop_num_of_clauses:                    9670
% 7.62/1.50  prop_preprocess_simplified:             17748
% 7.62/1.50  prop_fo_subsumed:                       87
% 7.62/1.50  prop_solver_time:                       0.
% 7.62/1.50  smt_solver_time:                        0.
% 7.62/1.50  smt_fast_solver_time:                   0.
% 7.62/1.50  prop_fast_solver_time:                  0.
% 7.62/1.50  prop_unsat_core_time:                   0.
% 7.62/1.50  
% 7.62/1.50  ------ QBF
% 7.62/1.50  
% 7.62/1.50  qbf_q_res:                              0
% 7.62/1.50  qbf_num_tautologies:                    0
% 7.62/1.50  qbf_prep_cycles:                        0
% 7.62/1.50  
% 7.62/1.50  ------ BMC1
% 7.62/1.50  
% 7.62/1.50  bmc1_current_bound:                     -1
% 7.62/1.50  bmc1_last_solved_bound:                 -1
% 7.62/1.50  bmc1_unsat_core_size:                   -1
% 7.62/1.50  bmc1_unsat_core_parents_size:           -1
% 7.62/1.50  bmc1_merge_next_fun:                    0
% 7.62/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.62/1.50  
% 7.62/1.50  ------ Instantiation
% 7.62/1.50  
% 7.62/1.50  inst_num_of_clauses:                    1870
% 7.62/1.50  inst_num_in_passive:                    246
% 7.62/1.50  inst_num_in_active:                     856
% 7.62/1.50  inst_num_in_unprocessed:                770
% 7.62/1.50  inst_num_of_loops:                      1040
% 7.62/1.50  inst_num_of_learning_restarts:          0
% 7.62/1.50  inst_num_moves_active_passive:          179
% 7.62/1.50  inst_lit_activity:                      0
% 7.62/1.50  inst_lit_activity_moves:                0
% 7.62/1.50  inst_num_tautologies:                   0
% 7.62/1.50  inst_num_prop_implied:                  0
% 7.62/1.50  inst_num_existing_simplified:           0
% 7.62/1.50  inst_num_eq_res_simplified:             0
% 7.62/1.50  inst_num_child_elim:                    0
% 7.62/1.50  inst_num_of_dismatching_blockings:      932
% 7.62/1.50  inst_num_of_non_proper_insts:           1934
% 7.62/1.50  inst_num_of_duplicates:                 0
% 7.62/1.50  inst_inst_num_from_inst_to_res:         0
% 7.62/1.50  inst_dismatching_checking_time:         0.
% 7.62/1.50  
% 7.62/1.50  ------ Resolution
% 7.62/1.50  
% 7.62/1.50  res_num_of_clauses:                     0
% 7.62/1.50  res_num_in_passive:                     0
% 7.62/1.50  res_num_in_active:                      0
% 7.62/1.50  res_num_of_loops:                       227
% 7.62/1.50  res_forward_subset_subsumed:            97
% 7.62/1.50  res_backward_subset_subsumed:           8
% 7.62/1.50  res_forward_subsumed:                   0
% 7.62/1.50  res_backward_subsumed:                  1
% 7.62/1.50  res_forward_subsumption_resolution:     9
% 7.62/1.50  res_backward_subsumption_resolution:    0
% 7.62/1.50  res_clause_to_clause_subsumption:       3706
% 7.62/1.50  res_orphan_elimination:                 0
% 7.62/1.50  res_tautology_del:                      123
% 7.62/1.50  res_num_eq_res_simplified:              0
% 7.62/1.50  res_num_sel_changes:                    0
% 7.62/1.50  res_moves_from_active_to_pass:          0
% 7.62/1.50  
% 7.62/1.50  ------ Superposition
% 7.62/1.50  
% 7.62/1.50  sup_time_total:                         0.
% 7.62/1.50  sup_time_generating:                    0.
% 7.62/1.50  sup_time_sim_full:                      0.
% 7.62/1.50  sup_time_sim_immed:                     0.
% 7.62/1.50  
% 7.62/1.50  sup_num_of_clauses:                     955
% 7.62/1.50  sup_num_in_active:                      189
% 7.62/1.50  sup_num_in_passive:                     766
% 7.62/1.50  sup_num_of_loops:                       206
% 7.62/1.50  sup_fw_superposition:                   706
% 7.62/1.50  sup_bw_superposition:                   600
% 7.62/1.50  sup_immediate_simplified:               252
% 7.62/1.50  sup_given_eliminated:                   5
% 7.62/1.50  comparisons_done:                       0
% 7.62/1.50  comparisons_avoided:                    0
% 7.62/1.50  
% 7.62/1.50  ------ Simplifications
% 7.62/1.50  
% 7.62/1.50  
% 7.62/1.50  sim_fw_subset_subsumed:                 74
% 7.62/1.50  sim_bw_subset_subsumed:                 28
% 7.62/1.50  sim_fw_subsumed:                        125
% 7.62/1.50  sim_bw_subsumed:                        40
% 7.62/1.50  sim_fw_subsumption_res:                 10
% 7.62/1.50  sim_bw_subsumption_res:                 0
% 7.62/1.50  sim_tautology_del:                      19
% 7.62/1.50  sim_eq_tautology_del:                   9
% 7.62/1.50  sim_eq_res_simp:                        5
% 7.62/1.50  sim_fw_demodulated:                     6
% 7.62/1.50  sim_bw_demodulated:                     9
% 7.62/1.50  sim_light_normalised:                   46
% 7.62/1.50  sim_joinable_taut:                      0
% 7.62/1.50  sim_joinable_simp:                      0
% 7.62/1.50  sim_ac_normalised:                      0
% 7.62/1.50  sim_smt_subsumption:                    0
% 7.62/1.50  
%------------------------------------------------------------------------------
